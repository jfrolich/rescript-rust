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
) -> Result<Vec<current::StructureItem>, crate::binary_ast::ppx::PpxError> {
    let mut mapper = Mapper::new(arena);
    let result = mapper.map_structure(str);
    mapper.finish(result)
}

/// Convert a signature from parsetree0 to current parsetree
pub fn map_signature(
    arena: &mut ParseArena,
    sig: &[pt0::SignatureItem],
) -> Result<Vec<current::SignatureItem>, crate::binary_ast::ppx::PpxError> {
    let mut mapper = Mapper::new(arena);
    let result = mapper.map_signature(sig);
    mapper.finish(result)
}

// ========== Helper functions ==========

fn map_closed_flag(flag: &pt0::ClosedFlag) -> current::ClosedFlag {
    match flag {
        pt0::ClosedFlag::Closed => current::ClosedFlag::Closed,
        pt0::ClosedFlag::Open => current::ClosedFlag::Open,
    }
}

// ========== Attribute helpers ==========

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

/// `Ast_mapper_from0.remove_constructor_args_attr`: drop the first
/// `_res.constructor_args` marker with an empty structure payload.
fn remove_constructor_args_attr(arena: &ParseArena, attrs: Attributes) -> (bool, Attributes) {
    let mut v: Vec<current::Attribute> = attrs.iter().cloned().collect();
    let found = v.iter().position(|(name, payload)| {
        arena.get_string(name.txt) == "_res.constructor_args"
            && matches!(payload, current::Payload::PStr(items) if items.is_empty())
    });
    match found {
        Some(i) => {
            v.remove(i);
            (true, Attributes::from_vec(v))
        }
        None => (false, attrs),
    }
}

/// `Ast_mapper_from0.has_explicit_arity_attr`.
fn has_explicit_arity_attr(arena: &ParseArena, attrs: &Attributes) -> bool {
    attrs.iter().any(|(name, _)| {
        let name = arena.get_string(name.txt);
        name == "ocaml.explicit_arity" || name == "explicit_arity"
    })
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

fn has_template_attr0(attrs: &[pt0::Attribute]) -> bool {
    attrs.iter().any(|(name, _)| name.txt == "res.template")
}

/// ast_mapper_from0.ml `template_source_from0`: `js`/`*j` strings are source
/// text; anything else is a semantic value given canonical template spelling.
fn template_source_from0(text: &str, delimiter: Option<&str>) -> String {
    match delimiter {
        Some("js" | "*j") => text.to_string(),
        _ => crate::string_literal::template_from_semantic(text)
            .source()
            .to_string(),
    }
}

/// Split v0 attributes at the first internal marker attribute: the
/// attributes before it and after it, or `None` without a marker.
fn split_at_marker<'x>(
    attrs: &'x [pt0::Attribute],
    marker: &str,
) -> Option<(&'x [pt0::Attribute], &'x [pt0::Attribute])> {
    let at = attrs.iter().position(|(name, _)| name.txt == marker)?;
    Some((&attrs[..at], &attrs[at + 1..]))
}

/// The `[@res.arity N]` of a `Function$` node.
fn arity_of_attributes(attrs: &[pt0::Attribute]) -> Option<usize> {
    attrs.iter().find_map(|(name, payload)| {
        if name.txt != "res.arity" {
            return None;
        }
        match payload {
            pt0::Payload::PStr(items) => match items.first().map(|item| &item.pstr_desc) {
                Some(pt0::StructureItemDesc::Eval(
                    pt0::Expression {
                        pexp_desc: pt0::ExpressionDesc::Constant(pt0::Constant::Integer(n, _)),
                        ..
                    },
                    _,
                )) => n.parse().ok(),
                _ => None,
            },
            _ => None,
        }
    })
}

/// The arity `N` of `function$<_, [#Has_arityN]>`.
fn has_arity_of_type(_fun_t: &current::CoreType, t_arity: &current::CoreType) -> Option<usize> {
    let current::CoreTypeDesc::Ptyp_variant(variant) = &*t_arity.ptyp_desc else {
        return None;
    };
    match variant.0.as_slice() {
        [current::RowField::Rtag(tag, _, _, _)] => tag.txt.strip_prefix("Has_arity")?.parse().ok(),
        _ => None,
    }
}

/// `Ast_helper0.Typ.varify_constructors`: `None` where it raises.
fn varify_constructors(
    arena: &ParseArena,
    names: &[&str],
    t: &pt0::CoreType,
) -> Option<pt0::CoreType> {
    let desc = match &t.ptyp_desc {
        pt0::CoreTypeDesc::Any => pt0::CoreTypeDesc::Any,
        pt0::CoreTypeDesc::Var(x) => {
            if names.contains(&x.as_str()) {
                return None;
            }
            pt0::CoreTypeDesc::Var(x.clone())
        }
        pt0::CoreTypeDesc::Arrow(label, a, b) => pt0::CoreTypeDesc::Arrow(
            *label,
            Box::new(varify_constructors(arena, names, a)?),
            Box::new(varify_constructors(arena, names, b)?),
        ),
        pt0::CoreTypeDesc::Tuple(l) => pt0::CoreTypeDesc::Tuple(
            l.iter()
                .map(|t| varify_constructors(arena, names, t))
                .collect::<Option<_>>()?,
        ),
        pt0::CoreTypeDesc::Constr(lid, args)
            if args.is_empty()
                && matches!(&lid.txt, Longident::Lident(s) if names.contains(&arena.get_string(*s))) =>
        {
            let Longident::Lident(s) = &lid.txt else {
                unreachable!()
            };
            pt0::CoreTypeDesc::Var(arena.get_string(*s).to_string())
        }
        pt0::CoreTypeDesc::Constr(lid, args) => pt0::CoreTypeDesc::Constr(
            lid.clone(),
            args.iter()
                .map(|t| varify_constructors(arena, names, t))
                .collect::<Option<_>>()?,
        ),
        pt0::CoreTypeDesc::Object(fields, flag) => pt0::CoreTypeDesc::Object(
            fields
                .iter()
                .map(|f| {
                    Some(match f {
                        pt0::ObjectField::Otag(l, a, t) => pt0::ObjectField::Otag(
                            l.clone(),
                            a.clone(),
                            varify_constructors(arena, names, t)?,
                        ),
                        pt0::ObjectField::Oinherit(t) => {
                            pt0::ObjectField::Oinherit(varify_constructors(arena, names, t)?)
                        }
                    })
                })
                .collect::<Option<_>>()?,
            *flag,
        ),
        pt0::CoreTypeDesc::Class => return None,
        pt0::CoreTypeDesc::Alias(t, s) => {
            if names.contains(&s.as_str()) {
                return None;
            }
            pt0::CoreTypeDesc::Alias(Box::new(varify_constructors(arena, names, t)?), s.clone())
        }
        pt0::CoreTypeDesc::Variant(rows, flag, labels) => pt0::CoreTypeDesc::Variant(
            rows.iter()
                .map(|r| {
                    Some(match r {
                        pt0::RowField::Rtag(l, a, b, ts) => pt0::RowField::Rtag(
                            l.clone(),
                            a.clone(),
                            *b,
                            ts.iter()
                                .map(|t| varify_constructors(arena, names, t))
                                .collect::<Option<_>>()?,
                        ),
                        pt0::RowField::Rinherit(t) => {
                            pt0::RowField::Rinherit(varify_constructors(arena, names, t)?)
                        }
                    })
                })
                .collect::<Option<_>>()?,
            *flag,
            labels.clone(),
        ),
        pt0::CoreTypeDesc::Poly(vars, t) => {
            if vars.iter().any(|v| names.contains(&v.txt.as_str())) {
                return None;
            }
            pt0::CoreTypeDesc::Poly(
                vars.clone(),
                Box::new(varify_constructors(arena, names, t)?),
            )
        }
        pt0::CoreTypeDesc::Package((lid, l)) => pt0::CoreTypeDesc::Package((
            lid.clone(),
            l.iter()
                .map(|(n, t)| Some((n.clone(), varify_constructors(arena, names, t)?)))
                .collect::<Option<_>>()?,
        )),
        pt0::CoreTypeDesc::Extension(ext) => pt0::CoreTypeDesc::Extension(ext.clone()),
    };
    Some(pt0::CoreType {
        ptyp_desc: desc,
        ptyp_loc: t.ptyp_loc,
        ptyp_attributes: t.ptyp_attributes.clone(),
    })
}

/// Mapper from parsetree0 to current parsetree.
/// Holds a mutable reference to the arena for creating LocIdx values.
pub struct Mapper<'a> {
    arena: &'a mut ParseArena,
    /// The first `Location.raise_errorf` the OCaml mapper would raise.
    error: Option<crate::binary_ast::ppx::PpxError>,
}

impl<'a> Mapper<'a> {
    pub fn new(arena: &'a mut ParseArena) -> Self {
        Self { arena, error: None }
    }

    fn finish<T>(&mut self, result: T) -> Result<T, crate::binary_ast::ppx::PpxError> {
        match self.error.take() {
            Some(error) => Err(error),
            None => Ok(result),
        }
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

    /// Record the first `Location.raise_errorf` of the OCaml mapper.
    fn raise(&mut self, loc: LocIdx, message: &str) {
        if self.error.is_none() {
            self.error = Some(crate::binary_ast::ppx::PpxError::at_loc(loc, message));
        }
    }

    /// `remove_template_attr` on mapped attributes.
    fn remove_template_attr(&self, attrs: Attributes) -> Attributes {
        let kept: Vec<current::Attribute> = attrs
            .iter()
            .filter(|(name, _)| self.arena.get_string(name.txt) != "res.template")
            .cloned()
            .collect();
        kept.into()
    }

    /// ast_mapper_from0.ml `map_constant ~loc`.
    fn map_constant(&mut self, c: &pt0::Constant, loc: LocIdx) -> current::Constant {
        match c {
            pt0::Constant::Integer(s, suffix) => {
                current::Constant::Integer(Cow::Owned(s.clone()), *suffix)
            }
            // Ast0 stores only the code point; reconstruct a canonical spelling.
            pt0::Constant::Char(semantic) => current::Constant::char(*semantic),
            pt0::Constant::String(s, Some(delim)) if delim == "js" || delim == "*j" => {
                match crate::string_literal::string_from_source(s) {
                    Some(payload) => current::Constant::String(payload),
                    None => {
                        self.raise(loc, "Invalid string escape sequence");
                        current::Constant::string("")
                    }
                }
            }
            pt0::Constant::String(s, None) => current::Constant::string(s),
            pt0::Constant::String(s, Some(delim)) if delim == "json" => {
                current::Constant::Json(Cow::Owned(s.clone()))
            }
            // Other v0 quotation delimiters are syntax, not part of the value.
            pt0::Constant::String(semantic, Some(_)) => current::Constant::string(semantic),
            pt0::Constant::Float(s, suffix) => {
                current::Constant::Float(Cow::Owned(s.clone()), *suffix)
            }
        }
    }

    /// ast_mapper_from0.ml `map_pattern_constant ~loc`.
    fn map_pattern_constant(&mut self, c: &pt0::Constant, loc: LocIdx) -> current::Constant {
        if let pt0::Constant::String(_, Some(tag)) = c
            && tag != "js"
            && tag != "*j"
        {
            self.raise(
                loc,
                "Tagged template literals are not supported in patterns",
            );
        }
        self.map_constant(c, loc)
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

    /// `Ast_mapper_from0.decode_args` for patterns: a v0 tuple without
    /// attributes splits into the argument list when `split_tuple` holds.
    fn decode_pat_args(&mut self, arg: Option<&pt0::Pattern>, split_tuple: bool) -> Vec<PatIdx> {
        match arg {
            None => Vec::new(),
            Some(pt0::Pattern {
                ppat_desc: pt0::PatternDesc::Tuple(args),
                ppat_attributes,
                ..
            }) if split_tuple && ppat_attributes.is_empty() => {
                args.iter().map(|p| self.push_pat(p)).collect()
            }
            Some(arg) => vec![self.push_pat(arg)],
        }
    }

    /// `Ast_mapper_from0.decode_args` for expressions.
    fn decode_expr_args(
        &mut self,
        arg: Option<&pt0::Expression>,
        split_tuple: bool,
    ) -> Vec<ExprIdx> {
        match arg {
            None => Vec::new(),
            Some(pt0::Expression {
                pexp_desc: pt0::ExpressionDesc::Tuple(args),
                pexp_attributes,
                ..
            }) if split_tuple && pexp_attributes.is_empty() => {
                args.iter().map(|e| self.push_expr(e)).collect()
            }
            Some(arg) => vec![self.push_expr(arg)],
        }
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
            pt0::ArgLabel::Labelled(s) => current::ArgLabel::Labelled(Located::mknoloc(*s)),
            pt0::ArgLabel::Optional(s) => current::ArgLabel::Optional(Located::mknoloc(*s)),
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
        if ext.0.txt == "re" {
            let loc = self.loc(&ext.0.loc);
            self.raise(
                loc,
                "A PPX returned a regexp extension outside an expression.",
            );
        }
        // ast_mapper_from0.ml `extension`: `%raw`/`%ffi` string payloads keep
        // their source spelling as `Pconst_raw_source`.
        let payload = if matches!(ext.0.txt.as_str(), "raw" | "ffi") {
            match self.map_raw_source_payload(&ext.1) {
                Some(payload) => payload,
                None => self.map_payload(&ext.1),
            }
        } else {
            self.map_payload(&ext.1)
        };
        (self.map_string_loc(&ext.0), payload)
    }

    /// ast_mapper_from0.ml `map_raw_source_payload`.
    fn map_raw_source_payload(&mut self, payload: &pt0::Payload) -> Option<current::Payload> {
        let pt0::Payload::PStr(items) = payload else {
            return None;
        };
        let [item] = items.as_slice() else {
            return None;
        };
        let pt0::StructureItemDesc::Eval(expr, eval_attrs) = &item.pstr_desc else {
            return None;
        };
        let pt0::ExpressionDesc::Constant(pt0::Constant::String(source, _)) = &expr.pexp_desc
        else {
            return None;
        };
        let expr_loc = self.loc(&expr.pexp_loc);
        let expr_attrs = self.map_attributes(&expr.pexp_attributes);
        let expression = self.arena.push_expr(current::Expression {
            pexp_desc: Box::new(current::ExpressionDesc::Pexp_constant(Box::new(
                current::Constant::RawSource(Cow::Owned(source.clone())),
            ))),
            pexp_loc: expr_loc,
            pexp_attributes: expr_attrs,
        });
        let eval_attrs = self.map_attributes(eval_attrs);
        let item_loc = self.loc(&item.pstr_loc);
        Some(current::Payload::PStr(Box::new(vec![
            current::StructureItem {
                pstr_desc: Box::new(current::StructureItemDesc::Pstr_eval(Box::new((
                    expression, eval_attrs,
                )))),
                pstr_loc: item_loc,
            },
        ])))
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
                // ast_mapper_from0.ml T.map Ptyp_arrow: a one-parameter arrow;
                // attributes before the internal `_res.arrow_node_attrs`
                // marker are node attributes, the rest (or all of them,
                // without a marker) argument attributes.
                let (node_attrs, arg_attrs) =
                    match split_at_marker(&typ.ptyp_attributes, "_res.arrow_node_attrs") {
                        Some((node, arg)) => (self.map_attributes(node), self.map_attributes(arg)),
                        None => (Attributes::new(), attrs),
                    };
                let lbl = self.map_arg_label(lbl);
                let ret_idx = self.push_core_type(t2);
                let typ_idx = self.push_core_type(t1);
                let arg = current::TypeArg {
                    attrs: arg_attrs,
                    lbl,
                    typ: typ_idx,
                };
                return self.mk_arrow(vec![arg], ret_idx, loc, node_attrs);
            }
            pt0::CoreTypeDesc::Tuple(tl) => current::CoreTypeDesc::Ptyp_tuple(Box::new(
                tl.iter().map(|t| self.push_core_type(t)).collect(),
            )),
            pt0::CoreTypeDesc::Constr(lid, tl) => {
                // First map to CoreType for inspection (function$ detection), then push to arena
                let mapped_types: Vec<current::CoreType> =
                    tl.iter().map(|t| self.map_core_type(t)).collect();

                // ast_mapper_from0.ml T.map Ptyp_constr function$: gather
                // [arity] parameters from the chain of unary arrows into one
                // n-ary arrow.
                if self.is_lident(&lid.txt, "function$")
                    && let [fun_t, t_arity] = &mapped_types[..]
                    && matches!(&*fun_t.ptyp_desc, current::CoreTypeDesc::Ptyp_arrow(_))
                    && let Some(arity) = has_arity_of_type(fun_t, t_arity)
                {
                    let (params, ret) = self.gather_arrow(fun_t, arity);
                    if let Some(ret) = ret {
                        return self.mk_arrow(
                            params,
                            ret,
                            fun_t.ptyp_loc,
                            fun_t.ptyp_attributes.clone(),
                        );
                    }
                    return fun_t.clone();
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
            ptyp_attributes: attrs,
        }
    }

    fn map_row_field(&mut self, rf: &pt0::RowField) -> current::RowField {
        match rf {
            pt0::RowField::Rtag(label, attrs, empty, types) => {
                let label = self.map_label_loc(label);
                let attrs = self.map_attributes(attrs);
                // ast_mapper_from0.ml T.row_field `map_group`: a marked tuple
                // with no other attributes is a multi-argument group; a PPX
                // annotated tuple keeps its wrapper.
                let groups = types
                    .iter()
                    .map(|t| {
                        let mut typ = self.map_core_type(t);
                        let (has_constructor_args, rest) = remove_constructor_args_attr(
                            self.arena,
                            std::mem::take(&mut typ.ptyp_attributes),
                        );
                        let loc = typ.ptyp_loc;
                        let txt = match &*typ.ptyp_desc {
                            current::CoreTypeDesc::Ptyp_tuple(args)
                                if has_constructor_args && rest.is_empty() =>
                            {
                                args.to_vec()
                            }
                            _ => {
                                typ.ptyp_attributes = rest;
                                vec![self.arena.push_core_type(typ)]
                            }
                        };
                        Located::new(txt, loc)
                    })
                    .collect();
                current::RowField::Rtag(label, attrs, *empty, groups)
            }
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
        let mut attrs: Vec<pt0::Attribute> = pat
            .ppat_attributes
            .iter()
            .filter(|(name, _)| name.txt != "_res.record_rest")
            .cloned()
            .collect();
        // ast_mapper_from0.ml `extract_variant_spread_attr`: the
        // `res.patVariantSpread` marker that `Ast_mapper_to0` puts on a
        // variant spread pattern, with any payload.
        let variant_spread = matches!(pat.ppat_desc, pt0::PatternDesc::Type(_))
            && match attrs
                .iter()
                .position(|(name, _)| name.txt == "res.patVariantSpread")
            {
                Some(at) => {
                    attrs.remove(at);
                    true
                }
                None => false,
            };
        let mut attrs = self.map_attributes(&attrs);
        // ast_mapper_from0.ml Ppat_constant drops the template marker.
        if matches!(pat.ppat_desc, pt0::PatternDesc::Constant(_))
            && has_template_attr0(&pat.ppat_attributes)
        {
            attrs = self.remove_template_attr(attrs);
        }

        let desc = match &pat.ppat_desc {
            pt0::PatternDesc::Any => current::PatternDesc::Ppat_any,
            pt0::PatternDesc::Var(s) => current::PatternDesc::Ppat_var(self.map_string_loc(s)),
            pt0::PatternDesc::Alias(p, s) => {
                current::PatternDesc::Ppat_alias(self.push_pat(p), self.map_string_loc(s))
            }
            pt0::PatternDesc::Constant(c) => {
                current::PatternDesc::Ppat_constant(Box::new(self.map_pattern_constant(c, loc)))
            }
            pt0::PatternDesc::Interval(c1, c2) => {
                let c1 = self.map_pattern_constant(c1, loc);
                let c2 = self.map_pattern_constant(c2, loc);
                current::PatternDesc::Ppat_interval(Box::new((c1, c2)))
            }
            pt0::PatternDesc::Tuple(pl) => current::PatternDesc::Ppat_tuple(Box::new(
                pl.iter().map(|p| self.push_pat(p)).collect(),
            )),
            pt0::PatternDesc::Construct(lid, arg) => {
                let args_loc = match arg {
                    Some(arg) => self.loc(&arg.ppat_loc),
                    None => loc,
                };
                let (has_constructor_args, rest) =
                    remove_constructor_args_attr(self.arena, std::mem::take(&mut attrs));
                attrs = rest;
                let split_tuple = has_constructor_args
                    || has_explicit_arity_attr(self.arena, &attrs)
                    || self.is_lident(&lid.txt, "::");
                let args = self.decode_pat_args(arg.as_deref(), split_tuple);
                current::PatternDesc::Ppat_construct(
                    self.map_longident_loc(lid),
                    current::ctor_args(args, args_loc),
                )
            }
            pt0::PatternDesc::Variant(tag, arg) => {
                let (has_constructor_args, rest) =
                    remove_constructor_args_attr(self.arena, std::mem::take(&mut attrs));
                attrs = rest;
                let args_loc = match arg {
                    Some(arg) => self.loc(&arg.ppat_loc),
                    None => loc,
                };
                let args = self.decode_pat_args(arg.as_deref(), has_constructor_args);
                current::PatternDesc::Ppat_variant(Box::new((
                    Cow::Owned(tag.clone()),
                    Located::new(args, args_loc),
                )))
            }
            pt0::PatternDesc::Record(fields, closed) => {
                let fields = fields
                    .iter()
                    .map(|(lid, pat)| {
                        let lid = self.map_longident_loc(lid);
                        let mapped_attrs = self.map_attributes(&pat.ppat_attributes);
                        let optional = has_optional_attribute(self.arena, &mapped_attrs);
                        let mapped_pat = if has_optional_attribute(self.arena, &mapped_attrs) {
                            let mut mapped = self.map_pattern(pat);
                            mapped.ppat_attributes =
                                remove_optional_attribute(self.arena, &mapped.ppat_attributes);
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
                // ast_mapper_from0.ml get_record_rest_attr: the rest row comes
                // back from the internal `_res.record_rest` attribute.
                let rest = pat
                    .ppat_attributes
                    .iter()
                    .find_map(|(name, payload)| match payload {
                        pt0::Payload::PPat(rest, None) if name.txt == "_res.record_rest" => {
                            Some(rest.as_ref().clone())
                        }
                        _ => None,
                    });
                let rest = rest.and_then(|rest| self.record_rest_of_pattern(&rest));
                current::PatternDesc::Ppat_record(Box::new((fields, map_closed_flag(closed), rest)))
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
            pt0::PatternDesc::Type(lid) if variant_spread => {
                current::PatternDesc::Ppat_variant_spread(self.map_longident_loc(lid))
            }
            pt0::PatternDesc::Type(lid) => {
                current::PatternDesc::Ppat_type(self.map_longident_loc(lid))
            }
            pt0::PatternDesc::Unpack(name) => {
                current::PatternDesc::Ppat_unpack(self.map_string_loc(name))
            }
            pt0::PatternDesc::Open(_, _) => {
                panic!("Ppat_open is no longer present in ReScript")
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
            ppat_attributes: attrs,
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
                pt0::ExpressionDesc::Construct(lid, ext) if self.is_lident(&lid.txt, "[]") => {
                    match ext {
                        None => break,
                        Some(ext) => current_expr = ext,
                    }
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
                found = Some(name.loc);
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
                let loc = loc.unwrap_or(expr.pexp_loc);
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
                let loc = loc.unwrap_or(expr.pexp_loc);
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
                let loc = loc.unwrap_or(expr.pexp_loc);
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
    /// ast_mapper_from0.ml `extract_props_and_children`: the props, and the
    /// children when the application passes `~children` just before its
    /// last argument.
    fn extract_jsx_props_and_children(
        &mut self,
        args: &[(pt0::ArgLabel, pt0::Expression)],
    ) -> (Vec<current::JsxProp>, Option<Vec<ExprIdx>>) {
        let mut props = Vec::new();
        let mut items = args;
        loop {
            match items {
                [] | [_] => return (props, None),
                [(pt0::ArgLabel::Labelled(name), children), _]
                    if self.get_str(*name) == "children" =>
                {
                    let children = self.map_jsx_children(children);
                    return (props, Some(children));
                }
                [(label, expr), rest @ ..] => {
                    if let Some(prop) = self.try_map_jsx_prop(label, expr) {
                        props.push(prop);
                    }
                    items = rest;
                }
            }
        }
    }

    /// ast_mapper_from0.ml `map_jsx_children`.
    fn map_jsx_children(&mut self, e: &pt0::Expression) -> Vec<ExprIdx> {
        match &e.pexp_desc {
            pt0::ExpressionDesc::Construct(lid, _)
                if self.is_lident(&lid.txt, "[]") || self.is_lident(&lid.txt, "::") =>
            {
                self.extract_jsx_children(e)
            }
            _ => vec![self.push_expr(e)],
        }
    }

    /// `Lexing.dummy_pos`.
    fn dummy_pos(&mut self) -> crate::parse_arena::PosIdx {
        let file_name = self.arena.intern("");
        self.arena.push_position(crate::location::Position {
            file_name,
            line: 0,
            bol: 0,
            cnum: -1,
        })
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

        // ast_mapper_from0.ml E.map: the first `res.braces`/`ns.braces` or
        // `res.await` marker decides which wrapper node the v0 attribute
        // slot encodes.
        let first_wrapper =
            expr.pexp_attributes
                .iter()
                .find_map(|(name, _)| match name.txt.as_str() {
                    "res.braces" | "ns.braces" => Some(true),
                    "res.await" => Some(false),
                    _ => None,
                });
        if first_wrapper == Some(true) {
            let at = expr
                .pexp_attributes
                .iter()
                .position(|(name, _)| name.txt == "res.braces" || name.txt == "ns.braces")
                .expect("found above");
            let outer_attrs = &expr.pexp_attributes[..at];
            let braces_loc = self.loc(&expr.pexp_attributes[at].0.loc);
            let inner_expr = pt0::Expression {
                pexp_desc: expr.pexp_desc.clone(),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes[at + 1..].to_vec(),
            };
            let inner_idx = self.push_expr(&inner_expr);
            let inner_loc = self.arena.get_expr(inner_idx).pexp_loc;
            return current::Expression {
                pexp_desc: Box::new(current::ExpressionDesc::Pexp_braces(Box::new(
                    current::PexpBraces {
                        expr: inner_idx,
                        braces_loc,
                    },
                ))),
                pexp_loc: inner_loc,
                pexp_attributes: self.map_attributes(outer_attrs),
            };
        }

        // ast_mapper_from0.ml E.map `res.await`: await-node attributes before
        // the marker, the inner expression's after it.
        if first_wrapper == Some(false) {
            let (await_attrs, inner_attrs) =
                split_at_marker(&expr.pexp_attributes, "res.await").unwrap_or((&[], &[]));
            let inner_expr = pt0::Expression {
                pexp_desc: expr.pexp_desc.clone(),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: inner_attrs.to_vec(),
            };
            let await_idx = self.push_expr(&inner_expr);
            return current::Expression {
                pexp_desc: Box::new(current::ExpressionDesc::Pexp_await(await_idx)),
                pexp_loc: loc,
                pexp_attributes: self.map_attributes(await_attrs),
            };
        }

        let desc = match &expr.pexp_desc {
            pt0::ExpressionDesc::Ident(lid) => {
                current::ExpressionDesc::Pexp_ident(self.map_longident_loc(lid))
            }
            pt0::ExpressionDesc::Constant(pt0::Constant::String(text, delimiter))
                if has_template_attr0(&expr.pexp_attributes)
                    && delimiter.as_deref() != Some("json") =>
            {
                attrs = self.remove_template_attr(attrs);
                let source = template_source_from0(text, delimiter.as_deref());
                let segment = self.mk_string_loc(&source, &expr.pexp_loc);
                current::ExpressionDesc::Pexp_template(Box::new(current::PexpTemplate {
                    source_segments: vec![segment],
                    values: vec![],
                }))
            }
            pt0::ExpressionDesc::Constant(c) => {
                if has_template_attr0(&expr.pexp_attributes) {
                    attrs = self.remove_template_attr(attrs);
                }
                current::ExpressionDesc::Pexp_constant(Box::new(self.map_constant(c, loc)))
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
            pt0::ExpressionDesc::Fun(lbl, default, pat, body) => {
                // ast_mapper_from0.ml Pexp_fun: a bare v0 fun is a
                // one-parameter function; `res.async` becomes the async flag,
                // and attributes after the internal `_res.fun_node_attrs`
                // marker are parameter attributes.
                let is_async = expr
                    .pexp_attributes
                    .iter()
                    .any(|(name, _)| name.txt == "res.async");
                let fun_attrs: Vec<pt0::Attribute> = expr
                    .pexp_attributes
                    .iter()
                    .filter(|(name, _)| name.txt != "res.async")
                    .cloned()
                    .collect();
                let (node_attrs, param_attrs) =
                    match split_at_marker(&fun_attrs, "_res.fun_node_attrs") {
                        Some((node, param)) => {
                            (self.map_attributes(node), self.map_attributes(param))
                        }
                        None => (self.map_attributes(&fun_attrs), Attributes::new()),
                    };
                let p_lbl = self.map_arg_label(lbl);
                let p_default = default.as_ref().map(|e| self.push_expr(e));
                let p_pat = self.push_pat(pat);
                let body_idx = self.push_expr(body);
                let param = current::FunParam {
                    p_attrs: param_attrs,
                    p_lbl,
                    p_default,
                    p_pat,
                };
                return self.mk_fun(loc, node_attrs, vec![param], body_idx, is_async);
            }
            pt0::ExpressionDesc::Function(cases) => {
                // ast_mapper_from0.ml Pexp_function: desugar
                // `function | p -> e` to `fun x -> match x with | p -> e`.
                let param_name = self.mk_string_loc("*function*", &expr.pexp_loc);
                let p_pat = self.arena.push_pat(current::Pattern {
                    ppat_desc: Box::new(current::PatternDesc::Ppat_var(param_name)),
                    ppat_loc: loc,
                    ppat_attributes: Attributes::new(),
                });
                let param_ident = self.arena.intern("*function*");
                let lid = self.push_longident(Longident::Lident(param_ident));
                let scrutinee = self.arena.push_expr(current::Expression {
                    pexp_desc: Box::new(current::ExpressionDesc::Pexp_ident(Located {
                        txt: lid,
                        loc,
                    })),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                });
                let cases = cases.iter().map(|c| self.map_case(c)).collect();
                let body = self.arena.push_expr(current::Expression {
                    pexp_desc: Box::new(current::ExpressionDesc::Pexp_match(Box::new((
                        scrutinee, cases,
                    )))),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                });
                let param = current::FunParam {
                    p_attrs: Attributes::new(),
                    p_lbl: current::ArgLabel::Nolabel,
                    p_default: None,
                    p_pat,
                };
                return self.mk_fun(loc, attrs, vec![param], body, false);
            }
            // ast_mapper_from0.ml: decode the v0 encoding of property
            // assignment, `#=` applied to a send.
            pt0::ExpressionDesc::Apply(func, args)
                if matches!(&func.pexp_desc, pt0::ExpressionDesc::Ident(lid)
                    if matches!(&lid.txt, Longident::Lident(op) if self.str_eq(*op, "#=")))
                    && matches!(
                        args.as_slice(),
                        [
                            (
                                pt0::ArgLabel::Nolabel,
                                pt0::Expression {
                                    pexp_desc: pt0::ExpressionDesc::Send(..),
                                    ..
                                }
                            ),
                            (pt0::ArgLabel::Nolabel, _)
                        ]
                    ) =>
            {
                let pt0::ExpressionDesc::Send(e, method) = &args[0].1.pexp_desc else {
                    unreachable!()
                };
                let v_idx = self.push_expr(&args[1].1);
                let name = self.map_label_loc(method);
                let e_idx = self.push_expr(e);
                current::ExpressionDesc::Pexp_object_set(Box::new((e_idx, name, v_idx)))
            }
            // ast_mapper_from0.ml: a v0 tagged template is `tag([segments],
            // [values])` marked `res.taggedTemplate`.
            pt0::ExpressionDesc::Apply(func, args)
                if !(has_jsx_attribute(&expr.pexp_attributes)
                    && matches!(func.pexp_desc, pt0::ExpressionDesc::Ident(_)))
                    && expr
                        .pexp_attributes
                        .iter()
                        .any(|(name, _)| name.txt == "res.taggedTemplate")
                    && matches!(
                        args.as_slice(),
                        [
                            (
                                pt0::ArgLabel::Nolabel,
                                pt0::Expression {
                                    pexp_desc: pt0::ExpressionDesc::Array(_),
                                    ..
                                }
                            ),
                            (
                                pt0::ArgLabel::Nolabel,
                                pt0::Expression {
                                    pexp_desc: pt0::ExpressionDesc::Array(_),
                                    ..
                                }
                            )
                        ]
                    ) =>
            {
                let (pt0::ExpressionDesc::Array(segments), pt0::ExpressionDesc::Array(values)) =
                    (&args[0].1.pexp_desc, &args[1].1.pexp_desc)
                else {
                    unreachable!()
                };
                let mut raw_sources = Vec::with_capacity(segments.len());
                for segment in segments {
                    let txt = match &segment.pexp_desc {
                        pt0::ExpressionDesc::Constant(pt0::Constant::String(txt, Some(delim)))
                            if delim == "js" || delim == "*j" =>
                        {
                            txt.clone()
                        }
                        pt0::ExpressionDesc::Constant(pt0::Constant::String(semantic, _)) => {
                            template_source_from0(semantic, None)
                        }
                        _ => unreachable!("a v0 tagged template segment is a string"),
                    };
                    raw_sources.push(self.mk_string_loc(&txt, &segment.pexp_loc));
                }
                let kept: Vec<current::Attribute> = attrs
                    .iter()
                    .filter(|(name, _)| self.arena.get_string(name.txt) != "res.taggedTemplate")
                    .cloned()
                    .collect();
                attrs = kept.into();
                let values = values.iter().map(|value| self.push_expr(value)).collect();
                let tag = self.push_expr(func);
                current::ExpressionDesc::Pexp_tagged_template(Box::new(
                    current::PexpTaggedTemplate {
                        tag,
                        raw_sources,
                        values,
                    },
                ))
            }
            // ast_mapper_from0.ml: a `^` chain marked `res.template`
            // alternating string segments and values becomes a template.
            pt0::ExpressionDesc::Apply(func, _)
                if !(has_jsx_attribute(&expr.pexp_attributes)
                    && matches!(func.pexp_desc, pt0::ExpressionDesc::Ident(_)))
                    && has_template_attr0(&expr.pexp_attributes) =>
            {
                fn flatten<'e>(
                    arena: &ParseArena,
                    acc: &mut Vec<&'e pt0::Expression>,
                    expression: &'e pt0::Expression,
                ) {
                    if let pt0::ExpressionDesc::Apply(op, args) = &expression.pexp_desc
                        && let pt0::ExpressionDesc::Ident(lid) = &op.pexp_desc
                        && matches!(&lid.txt, Longident::Lident(name) if arena.get_string(*name) == "^")
                        && let [(pt0::ArgLabel::Nolabel, lhs), (pt0::ArgLabel::Nolabel, rhs)] =
                            args.as_slice()
                        && has_template_attr0(&expression.pexp_attributes)
                    {
                        flatten(arena, acc, lhs);
                        acc.push(rhs);
                    } else {
                        acc.push(expression);
                    }
                }
                let mut parts = Vec::new();
                flatten(self.arena, &mut parts, expr);
                // `collect`
                let mut sources = Vec::new();
                let mut values = Vec::new();
                let mut collected = None;
                let mut index = 0;
                loop {
                    let Some(part) = parts.get(index) else {
                        break;
                    };
                    let pt0::ExpressionDesc::Constant(pt0::Constant::String(text, delimiter)) =
                        &part.pexp_desc
                    else {
                        break;
                    };
                    if delimiter.as_deref() == Some("json") {
                        self.raise(loc, "`json` literals do not support interpolation");
                        collected = Some(());
                        break;
                    }
                    let txt = template_source_from0(text, delimiter.as_deref());
                    sources.push(self.mk_string_loc(&txt, &part.pexp_loc));
                    if index + 1 == parts.len() {
                        collected = Some(());
                        break;
                    }
                    values.push(parts[index + 1]);
                    index += 2;
                }
                match collected {
                    Some(()) => {
                        attrs = self.remove_template_attr(attrs);
                        let values = values.iter().map(|value| self.push_expr(value)).collect();
                        current::ExpressionDesc::Pexp_template(Box::new(current::PexpTemplate {
                            source_segments: sources,
                            values,
                        }))
                    }
                    None => {
                        // Not a template shape: an ordinary application, with
                        // `^` renamed to `++`.
                        attrs = self.remove_template_attr(attrs);
                        let pt0::ExpressionDesc::Apply(func, args) = &expr.pexp_desc else {
                            unreachable!()
                        };
                        let binary = matches!(
                            args.as_slice(),
                            [(pt0::ArgLabel::Nolabel, _), (pt0::ArgLabel::Nolabel, _)]
                        );
                        let mut func = (**func).clone();
                        if binary
                            && let pt0::ExpressionDesc::Ident(lid) = &mut func.pexp_desc
                            && matches!(&lid.txt, Longident::Lident(name) if self.str_eq(*name, "^"))
                        {
                            lid.txt = Longident::Lident(self.arena.intern("++"));
                        }
                        let funct = self.push_expr(&func);
                        let args = args
                            .iter()
                            .map(|(label, arg)| (self.map_arg_label(label), self.push_expr(arg)))
                            .collect();
                        current::ExpressionDesc::Pexp_apply(Box::new(current::PexpApply {
                            funct,
                            args,
                            partial: false,
                            transformed_jsx: false,
                        }))
                    }
                }
            }
            pt0::ExpressionDesc::Apply(func, args) => {
                // Check for JSX attribute - convert back to JSX element
                if has_jsx_attribute(&expr.pexp_attributes) {
                    if let pt0::ExpressionDesc::Ident(tag_lid) = &func.pexp_desc {
                        let jsx_attrs =
                            self.map_attributes(&remove_jsx_attribute(&expr.pexp_attributes));
                        let (props, children) = self.extract_jsx_props_and_children(args);
                        let tag_name = self.longident_to_jsx_tag(&tag_lid.txt);
                        let tag_loc = Located::new(tag_name, self.loc(&tag_lid.loc));

                        let jsx_element = match children {
                            None => current::JsxElement::Unary(current::JsxUnaryElement {
                                tag_name: tag_loc,
                                props,
                            }),
                            // The v0 encoding has no closing-tag information;
                            // synthesize one matching the opening tag at
                            // `Lexing.dummy_pos`.
                            Some(children) => {
                                let opening_end = self.dummy_pos();
                                let closing_start = self.dummy_pos();
                                let closing_end = self.dummy_pos();
                                current::JsxElement::Container(current::JsxContainerElement {
                                    tag_name_start: tag_loc.clone(),
                                    opening_end,
                                    props,
                                    children,
                                    closing_tag: Some(current::JsxClosingTag {
                                        start: closing_start,
                                        name: tag_loc,
                                        end: closing_end,
                                    }),
                                })
                            }
                        };

                        return current::Expression {
                            pexp_desc: Box::new(current::ExpressionDesc::Pexp_jsx_element(
                                Box::new(jsx_element),
                            )),
                            pexp_loc: loc,
                            pexp_attributes: jsx_attrs,
                        };
                    }
                }

                // Check for partial application attribute (legacy) or use pt0_partial
                let partial = has_partial_attribute(&expr.pexp_attributes);
                let attrs = if has_partial_attribute(&expr.pexp_attributes) {
                    self.map_attributes(&remove_partial_attribute(&expr.pexp_attributes))
                } else {
                    attrs.clone()
                };

                // Map operator names
                // ast_mapper_from0.ml: operators are renamed only when applied
                // to two unlabelled arguments.
                let binary = matches!(
                    args.as_slice(),
                    [(pt0::ArgLabel::Nolabel, _), (pt0::ArgLabel::Nolabel, _)]
                );
                let func = if binary && let pt0::ExpressionDesc::Ident(lid) = &func.pexp_desc {
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
                                        loc: lid.loc,
                                    }),
                                    pexp_loc: func.pexp_loc,
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
                        transformed_jsx: false,
                    }))),
                    pexp_loc: loc,
                    pexp_attributes: attrs,
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
                                pexp_attributes: jsx_attrs,
                            };
                        }
                    }
                }

                // ast_mapper_from0.ml Pexp_construct Function$: gather
                // [res.arity] parameters from the chain of unary functions
                // into one n-ary function; the construct node's other
                // attributes become the function node's attributes.
                if self.is_lident(&lid.txt, "Function$")
                    && let Some(inner) = arg
                    && matches!(inner.pexp_desc, pt0::ExpressionDesc::Fun(..))
                {
                    let arity = arity_of_attributes(&expr.pexp_attributes)
                        .expect("Function$ carries a res.arity attribute");
                    let e1 = self.map_expression(inner);
                    let current::ExpressionDesc::Pexp_fun(f) = &*e1.pexp_desc else {
                        unreachable!("a v0 fun maps to a function");
                    };
                    let is_async = f.is_async;
                    let (params, body) = self.gather_fun(&e1, arity);
                    let Some(body) = body else {
                        return e1;
                    };
                    let node_attrs: Vec<pt0::Attribute> = expr
                        .pexp_attributes
                        .iter()
                        .filter(|(name, _)| name.txt != "res.arity")
                        .cloned()
                        .collect();
                    let mut fun_attrs = e1.pexp_attributes.clone();
                    fun_attrs.extend(self.map_attributes(&node_attrs));
                    return self.mk_fun(e1.pexp_loc, fun_attrs, params, body, is_async);
                }
                let args_loc = match arg {
                    Some(arg) => self.loc(&arg.pexp_loc),
                    None => loc,
                };
                let lid1 = self.map_longident_loc(lid);
                let (has_constructor_args, rest) =
                    remove_constructor_args_attr(self.arena, std::mem::take(&mut attrs));
                attrs = rest;
                let split_tuple = has_constructor_args
                    || has_explicit_arity_attr(self.arena, &attrs)
                    || self.is_lident(&lid.txt, "::");
                let args = self.decode_expr_args(arg.as_deref(), split_tuple);
                current::ExpressionDesc::Pexp_construct(lid1, current::ctor_args(args, args_loc))
            }
            pt0::ExpressionDesc::Variant(label, arg) => {
                let (has_constructor_args, rest) =
                    remove_constructor_args_attr(self.arena, std::mem::take(&mut attrs));
                attrs = rest;
                let args_loc = match arg {
                    Some(arg) => self.loc(&arg.pexp_loc),
                    None => loc,
                };
                let args = self.decode_expr_args(arg.as_deref(), has_constructor_args);
                current::ExpressionDesc::Pexp_variant(Box::new((
                    Cow::Owned(label.clone()),
                    Located::new(args, args_loc),
                )))
            }
            pt0::ExpressionDesc::Record(fields, base) => {
                let fields = fields
                    .iter()
                    .map(|(lid, e)| {
                        let mapped_expr = self.map_expression(e);
                        let optional =
                            has_optional_attribute(self.arena, &mapped_expr.pexp_attributes);
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
            pt0::ExpressionDesc::Ifthenelse(e1, e2, Some(e3))
                if attrs.iter().any(|(name, payload)| {
                    self.arena.get_string(name.txt) == "res.ternary"
                        && matches!(payload, current::Payload::PStr(items) if items.is_empty())
                }) =>
            {
                // ast_mapper_from0.ml `extract_ternary_attr`: drop the first
                // `res.ternary` marker.
                let at = attrs
                    .iter()
                    .position(|(name, payload)| {
                        self.arena.get_string(name.txt) == "res.ternary"
                            && matches!(payload, current::Payload::PStr(items) if items.is_empty())
                    })
                    .expect("checked by the guard");
                attrs.remove(at);
                let e1_idx = self.push_expr(e1);
                let e2_idx = self.push_expr(e2);
                let e3_idx = self.push_expr(e3);
                current::ExpressionDesc::Pexp_ternary(Box::new((e1_idx, e2_idx, e3_idx)))
            }
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
                current::ExpressionDesc::Pexp_object_get(Box::new((
                    e_idx,
                    self.map_label_loc(method),
                )))
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
                return self.map_newtype(expr, name, body, loc);
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
            // ast_mapper_from0.ml: `%res.break` / `%res.continue` with an empty
            // payload are loop control.
            pt0::ExpressionDesc::Extension((name, pt0::Payload::PStr(items)))
                if items.is_empty() && name.txt == "res.break" =>
            {
                current::ExpressionDesc::Pexp_break
            }
            pt0::ExpressionDesc::Extension((name, pt0::Payload::PStr(items)))
                if items.is_empty() && name.txt == "res.continue" =>
            {
                current::ExpressionDesc::Pexp_continue
            }
            // ast_mapper_from0.ml: decode the reserved v0 `%obj` encoding of
            // object literals.
            pt0::ExpressionDesc::Extension((name, pt0::Payload::PStr(items)))
                if name.txt == "obj" && v0_object_literal_rows(items).is_some() =>
            {
                let rows = v0_object_literal_rows(items).expect("checked by the guard");
                let fields = rows
                    .iter()
                    .map(|(lid, e)| {
                        let Longident::Lident(field) = &lid.txt else {
                            unreachable!("checked by the guard")
                        };
                        let field = Located::new(
                            Cow::Owned(self.get_str(*field).to_string()),
                            self.loc(&lid.loc),
                        );
                        (field, self.push_expr(e))
                    })
                    .collect();
                current::ExpressionDesc::Pexp_object_literal(Box::new(fields))
            }
            pt0::ExpressionDesc::Extension((name, payload)) if name.txt == "re" => {
                let regexp = match payload {
                    pt0::Payload::PStr(items) => match items.as_slice() {
                        [
                            pt0::StructureItem {
                                pstr_desc: pt0::StructureItemDesc::Eval(source_expr, eval_attrs),
                                ..
                            },
                        ] => match &source_expr.pexp_desc {
                            pt0::ExpressionDesc::Constant(pt0::Constant::String(source, _)) => {
                                match crate::binary_ast::ppx::parse_js_regexp_literal(source) {
                                    Some(parsed) => {
                                        Ok((parsed, eval_attrs, &source_expr.pexp_attributes))
                                    }
                                    None => Err(self.loc(&source_expr.pexp_loc)),
                                }
                            }
                            _ => Err(loc),
                        },
                        _ => Err(loc),
                    },
                    _ => Err(loc),
                };
                match regexp {
                    Ok(((pattern, flags), eval_attrs, source_attrs)) => {
                        // Payload wrappers disappear at this boundary: the
                        // expression keeps its location and receives both
                        // levels of payload attributes.
                        let eval_attrs = self.map_attributes(eval_attrs);
                        let source_attrs = self.map_attributes(source_attrs);
                        attrs.extend(eval_attrs);
                        attrs.extend(source_attrs);
                        current::ExpressionDesc::Pexp_regexp(Box::new(current::PexpRegexp {
                            pattern,
                            flags,
                        }))
                    }
                    Err(error_loc) => {
                        self.raise(
                            error_loc,
                            "A PPX returned a malformed regexp payload. Expected a string containing one regexp literal.",
                        );
                        current::ExpressionDesc::Pexp_extension(Box::new(
                            self.map_extension(&(name.clone(), payload.clone())),
                        ))
                    }
                }
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
                    current::Payload::PStr(Box::default()),
                )))
            }
        };

        current::Expression {
            pexp_desc: Box::new(desc),
            pexp_loc: loc,
            pexp_attributes: attrs,
        }
    }

    /// A function node in the arena shape the parser builds: the first
    /// parameter inline, the complete list in the n-ary side table.
    fn mk_fun(
        &mut self,
        loc: LocIdx,
        attrs: Attributes,
        params: Vec<current::FunParam>,
        body: ExprIdx,
        is_async: bool,
    ) -> current::Expression {
        let arity = self.arena.push_arity(Some(params.len() as i32));
        let unknown_arity = self.arena.push_arity(None);
        let first = params[0].clone();
        self.arena.set_nary_fun_params(arity, params, unknown_arity);
        current::Expression {
            pexp_desc: Box::new(current::ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label: first.p_lbl,
                default: first.p_default,
                lhs: first.p_pat,
                rhs: body,
                arity,
                is_async,
            }))),
            pexp_loc: loc,
            pexp_attributes: attrs,
        }
    }

    /// An arrow node in the arena shape the parser builds.
    fn mk_arrow(
        &mut self,
        params: Vec<current::TypeArg>,
        ret: CoreTypeIdx,
        loc: LocIdx,
        attrs: Attributes,
    ) -> current::CoreType {
        let arity = self.arena.push_arity(Some(params.len() as i32));
        let first = params[0].clone();
        self.arena.set_nary_arrow_args(arity, params);
        current::CoreType {
            ptyp_desc: Box::new(current::CoreTypeDesc::Ptyp_arrow(Box::new((
                Box::new(first),
                ret,
                arity,
            )))),
            ptyp_loc: loc,
            ptyp_attributes: attrs,
        }
    }

    fn fun_params(&self, f: &PexpFun) -> Vec<current::FunParam> {
        self.arena.nary_fun_params(f).into_owned()
    }

    /// ast_mapper_from0.ml `gather` for `Function$`: collect [n] parameters
    /// from the chain of functions; nested first-class functions are left
    /// intact. Returns the parameters and the body, `None` when nothing was
    /// gathered.
    fn gather_fun(
        &self,
        head: &current::Expression,
        n: usize,
    ) -> (Vec<current::FunParam>, Option<ExprIdx>) {
        let mut params = Vec::new();
        let mut body = None;
        let mut remaining = n;
        let mut current_expr = head.clone();
        let mut is_head = true;
        while remaining > 0 {
            let current::ExpressionDesc::Pexp_fun(f) = &*current_expr.pexp_desc else {
                break;
            };
            let level = self.fun_params(f);
            if level.len() > remaining
                || !(is_head || (current_expr.pexp_attributes.is_empty() && !f.is_async))
            {
                break;
            }
            remaining -= level.len();
            params.extend(level);
            let level_body = self.arena.nary_fun_body(f);
            body = Some(level_body);
            is_head = false;
            current_expr = self.arena.get_expr(level_body).clone();
        }
        (params, body)
    }

    /// ast_mapper_from0.ml `gather` for `function$`.
    fn gather_arrow(
        &self,
        head: &current::CoreType,
        n: usize,
    ) -> (Vec<current::TypeArg>, Option<CoreTypeIdx>) {
        let mut params = Vec::new();
        let mut ret = None;
        let mut remaining = n;
        let mut current_typ = head.clone();
        let mut is_head = true;
        while remaining > 0 {
            let current::CoreTypeDesc::Ptyp_arrow(inner) = &*current_typ.ptyp_desc else {
                break;
            };
            let (arg, level_ret, arity) = &**inner;
            let level = self.arena.nary_arrow_args(arg, *arity).into_owned();
            if level.len() > remaining || !(is_head || current_typ.ptyp_attributes.is_empty()) {
                break;
            }
            remaining -= level.len();
            params.extend(level);
            ret = Some(*level_ret);
            is_head = false;
            current_typ = self.arena.get_core_type(*level_ret).clone();
        }
        (params, ret)
    }

    /// ast_mapper_from0.ml Pexp_newtype: fuse a chain of newtype wrappers
    /// over a `Function$` node into the function's newtypes. On the
    /// outermost wrapper, attributes before the internal
    /// `_res.newtype_attrs` marker (all of them, without a marker) are
    /// function-node attributes.
    fn map_newtype(
        &mut self,
        expr: &pt0::Expression,
        name: &OldLocated<String>,
        body: &pt0::Expression,
        loc: LocIdx,
    ) -> current::Expression {
        let (node_attrs, first_attrs) =
            split_at_marker(&expr.pexp_attributes, "_res.newtype_attrs")
                .unwrap_or((&expr.pexp_attributes[..], &[]));
        let mut chain = vec![(name, first_attrs)];
        let mut e = body;
        let base = loop {
            match &e.pexp_desc {
                pt0::ExpressionDesc::Newtype(name, body) => {
                    chain.push((name, &e.pexp_attributes[..]));
                    e = body;
                }
                pt0::ExpressionDesc::Construct(lid, Some(_))
                    if self.is_lident(&lid.txt, "Function$") =>
                {
                    break Some(e);
                }
                _ => break None,
            }
        };
        let newtypes: Vec<(Located<StrIdx>, Attributes)> = chain
            .iter()
            .map(|(name, attrs)| (self.map_string_loc(name), self.map_attributes(attrs)))
            .collect();
        if let Some(base) = base {
            let base1 = self.map_expression(base);
            if let current::ExpressionDesc::Pexp_fun(f) = &*base1.pexp_desc
                && self.arena.nary_fun_newtypes(f).is_empty()
            {
                self.arena.set_nary_fun_newtypes(f.lhs, newtypes);
                let mut attrs = base1.pexp_attributes.clone();
                attrs.extend(self.map_attributes(node_attrs));
                return current::Expression {
                    pexp_desc: base1.pexp_desc,
                    pexp_loc: loc,
                    pexp_attributes: attrs,
                };
            }
        }
        let attrs = self.map_attributes(&expr.pexp_attributes);
        let error = self.error_extension(
            "A PPX returned a locally abstract type wrapper that does not enclose a ReScript function. This v0 AST form is not supported.",
            &expr.pexp_loc,
        );
        current::Expression {
            pexp_desc: Box::new(current::ExpressionDesc::Pexp_extension(Box::new(error))),
            pexp_loc: loc,
            pexp_attributes: attrs,
        }
    }

    /// `Ast_mapper.extension_of_error` for a located message.
    fn error_extension(&mut self, msg: &str, loc: &FullLocation) -> current::Extension {
        let loc_idx = self.loc(loc);
        let str_item = |mapper: &mut Self, s: &str| {
            let expr = mapper.arena.push_expr(current::Expression {
                pexp_desc: Box::new(current::ExpressionDesc::Pexp_constant(Box::new(
                    current::Constant::string(s),
                ))),
                pexp_loc: loc_idx,
                pexp_attributes: Attributes::new(),
            });
            current::StructureItem {
                pstr_desc: Box::new(current::StructureItemDesc::Pstr_eval(Box::new((
                    expr,
                    Attributes::new(),
                )))),
                pstr_loc: loc_idx,
            }
        };
        let items = vec![str_item(self, msg), str_item(self, "")];
        (
            self.mk_string_loc("ocaml.error", loc),
            current::Payload::PStr(Box::new(items)),
        )
    }

    fn record_rest_of_pattern(&mut self, rest: &pt0::Pattern) -> Option<current::RecordPatRest> {
        match &rest.ppat_desc {
            pt0::PatternDesc::Constraint(var, typ) => match &var.ppat_desc {
                pt0::PatternDesc::Var(name) => Some(current::RecordPatRest {
                    rest_loc: self.loc(&rest.ppat_loc),
                    rest_name: self.map_string_loc(name),
                    rest_type: Some(self.push_core_type(typ)),
                }),
                _ => None,
            },
            pt0::PatternDesc::Var(name) => Some(current::RecordPatRest {
                rest_loc: self.loc(&rest.ppat_loc),
                rest_name: self.map_string_loc(name),
                rest_type: None,
            }),
            _ => None,
        }
    }

    /// ast_mapper_from0.ml value_binding: `(x : a. t')` over
    /// `(type a) => (e : t)` with `t'` the varified `t` is a
    /// locally abstract constraint.
    fn decode_value_constraint<'x>(
        &self,
        vb: &'x pt0::ValueBinding,
    ) -> Option<(
        &'x pt0::Pattern,
        &'x pt0::Expression,
        Vec<&'x OldLocated<String>>,
        &'x pt0::CoreType,
    )> {
        let pt0::PatternDesc::Constraint(pat, poly) = &vb.pvb_pat.ppat_desc else {
            return None;
        };
        let pt0::CoreTypeDesc::Poly(poly_newtypes, poly_type) = &poly.ptyp_desc else {
            return None;
        };
        if !vb.pvb_pat.ppat_attributes.is_empty()
            || !poly.ptyp_attributes.is_empty()
            || poly_newtypes.is_empty()
        {
            return None;
        }
        let mut newtypes = Vec::new();
        let mut e = &vb.pvb_expr;
        let (expr, typ) = loop {
            if !e.pexp_attributes.is_empty() {
                return None;
            }
            match &e.pexp_desc {
                pt0::ExpressionDesc::Newtype(name, rest) => {
                    newtypes.push(name);
                    e = rest;
                }
                pt0::ExpressionDesc::Constraint(expr, typ) => break (expr.as_ref(), typ.as_ref()),
                _ => return None,
            }
        };
        let names: Vec<&str> = newtypes.iter().map(|n| n.txt.as_str()).collect();
        let poly_names: Vec<&str> = poly_newtypes.iter().map(|n| n.txt.as_str()).collect();
        if names != poly_names
            || varify_constructors(self.arena, &names, typ).as_ref() != Some(poly_type.as_ref())
        {
            return None;
        }
        Some((pat, expr, newtypes, typ))
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
        if let Some((pat, expr, newtypes, typ)) = self.decode_value_constraint(vb) {
            let pvb_pat = self.push_pat(pat);
            let pvb_expr = self.push_expr(expr);
            let pvb_loc = self.loc(&vb.pvb_loc);
            let constraint = current::ValueConstraint {
                pvc_newtypes: newtypes.iter().map(|n| self.map_string_loc(n)).collect(),
                pvc_type: self.push_core_type(typ),
                pvc_pattern: None,
                pvc_expression: None,
            };
            self.arena
                .set_value_constraint(pvb_pat, constraint, pvb_expr, pvb_loc);
            return current::ValueBinding {
                pvb_pat,
                pvb_expr,
                pvb_attributes: self.map_attributes(&vb.pvb_attributes),
                pvb_loc,
            };
        }
        current::ValueBinding {
            pvb_pat: self.push_pat(&vb.pvb_pat),
            pvb_expr: self.push_expr(&vb.pvb_expr),
            pvb_attributes: self.map_attributes(&vb.pvb_attributes),
            pvb_loc: self.loc(&vb.pvb_loc),
        }
    }

    // ========== Module expressions ==========

    fn map_module_expr(&mut self, me: &pt0::ModuleExpr) -> current::ModuleExpr {
        // ast_mapper_from0.ml M.map: `Ast_mapper_to0` puts the inner module's
        // attributes before the `res.await` marker and the await node's after
        // it. The last marker belongs to the outermost await.
        if let Some(at) = me
            .pmod_attributes
            .iter()
            .rposition(|(name, _)| name.txt == "res.await")
        {
            let marker_loc = me.pmod_attributes[at].0.loc;
            // `await_marker_loc`: a marker without a location falls back to
            // the node's.
            let none = self.arena.to_location(self.arena.none_loc());
            let await_loc = if marker_loc == none {
                me.pmod_loc
            } else {
                marker_loc
            };
            let inner = pt0::ModuleExpr {
                pmod_desc: me.pmod_desc.clone(),
                pmod_loc: me.pmod_loc,
                pmod_attributes: me.pmod_attributes[..at].to_vec(),
            };
            let inner_idx = self.push_mod_expr(&inner);
            let loc = self.loc(&await_loc);
            let attrs = self.map_attributes(&me.pmod_attributes[at + 1..]);
            return current::ModuleExpr {
                pmod_desc: Box::new(current::ModuleExprDesc::Pmod_await(inner_idx)),
                pmod_loc: loc,
                pmod_attributes: attrs,
            };
        }
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
            pmod_attributes: attrs,
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
            pmty_attributes: attrs,
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
        // Ast_helper.Type.mk: the first `res.inlineRecordDefinition`
        // attribute becomes the declaration's origin.
        let mut ptype_attributes = self.map_attributes(&td.ptype_attributes);
        let ptype_origin = match ptype_attributes
            .iter()
            .position(|(name, _)| self.arena.get_string(name.txt) == "res.inlineRecordDefinition")
        {
            Some(at) => {
                ptype_attributes.remove(at);
                current::TypeDeclarationOrigin::Inline_record_definition
            }
            None => current::TypeDeclarationOrigin::Declared,
        };
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
            ptype_origin,
            ptype_attributes,
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
        // ast_mapper_from0.ml: `Type.constructor`, which takes a valid
        // `@as` out of the attributes.
        let name = self.map_string_loc(&cd.pcd_name);
        let args = self.map_constructor_arguments(&cd.pcd_args);
        let res = cd.pcd_res.as_ref().map(|t| self.push_core_type(t));
        let loc = self.loc(&cd.pcd_loc);
        let attrs = self.map_attributes(&cd.pcd_attributes);
        crate::ast_helper_type::constructor(self.arena, loc, attrs, args, res, None, name)
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

        // ast_mapper_from0.ml: `Type.field`, which takes the `@as` rename
        // out of the attributes.
        let name = self.map_string_loc(&ld.pld_name);
        let mutable = map_mutable_flag(ld.pld_mutable);
        let typ = self.push_core_type(&ld.pld_type);
        let loc = self.loc(&ld.pld_loc);
        crate::ast_helper_type::field(
            self.arena,
            loc,
            final_attrs,
            mutable,
            optional,
            None,
            name,
            typ,
        )
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
            ptyext_attributes: self.map_attributes(&te.ptyext_attributes),
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
            pext_attributes: self.map_attributes(&ec.pext_attributes),
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
        // ast_mapper_from0.ml: a parsetree0 external carries one string.
        let pval_prim = match vd.pval_prim.as_slice() {
            [] => None,
            [s] => Some(current::PrimitiveRepr::PrimName(
                self.arena.push_string(s.clone()),
            )),
            _ => {
                if self.error.is_none() {
                    let loc = self.loc(&vd.pval_loc);
                    self.error = Some(crate::binary_ast::ppx::PpxError::at_loc(
                        loc,
                        "An external declaration can carry only a single primitive string",
                    ));
                }
                None
            }
        };
        current::ValueDescription {
            pval_name: self.map_string_loc(&vd.pval_name),
            pval_type: self.push_core_type(&vd.pval_type),
            pval_prim,
            pval_attributes: self.map_attributes(&vd.pval_attributes),
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
            pmd_attributes: self.map_attributes(&md.pmd_attributes),
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
            pmtd_attributes: self.map_attributes(&mtd.pmtd_attributes),
            pmtd_loc: self.loc(&mtd.pmtd_loc),
        }
    }

    fn map_module_binding(&mut self, mb: &pt0::ModuleBinding) -> current::ModuleBinding {
        current::ModuleBinding {
            pmb_name: self.map_string_loc(&mb.pmb_name),
            pmb_expr: self.push_mod_expr(&mb.pmb_expr),
            pmb_attributes: self.map_attributes(&mb.pmb_attributes),
            pmb_loc: self.loc(&mb.pmb_loc),
        }
    }

    fn map_open_description(&mut self, od: &pt0::OpenDescription) -> current::OpenDescription {
        current::OpenDescription {
            popen_lid: self.map_longident_loc(&od.popen_lid),
            popen_override: map_override_flag(od.popen_override),
            popen_loc: self.loc(&od.popen_loc),
            popen_attributes: self.map_attributes(&od.popen_attributes),
        }
    }

    fn map_include_declaration(
        &mut self,
        id: &pt0::IncludeDeclaration,
    ) -> current::IncludeDeclaration {
        current::IncludeDeclaration {
            pincl_mod: self.push_mod_expr(&id.pincl_mod),
            pincl_loc: self.loc(&id.pincl_loc),
            pincl_attributes: self.map_attributes(&id.pincl_attributes),
        }
    }

    fn map_include_description(
        &mut self,
        id: &pt0::IncludeDescription,
    ) -> current::IncludeDescription {
        current::IncludeDescription {
            pincl_mod: self.push_mod_type(&id.pincl_mod),
            pincl_loc: self.loc(&id.pincl_loc),
            pincl_attributes: self.map_attributes(&id.pincl_attributes),
        }
    }
}

/// The rows of the v0 `%obj` encoding of an object literal: a single
/// `Pstr_eval` with no attributes of a record without spread whose labels are
/// all `Lident` (ast_mapper_from0.ml `Pexp_extension ({txt = "obj"}, ...)`).
fn v0_object_literal_rows(
    items: &[pt0::StructureItem],
) -> Option<&[(OldLocated<Longident>, pt0::Expression)]> {
    let [item] = items else {
        return None;
    };
    let pt0::StructureItemDesc::Eval(e, eval_attrs) = &item.pstr_desc else {
        return None;
    };
    if !eval_attrs.is_empty() {
        return None;
    }
    let pt0::ExpressionDesc::Record(rows, None) = &e.pexp_desc else {
        return None;
    };
    rows.iter()
        .all(|(lid, _)| matches!(lid.txt, Longident::Lident(_)))
        .then_some(rows.as_slice())
}
