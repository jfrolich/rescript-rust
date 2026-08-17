//! Mapper from current parsetree to parsetree0
//!
//! This module converts the current Rust parsetree types to the frozen parsetree0
//! format used for binary AST serialization.
//!
//! Key transformations:
//! - Function arity → [@res.arity N] attribute + Function$ wrapper
//! - Arrow type arity → function$ type constructor
//! - async flag → [@res.async] attribute
//! - Pexp_await → [@res.await] attribute on expression
//! - partial flag → [@res.partial] attribute
//! - optional record fields → [@res.optional] attribute
//! - JSX elements → already handled by JSX PPX
//!
//! This mirrors `compiler/common/ast_mapper_to0.ml`.

use crate::intern::StrIdx;
use crate::location::{Located as OldLocated, Location as FullLocation};
use crate::parse_arena::{
    CoreTypeIdx, ExprIdx, LocIdx, Located, ModExprIdx, ModTypeIdx, ParseArena, PatIdx,
};
use crate::parser::ast::{self as current, PexpApply, PexpFun};
use crate::parser::longident::Longident;

use super::parsetree0 as pt0;

// ========== Public API ==========

/// Convert a structure from current parsetree to parsetree0
pub fn map_structure(arena: &mut ParseArena, str: &[current::StructureItem]) -> pt0::Structure {
    let mut mapper = Mapper::new(arena);
    mapper.map_structure(str)
}

/// Convert a signature from current parsetree to parsetree0
pub fn map_signature(arena: &mut ParseArena, sig: &[current::SignatureItem]) -> pt0::Signature {
    let mut mapper = Mapper::new(arena);
    mapper.map_signature(sig)
}

// ========== Mapper struct ==========

/// Mapper from current parsetree (with LocIdx) to parsetree0 (with full Location).
/// Holds a reference to the arena for converting LocIdx values to Location.
pub struct Mapper<'a> {
    arena: &'a mut ParseArena,
}

impl<'a> Mapper<'a> {
    pub fn new(arena: &'a mut ParseArena) -> Self {
        Self { arena }
    }

    /// Intern a string to get a StrIdx (for creating synthetic Longidents)
    fn intern(&mut self, s: &str) -> StrIdx {
        self.arena.intern_string(s)
    }

    /// Get the string content for a StrIdx
    fn get_str(&self, idx: StrIdx) -> &str {
        self.arena.get_string(idx)
    }

    /// Convert a LocIdx to full Location
    fn loc(&mut self, idx: LocIdx) -> FullLocation {
        self.arena.to_location(idx)
    }

    /// Convert an arena-based Located<T> to a full Located<T>
    fn map_loc<T: Clone>(&mut self, located: &Located<T>) -> OldLocated<T> {
        OldLocated {
            txt: located.txt.clone(),
            loc: self.loc(located.loc),
        }
    }

    /// Convert a Located<Cow<'static, str>> to OldLocated<String> for labels
    fn map_label_loc(
        &mut self,
        located: &Located<std::borrow::Cow<'static, str>>,
    ) -> OldLocated<String> {
        OldLocated {
            txt: located.txt.to_string(),
            loc: self.loc(located.loc),
        }
    }

    /// Convert a Located<StrIdx> to OldLocated<String> by looking up the string
    fn map_string_loc(&mut self, located: &Located<StrIdx>) -> OldLocated<String> {
        OldLocated {
            txt: self.arena.get_string(located.txt).to_string(),
            loc: self.loc(located.loc),
        }
    }

    /// Convert a Located<LidentIdx> to OldLocated<Longident> by looking up in arena
    fn map_longident_loc(
        &mut self,
        located: &Located<crate::parse_arena::LidentIdx>,
    ) -> OldLocated<crate::parser::longident::Longident> {
        OldLocated {
            txt: self.arena.get_longident(located.txt).clone(),
            loc: self.loc(located.loc),
        }
    }

    /// Get the longident for a LidentIdx
    fn get_longident(
        &mut self,
        idx: crate::parse_arena::LidentIdx,
    ) -> &crate::parser::longident::Longident {
        self.arena.get_longident(idx)
    }

    /// Create an OldLocated from text and location index
    #[allow(dead_code)]
    fn mkloc<T>(&mut self, txt: T, loc: LocIdx) -> OldLocated<T> {
        OldLocated {
            txt,
            loc: self.loc(loc),
        }
    }

    // ========== Arena index lookup helpers ==========
    // These methods look up an arena-indexed AST node and map it.
    // We clone the looked-up node to avoid borrow conflicts (`self.arena` is `&mut`).

    fn map_expr_idx(&mut self, idx: ExprIdx) -> pt0::Expression {
        let expr = self.arena.get_expr(idx).clone();
        self.map_expression_with_owner(&expr, Some(idx))
    }

    fn map_pat_idx(&mut self, idx: PatIdx) -> pt0::Pattern {
        let pat = self.arena.get_pat(idx).clone();
        self.map_pattern(&pat)
    }

    fn map_core_type_idx(&mut self, idx: CoreTypeIdx) -> pt0::CoreType {
        let ct = self.arena.get_core_type(idx).clone();
        self.map_core_type(&ct)
    }

    fn map_mod_expr_idx(&mut self, idx: ModExprIdx) -> pt0::ModuleExpr {
        let me = self.arena.get_mod_expr(idx).clone();
        self.map_module_expr(&me)
    }

    fn map_mod_type_idx(&mut self, idx: ModTypeIdx) -> pt0::ModuleType {
        let mt = self.arena.get_mod_type(idx).clone();
        self.map_module_type(&mt)
    }

    // ========== Public API methods ==========

    /// Convert a structure from current parsetree to parsetree0
    pub fn map_structure(&mut self, str: &[current::StructureItem]) -> pt0::Structure {
        str.iter()
            .map(|item| self.map_structure_item(item))
            .collect()
    }

    /// Convert a signature from current parsetree to parsetree0
    pub fn map_signature(&mut self, sig: &[current::SignatureItem]) -> pt0::Signature {
        sig.iter()
            .map(|item| self.map_signature_item(item))
            .collect()
    }

    // ========== Helper functions ==========

    #[allow(dead_code)]
    fn mk_optional_attr(&mut self, loc: LocIdx) -> pt0::Attribute {
        (
            OldLocated::new("res.optional".to_string(), self.loc(loc)),
            pt0::Payload::PStr(vec![]),
        )
    }

    #[allow(dead_code)]
    fn mk_async_attr(&mut self, loc: LocIdx) -> pt0::Attribute {
        (
            OldLocated::new("res.async".to_string(), self.loc(loc)),
            pt0::Payload::PStr(vec![]),
        )
    }

    fn mk_await_attr(&mut self) -> pt0::Attribute {
        let loc = self.arena.none_loc();
        (
            OldLocated::new("res.await".to_string(), self.loc(loc)),
            pt0::Payload::PStr(vec![]),
        )
    }

    #[allow(dead_code)]
    fn mk_partial_attr(&mut self, loc: LocIdx) -> pt0::Attribute {
        (
            OldLocated::new("res.partial".to_string(), self.loc(loc)),
            pt0::Payload::PStr(vec![]),
        )
    }

    #[allow(dead_code)]
    fn mk_arity_attr(&mut self, arity: usize, loc: LocIdx) -> pt0::Attribute {
        let full_loc = self.loc(loc);
        (
            OldLocated::new("res.arity".to_string(), full_loc.clone()),
            pt0::Payload::PStr(vec![pt0::StructureItem {
                pstr_desc: pt0::StructureItemDesc::Eval(
                    pt0::Expression {
                        pexp_desc: pt0::ExpressionDesc::Constant(pt0::Constant::Integer(
                            arity.to_string(),
                            None,
                        )),
                        pexp_loc: full_loc.clone(),
                        pexp_attributes: vec![],
                    },
                    vec![],
                ),
                pstr_loc: full_loc,
            }]),
        )
    }

    // ========== JSX helpers ==========

    fn mk_jsx_attr(&mut self, loc: LocIdx) -> pt0::Attribute {
        (
            OldLocated::new("JSX".to_string(), self.loc(loc)),
            pt0::Payload::PStr(vec![]),
        )
    }

    fn mk_unit_expr(&mut self, loc: LocIdx) -> pt0::Expression {
        let full_loc = self.loc(loc);
        let unit_idx = self.intern("()");
        pt0::Expression {
            pexp_desc: pt0::ExpressionDesc::Construct(
                OldLocated::new(Longident::Lident(unit_idx), full_loc.clone()),
                None,
            ),
            pexp_loc: full_loc,
            pexp_attributes: vec![],
        }
    }

    fn mk_nil_expr(&mut self, loc: LocIdx) -> pt0::Expression {
        let full_loc = self.loc(loc);
        let nil_idx = self.intern("[]");
        pt0::Expression {
            pexp_desc: pt0::ExpressionDesc::Construct(
                OldLocated::new(Longident::Lident(nil_idx), full_loc.clone()),
                None,
            ),
            pexp_loc: full_loc,
            pexp_attributes: vec![],
        }
    }

    fn map_jsx_props(
        &mut self,
        props: &[current::JsxProp],
        _loc: LocIdx,
    ) -> Vec<(pt0::ArgLabel, pt0::Expression)> {
        let mut result = Vec::with_capacity(props.len());
        for prop in props {
            let item = match prop {
                current::JsxProp::Punning { optional, name } => {
                    let name_loc = self.loc(name.loc);
                    // Use the StrIdx directly - it's already interned and enables sharing
                    let name_idx = name.txt;
                    let ident_expr = pt0::Expression {
                        pexp_desc: pt0::ExpressionDesc::Ident(OldLocated::new(
                            Longident::Lident(name_idx),
                            name_loc.clone(),
                        )),
                        pexp_loc: name_loc,
                        pexp_attributes: vec![],
                    };
                    let label = if *optional {
                        pt0::ArgLabel::Optional(name_idx)
                    } else {
                        pt0::ArgLabel::Labelled(name_idx)
                    };
                    (label, ident_expr)
                }
                current::JsxProp::Value {
                    name,
                    optional,
                    value,
                } => {
                    let name_idx = name.txt;
                    let label = if *optional {
                        pt0::ArgLabel::Optional(name_idx)
                    } else {
                        pt0::ArgLabel::Labelled(name_idx)
                    };
                    let name_loc = self.loc(name.loc);
                    let mut value_expr = self.map_expr_idx(*value);
                    value_expr.pexp_attributes.insert(
                        0,
                        (
                            OldLocated::new("res.jsxPropLoc".to_string(), name_loc),
                            pt0::Payload::PStr(vec![]),
                        ),
                    );
                    (label, value_expr)
                }
                current::JsxProp::Spreading { loc, expr } => {
                    let spread_idx = self.intern("_spreadProps");
                    let spread_loc = self.loc(*loc);
                    let mut value_expr = self.map_expr_idx(*expr);
                    value_expr.pexp_attributes.insert(
                        0,
                        (
                            OldLocated::new("res.jsxSpreadLoc".to_string(), spread_loc),
                            pt0::Payload::PStr(vec![]),
                        ),
                    );
                    (pt0::ArgLabel::Labelled(spread_idx), value_expr)
                }
            };
            result.push(item);
        }
        result
    }

    fn jsx_tag_to_longident(&mut self, tag: &current::JsxTagName) -> Longident {
        match tag {
            current::JsxTagName::Lower(name) => {
                let idx = self.intern(name);
                Longident::Lident(idx)
            }
            current::JsxTagName::QualifiedLower { path, name } => {
                let name_idx = self.intern(name);
                Longident::Ldot(Box::new(self.get_longident(*path).clone()), name_idx)
            }
            current::JsxTagName::Upper(lid_idx) => self.get_longident(*lid_idx).clone(),
            current::JsxTagName::Invalid(name) => {
                let idx = self.intern(name);
                Longident::Lident(idx)
            }
        }
    }

    fn map_jsx_children_to_list(&mut self, children: &[ExprIdx], loc: LocIdx) -> pt0::Expression {
        // Convert children to a list expression (cons cells ending with [])
        let mut result = self.mk_nil_expr(loc);
        let full_loc = self.loc(loc);
        let cons_idx = self.intern("::");
        for child in children.iter().rev() {
            let child_expr = self.map_expr_idx(*child);
            result = pt0::Expression {
                pexp_desc: pt0::ExpressionDesc::Construct(
                    OldLocated::new(Longident::Lident(cons_idx), full_loc.clone()),
                    Some(Box::new(pt0::Expression {
                        pexp_desc: pt0::ExpressionDesc::Tuple(vec![child_expr, result]),
                        pexp_loc: full_loc.clone(),
                        pexp_attributes: vec![],
                    })),
                ),
                pexp_loc: full_loc.clone(),
                pexp_attributes: vec![],
            };
        }
        result
    }

    // ========== Flag conversions ==========

    fn map_rec_flag(&mut self, flag: current::RecFlag) -> pt0::RecFlag {
        match flag {
            current::RecFlag::Nonrecursive => pt0::RecFlag::Nonrecursive,
            current::RecFlag::Recursive => pt0::RecFlag::Recursive,
        }
    }

    fn map_direction_flag(&mut self, flag: current::DirectionFlag) -> pt0::DirectionFlag {
        match flag {
            current::DirectionFlag::Upto => pt0::DirectionFlag::Upto,
            current::DirectionFlag::Downto => pt0::DirectionFlag::Downto,
        }
    }

    fn map_closed_flag(&mut self, flag: current::ClosedFlag) -> pt0::ClosedFlag {
        match flag {
            current::ClosedFlag::Closed => pt0::ClosedFlag::Closed,
            current::ClosedFlag::Open => pt0::ClosedFlag::Open,
        }
    }

    fn map_override_flag(&mut self, flag: current::OverrideFlag) -> pt0::OverrideFlag {
        match flag {
            current::OverrideFlag::Fresh => pt0::OverrideFlag::Fresh,
            current::OverrideFlag::Override => pt0::OverrideFlag::Override,
        }
    }

    fn map_mutable_flag(&mut self, flag: current::MutableFlag) -> pt0::MutableFlag {
        match flag {
            current::MutableFlag::Immutable => pt0::MutableFlag::Immutable,
            current::MutableFlag::Mutable => pt0::MutableFlag::Mutable,
        }
    }

    fn map_private_flag(&mut self, flag: current::PrivateFlag) -> pt0::PrivateFlag {
        match flag {
            current::PrivateFlag::Private => pt0::PrivateFlag::Private,
            current::PrivateFlag::Public => pt0::PrivateFlag::Public,
        }
    }

    fn map_variance(&mut self, var: current::Variance) -> pt0::Variance {
        match var {
            current::Variance::Covariant => pt0::Variance::Covariant,
            current::Variance::Contravariant => pt0::Variance::Contravariant,
            current::Variance::Invariant => pt0::Variance::Invariant,
        }
    }

    fn map_arg_label(&mut self, label: &current::ArgLabel) -> pt0::ArgLabel {
        match label {
            current::ArgLabel::Nolabel => pt0::ArgLabel::Nolabel,
            // Current parsetree already uses StrIdx, just pass it through
            current::ArgLabel::Labelled(s) => pt0::ArgLabel::Labelled(s.txt),
            current::ArgLabel::Optional(s) => pt0::ArgLabel::Optional(s.txt),
        }
    }

    // ========== Constant ==========

    fn map_constant(&mut self, c: &current::Constant) -> pt0::Constant {
        match c {
            current::Constant::Integer(s, opt) => pt0::Constant::Integer(s.to_string(), *opt),
            current::Constant::Char(i) => pt0::Constant::Char(*i),
            current::Constant::String(s, opt) => {
                // OCaml maps None (regular strings) to Some("js") in parsetree0.
                // The "*j" transformation happens later in Ast_config.process_str during compilation,
                // NOT during parsetree0 conversion.
                // For parsetree0 parity, we just need to convert None -> Some("js").
                let mapped_delim = match opt {
                    None => Some("js".to_string()),
                    other => other.as_ref().map(|d| d.to_string()),
                };
                pt0::Constant::String(s.to_string(), mapped_delim)
            }
            current::Constant::Float(s, opt) => pt0::Constant::Float(s.to_string(), *opt),
        }
    }

    // ========== Attributes ==========

    fn map_attribute(&mut self, attr: &current::Attribute) -> pt0::Attribute {
        let (name, payload) = attr;
        (self.map_string_loc(name), self.map_payload(payload))
    }

    fn map_attributes(&mut self, attrs: &current::Attributes) -> pt0::Attributes {
        attrs.iter().map(|a| self.map_attribute(a)).collect()
    }

    fn map_payload(&mut self, payload: &current::Payload) -> pt0::Payload {
        match payload {
            current::Payload::PStr(items) => {
                pt0::Payload::PStr(items.iter().map(|i| self.map_structure_item(i)).collect())
            }
            current::Payload::PSig(items) => {
                pt0::Payload::PSig(items.iter().map(|i| self.map_signature_item(i)).collect())
            }
            current::Payload::PTyp(ty_idx) => {
                pt0::Payload::PTyp(Box::new(self.map_core_type_idx(*ty_idx)))
            }
            current::Payload::PPat(inner) => {
                let (ref pat_idx, ref guard) = **inner;
                pt0::Payload::PPat(
                    Box::new(self.map_pat_idx(*pat_idx)),
                    guard.as_ref().map(|e| Box::new(self.map_expr_idx(*e))),
                )
            }
        }
    }

    // ========== Core Types ==========

    pub fn map_core_type(&mut self, ty: &current::CoreType) -> pt0::CoreType {
        // Handle arrow types specially to support arity wrapping
        if let current::CoreTypeDesc::Ptyp_arrow(inner) = &*ty.ptyp_desc {
            let (ref arg, ref ret_idx, ref arity) = **inner;
            let loc = self.loc(ty.ptyp_loc);
            // Merge outer type's attributes with arg's attributes (OCaml does this)
            let arrow_attrs: Vec<pt0::Attribute> = self
                .map_attributes(&ty.ptyp_attributes)
                .into_iter()
                .chain(self.map_attributes(&arg.attrs))
                .collect();

            // Create the base arrow type
            let arrow_type = pt0::CoreType {
                ptyp_desc: pt0::CoreTypeDesc::Arrow(
                    self.map_arg_label(&arg.lbl),
                    Box::new(self.map_core_type_idx(arg.typ)),
                    Box::new(self.map_core_type_idx(*ret_idx)),
                ),
                ptyp_loc: loc.clone(),
                ptyp_attributes: arrow_attrs,
            };

            // Look up arity value from arena (current::Arity is now ArityIdx)
            let arity_value = self.arena.get_arity(*arity);
            match arity_value {
                None => arrow_type,
                Some(n) => {
                    // Wrap in function$ type constructor with arity variant
                    // Creates: function$<arrow_type, [ `Has_arity{N} ]>
                    let arity_string = format!("Has_arity{}", n);
                    let function_idx = self.intern("function$");
                    let arity_type = pt0::CoreType {
                        ptyp_desc: pt0::CoreTypeDesc::Variant(
                            vec![pt0::RowField::Rtag(
                                OldLocated::new(arity_string, loc.clone()),
                                vec![], // no attributes
                                true,   // constant (no payload)
                                vec![], // no types
                            )],
                            pt0::ClosedFlag::Closed,
                            None,
                        ),
                        ptyp_loc: loc.clone(),
                        ptyp_attributes: vec![],
                    };
                    pt0::CoreType {
                        ptyp_desc: pt0::CoreTypeDesc::Constr(
                            OldLocated::new(Longident::Lident(function_idx), loc.clone()),
                            vec![arrow_type, arity_type],
                        ),
                        ptyp_loc: loc,
                        ptyp_attributes: vec![],
                    }
                }
            }
        } else {
            pt0::CoreType {
                ptyp_desc: self.map_core_type_desc(&*ty.ptyp_desc),
                ptyp_loc: self.loc(ty.ptyp_loc),
                ptyp_attributes: self.map_attributes(&ty.ptyp_attributes),
            }
        }
    }

    fn map_core_type_desc(&mut self, desc: &current::CoreTypeDesc) -> pt0::CoreTypeDesc {
        match desc {
            current::CoreTypeDesc::Ptyp_any => pt0::CoreTypeDesc::Any,
            current::CoreTypeDesc::Ptyp_var(s) => pt0::CoreTypeDesc::Var(s.to_string()),
            current::CoreTypeDesc::Ptyp_arrow(inner) => {
                let (ref arg, ref ret_idx, ref arity) = **inner;
                // This branch should not normally be reached since map_core_type handles arrows
                // But keep it for completeness - treat as no arity
                pt0::CoreTypeDesc::Arrow(
                    self.map_arg_label(&arg.lbl),
                    Box::new(self.map_core_type_idx(arg.typ)),
                    Box::new(self.map_core_type_idx(*ret_idx)),
                )
            }
            current::CoreTypeDesc::Ptyp_tuple(types) => {
                pt0::CoreTypeDesc::Tuple(types.iter().map(|t| self.map_core_type_idx(*t)).collect())
            }
            current::CoreTypeDesc::Ptyp_constr(inner) => {
                let (ref lid, ref types) = **inner;
                pt0::CoreTypeDesc::Constr(
                    self.map_longident_loc(lid),
                    types.iter().map(|t| self.map_core_type_idx(*t)).collect(),
                )
            }
            current::CoreTypeDesc::Ptyp_object(inner) => {
                let (ref fields, ref flag) = **inner;
                pt0::CoreTypeDesc::Object(
                    fields.iter().map(|f| self.map_object_field(f)).collect(),
                    self.map_closed_flag(*flag),
                )
            }
            current::CoreTypeDesc::Ptyp_alias(inner) => {
                let (ref ty_idx, ref s) = **inner;
                pt0::CoreTypeDesc::Alias(Box::new(self.map_core_type_idx(*ty_idx)), s.to_string())
            }
            current::CoreTypeDesc::Ptyp_variant(inner) => {
                let (ref fields, ref flag, ref labels) = **inner;
                pt0::CoreTypeDesc::Variant(
                    fields.iter().map(|f| self.map_row_field(f)).collect(),
                    self.map_closed_flag(*flag),
                    labels
                        .as_ref()
                        .map(|ls| ls.iter().map(|l| l.to_string()).collect()),
                )
            }
            current::CoreTypeDesc::Ptyp_poly(inner) => {
                let (ref vars, ref ty_idx) = **inner;
                pt0::CoreTypeDesc::Poly(
                    vars.iter().map(|v| self.map_string_loc(v)).collect(),
                    Box::new(self.map_core_type_idx(*ty_idx)),
                )
            }
            current::CoreTypeDesc::Ptyp_package(pkg) => {
                pt0::CoreTypeDesc::Package(self.map_package_type(pkg))
            }
            current::CoreTypeDesc::Ptyp_extension(ext) => {
                pt0::CoreTypeDesc::Extension(self.map_extension(ext))
            }
        }
    }

    fn map_package_type(&mut self, pkg: &current::PackageType) -> pt0::PackageType {
        let (lid, constraints) = pkg;
        (
            self.map_longident_loc(lid),
            constraints
                .iter()
                .map(|(lid, ty_idx)| (self.map_longident_loc(lid), self.map_core_type_idx(*ty_idx)))
                .collect(),
        )
    }

    fn map_row_field(&mut self, field: &current::RowField) -> pt0::RowField {
        match field {
            current::RowField::Rtag(label, attrs, b, types) => pt0::RowField::Rtag(
                self.map_label_loc(label),
                self.map_attributes(attrs),
                *b,
                types.iter().map(|t| self.map_core_type_idx(*t)).collect(),
            ),
            current::RowField::Rinherit(ty_idx) => {
                pt0::RowField::Rinherit(self.map_core_type_idx(*ty_idx))
            }
        }
    }

    fn map_object_field(&mut self, field: &current::ObjectField) -> pt0::ObjectField {
        match field {
            current::ObjectField::Otag(label, attrs, ty_idx) => pt0::ObjectField::Otag(
                self.map_string_loc(label),
                self.map_attributes(attrs),
                self.map_core_type_idx(*ty_idx),
            ),
            current::ObjectField::Oinherit(ty_idx) => {
                pt0::ObjectField::Oinherit(self.map_core_type_idx(*ty_idx))
            }
        }
    }

    fn map_extension(&mut self, ext: &current::Extension) -> pt0::Extension {
        let (name, payload) = ext;
        (self.map_string_loc(name), self.map_payload(payload))
    }

    // ========== Patterns ==========

    pub fn map_pattern(&mut self, pat: &current::Pattern) -> pt0::Pattern {
        pt0::Pattern {
            ppat_desc: self.map_pattern_desc(&*pat.ppat_desc),
            ppat_loc: self.loc(pat.ppat_loc),
            ppat_attributes: self.map_attributes(&pat.ppat_attributes),
        }
    }

    fn map_pattern_desc(&mut self, desc: &current::PatternDesc) -> pt0::PatternDesc {
        match desc {
            current::PatternDesc::Ppat_any => pt0::PatternDesc::Any,
            current::PatternDesc::Ppat_var(s) => pt0::PatternDesc::Var(self.map_string_loc(s)),
            current::PatternDesc::Ppat_alias(pat_idx, s) => pt0::PatternDesc::Alias(
                Box::new(self.map_pat_idx(*pat_idx)),
                self.map_string_loc(s),
            ),
            current::PatternDesc::Ppat_constant(c) => {
                pt0::PatternDesc::Constant(self.map_constant(c))
            }
            current::PatternDesc::Ppat_interval(inner) => {
                let (ref c1, ref c2) = **inner;
                pt0::PatternDesc::Interval(self.map_constant(c1), self.map_constant(c2))
            }
            current::PatternDesc::Ppat_tuple(pats) => {
                pt0::PatternDesc::Tuple(pats.iter().map(|p| self.map_pat_idx(*p)).collect())
            }
            current::PatternDesc::Ppat_construct(lid, opt) => pt0::PatternDesc::Construct(
                self.map_longident_loc(lid),
                opt.as_ref().map(|p| Box::new(self.map_pat_idx(*p))),
            ),
            current::PatternDesc::Ppat_variant(inner) => {
                let (ref label, ref opt) = **inner;
                pt0::PatternDesc::Variant(
                    label.to_string(),
                    opt.as_ref().map(|p| Box::new(self.map_pat_idx(*p))),
                )
            }
            current::PatternDesc::Ppat_record(inner) => {
                let (ref fields, ref flag) = **inner;
                // Use RecordElement with 3 fields (lid, x, opt) for current parsetree format
                pt0::PatternDesc::Record(
                    fields
                        .iter()
                        .map(|f| pt0::RecordElement {
                            lid: self.map_longident_loc(&f.lid),
                            x: self.map_pat_idx(f.pat),
                            opt: f.opt,
                        })
                        .collect(),
                    self.map_closed_flag(*flag),
                )
            }
            current::PatternDesc::Ppat_array(pats) => {
                pt0::PatternDesc::Array(pats.iter().map(|p| self.map_pat_idx(*p)).collect())
            }
            current::PatternDesc::Ppat_or(p1, p2) => pt0::PatternDesc::Or(
                Box::new(self.map_pat_idx(*p1)),
                Box::new(self.map_pat_idx(*p2)),
            ),
            current::PatternDesc::Ppat_constraint(inner) => {
                let (ref pat_idx, ref ty_idx) = **inner;
                pt0::PatternDesc::Constraint(
                    Box::new(self.map_pat_idx(*pat_idx)),
                    Box::new(self.map_core_type_idx(*ty_idx)),
                )
            }
            current::PatternDesc::Ppat_type(lid) => {
                pt0::PatternDesc::Type(self.map_longident_loc(lid))
            }
            current::PatternDesc::Ppat_unpack(s) => {
                pt0::PatternDesc::Unpack(self.map_string_loc(s))
            }
            current::PatternDesc::Ppat_exception(pat_idx) => {
                pt0::PatternDesc::Exception(Box::new(self.map_pat_idx(*pat_idx)))
            }
            current::PatternDesc::Ppat_extension(ext) => {
                pt0::PatternDesc::Extension(self.map_extension(ext))
            }
            current::PatternDesc::Ppat_open(lid, pat_idx) => pt0::PatternDesc::Open(
                self.map_longident_loc(lid),
                Box::new(self.map_pat_idx(*pat_idx)),
            ),
        }
    }

    // ========== Expressions ==========

    pub fn map_expression(&mut self, expr: &current::Expression) -> pt0::Expression {
        self.map_expression_with_owner(expr, None)
    }

    fn map_expression_with_owner(
        &mut self,
        expr: &current::Expression,
        owner_idx: Option<ExprIdx>,
    ) -> pt0::Expression {
        if let current::ExpressionDesc::Pexp_await(inner_idx) = &*expr.pexp_desc {
            let mut inner = self.map_expr_idx(*inner_idx);
            inner.pexp_attributes.insert(0, self.mk_await_attr());
            return inner;
        }

        // Check if this is a JSX element that needs the [@JSX] attribute
        let is_jsx = matches!(
            &*expr.pexp_desc,
            current::ExpressionDesc::Pexp_jsx_element(_)
                | current::ExpressionDesc::Pexp_inline_for(_)
        );
        let mut attrs = self.map_attributes(&expr.pexp_attributes);
        if is_jsx {
            attrs.insert(0, self.mk_jsx_attr(expr.pexp_loc));
        }
        // Upstream #7887: for-of / for-await-of are encoded in parsetree0 as
        // a regular `for` loop carrying an `_res.for_of` / `_res.for_await_of`
        // attribute whose payload is the iterable (PPat (Pat.any (), Some
        // iterable)). Mirrors `compiler/ml/ast_mapper_to0.ml` after the PR.
        match &*expr.pexp_desc {
            current::ExpressionDesc::Pexp_for_of(inner) => {
                let (_pat, iterable_idx, _body) = inner.as_ref();
                let attr = self.mk_for_of_attr("_res.for_of", expr.pexp_loc, *iterable_idx);
                attrs.insert(0, attr);
            }
            current::ExpressionDesc::Pexp_for_await_of(inner) => {
                let (_pat, iterable_idx, _body) = inner.as_ref();
                let attr = self.mk_for_of_attr("_res.for_await_of", expr.pexp_loc, *iterable_idx);
                attrs.insert(0, attr);
            }
            _ => {}
        }
        pt0::Expression {
            pexp_desc: self.map_expression_desc(&*expr.pexp_desc, expr.pexp_loc, owner_idx),
            pexp_loc: self.loc(expr.pexp_loc),
            pexp_attributes: attrs,
        }
    }

    /// Build the `_res.for_of` / `_res.for_await_of` attribute used to encode
    /// `for ... of` / `for await ... of` in the legacy parsetree0 format.
    fn mk_for_of_attr(
        &mut self,
        name: &str,
        loc_idx: LocIdx,
        iterable_idx: ExprIdx,
    ) -> pt0::Attribute {
        let loc = self.loc(loc_idx);
        let pat_any = pt0::Pattern {
            ppat_desc: pt0::PatternDesc::Any,
            ppat_loc: loc.clone(),
            ppat_attributes: vec![],
        };
        let iterable = self.map_expr_idx(iterable_idx);
        let payload = pt0::Payload::PPat(Box::new(pat_any), Some(Box::new(iterable)));
        (OldLocated::new(name.to_string(), loc), payload)
    }

    fn map_expression_desc(
        &mut self,
        desc: &current::ExpressionDesc,
        loc: LocIdx,
        owner_idx: Option<ExprIdx>,
    ) -> pt0::ExpressionDesc {
        match desc {
            current::ExpressionDesc::Pexp_ident(lid) => {
                pt0::ExpressionDesc::Ident(self.map_longident_loc(lid))
            }
            current::ExpressionDesc::Pexp_constant(c) => {
                pt0::ExpressionDesc::Constant(self.map_constant(c))
            }
            current::ExpressionDesc::Pexp_let(inner) => {
                let (ref flag, ref bindings, ref body_idx) = **inner;
                pt0::ExpressionDesc::Let(
                    self.map_rec_flag(*flag),
                    bindings
                        .iter()
                        .map(|vb| self.map_value_binding(vb))
                        .collect(),
                    Box::new(self.map_expr_idx(*body_idx)),
                )
            }
            current::ExpressionDesc::Pexp_fun(inner) => {
                let PexpFun {
                    arg_label,
                    default,
                    lhs,
                    rhs,
                    arity,
                    is_async,
                } = &**inner;
                // Output current parsetree format with arity and is_async fields
                // Look up arity from arena (current::Arity is now ArityIdx)
                let arity_opt = self.arena.get_arity(*arity);
                let default_idx = owner_idx
                    .and_then(|owner| self.arena.fun_default(owner))
                    .or(*default);
                pt0::ExpressionDesc::Fun {
                    arg_label: self.map_arg_label(&arg_label),
                    default: default_idx.map(|e| Box::new(self.map_expr_idx(e))),
                    lhs: Box::new(self.map_pat_idx(*lhs)),
                    rhs: Box::new(self.map_expr_idx(*rhs)),
                    arity: arity_opt,
                    is_async: *is_async,
                }
            }
            current::ExpressionDesc::Pexp_apply(inner) => {
                let PexpApply {
                    funct: funct_idx,
                    args,
                    partial,
                    transformed_jsx,
                } = &**inner;
                // Look up the function expression from arena
                let funct = self.arena.get_expr(*funct_idx).clone();
                // Convert operators for parsetree0 compatibility
                // Check if this is a binary operator application that needs conversion
                let converted_funct = if args.len() == 2
                    && matches!(&args[0].0, current::ArgLabel::Nolabel)
                    && matches!(&args[1].0, current::ArgLabel::Nolabel)
                {
                    if let current::ExpressionDesc::Pexp_ident(lid) = &*funct.pexp_desc {
                        // Get the StrIdx first to avoid borrow conflicts
                        let op_idx = if let Longident::Lident(op) = self.get_longident(lid.txt) {
                            Some(*op)
                        } else {
                            None
                        };
                        if let Some(op) = op_idx {
                            let op_str = self.get_str(op);
                            match op_str {
                                "->" => Some("|."),
                                "++" => Some("^"),
                                "!=" => Some("<>"),
                                "!==" => Some("!="),
                                "===" => Some("=="),
                                "==" => Some("="),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                let mapped_funct = if let Some(new_name) = converted_funct {
                    if let current::ExpressionDesc::Pexp_ident(lid) = &*funct.pexp_desc {
                        let full_loc = self.loc(lid.loc);
                        let new_name_idx = self.intern(new_name);
                        pt0::Expression {
                            pexp_desc: pt0::ExpressionDesc::Ident(OldLocated::new(
                                Longident::Lident(new_name_idx),
                                full_loc,
                            )),
                            pexp_loc: self.loc(funct.pexp_loc),
                            pexp_attributes: self.map_attributes(&funct.pexp_attributes),
                        }
                    } else {
                        self.map_expression_with_owner(&funct, Some(*funct_idx))
                    }
                } else {
                    self.map_expression_with_owner(&funct, Some(*funct_idx))
                };

                let mut mapped_args = Vec::with_capacity(args.len());
                for (label, e_idx) in args {
                    mapped_args.push((self.map_arg_label(&label), self.map_expr_idx(*e_idx)));
                }

                pt0::ExpressionDesc::Apply {
                    funct: Box::new(mapped_funct),
                    args: mapped_args,
                    partial: *partial,
                    transformed_jsx: *transformed_jsx,
                }
            }
            current::ExpressionDesc::Pexp_match(inner) => {
                let (ref e_idx, ref cases) = **inner;
                pt0::ExpressionDesc::Match(
                    Box::new(self.map_expr_idx(*e_idx)),
                    cases
                        .iter()
                        .enumerate()
                        .map(|(case_index, c)| self.map_case(c, owner_idx, case_index))
                        .collect(),
                )
            }
            current::ExpressionDesc::Pexp_try(inner) => {
                let (ref e_idx, ref cases) = **inner;
                pt0::ExpressionDesc::Try(
                    Box::new(self.map_expr_idx(*e_idx)),
                    cases
                        .iter()
                        .enumerate()
                        .map(|(case_index, c)| self.map_case(c, owner_idx, case_index))
                        .collect(),
                )
            }
            current::ExpressionDesc::Pexp_tuple(exprs) => {
                pt0::ExpressionDesc::Tuple(exprs.iter().map(|e| self.map_expr_idx(*e)).collect())
            }
            current::ExpressionDesc::Pexp_construct(lid, opt) => {
                let arg_idx = owner_idx
                    .and_then(|owner| self.arena.construct_arg(owner))
                    .or(*opt);
                pt0::ExpressionDesc::Construct(
                    self.map_longident_loc(lid),
                    arg_idx.map(|e| Box::new(self.map_expr_idx(e))),
                )
            }
            current::ExpressionDesc::Pexp_variant(inner) => {
                let (ref label, ref opt) = **inner;
                let arg_idx = owner_idx
                    .and_then(|owner| self.arena.variant_arg(owner))
                    .or(*opt);
                pt0::ExpressionDesc::Variant(
                    label.to_string(),
                    arg_idx.map(|e| Box::new(self.map_expr_idx(e))),
                )
            }
            current::ExpressionDesc::Pexp_record(inner) => {
                let (ref fields, ref spread) = **inner;
                let spread_idx = owner_idx
                    .and_then(|owner| self.arena.record_spread(owner))
                    .or(*spread);
                // Use RecordElement with 3 fields (lid, x, opt) for current parsetree format
                pt0::ExpressionDesc::Record(
                    fields
                        .iter()
                        .map(|f| pt0::RecordElement {
                            lid: self.map_longident_loc(&f.lid),
                            x: self.map_expr_idx(f.expr),
                            opt: f.opt,
                        })
                        .collect(),
                    spread_idx.map(|e| Box::new(self.map_expr_idx(e))),
                )
            }
            current::ExpressionDesc::Pexp_field(e_idx, lid) => pt0::ExpressionDesc::Field(
                Box::new(self.map_expr_idx(*e_idx)),
                self.map_longident_loc(lid),
            ),
            current::ExpressionDesc::Pexp_setfield(inner) => {
                let (ref e1_idx, ref lid, ref e2_idx) = **inner;
                pt0::ExpressionDesc::Setfield(
                    Box::new(self.map_expr_idx(*e1_idx)),
                    self.map_longident_loc(lid),
                    Box::new(self.map_expr_idx(*e2_idx)),
                )
            }
            current::ExpressionDesc::Pexp_array(exprs) => {
                pt0::ExpressionDesc::Array(exprs.iter().map(|e| self.map_expr_idx(*e)).collect())
            }
            current::ExpressionDesc::Pexp_ifthenelse(inner) => {
                let (ref e1_idx, ref e2_idx, ref e3) = **inner;
                let else_idx = owner_idx
                    .and_then(|owner| self.arena.if_else_branch(owner))
                    .or(*e3);
                pt0::ExpressionDesc::Ifthenelse(
                    Box::new(self.map_expr_idx(*e1_idx)),
                    Box::new(self.map_expr_idx(*e2_idx)),
                    else_idx.map(|e| Box::new(self.map_expr_idx(e))),
                )
            }
            current::ExpressionDesc::Pexp_sequence(e1_idx, e2_idx) => {
                pt0::ExpressionDesc::Sequence(
                    Box::new(self.map_expr_idx(*e1_idx)),
                    Box::new(self.map_expr_idx(*e2_idx)),
                )
            }
            current::ExpressionDesc::Pexp_break => {
                let full_loc = self.loc(loc);
                pt0::ExpressionDesc::Extension((
                    OldLocated::new("res.break".to_string(), full_loc),
                    pt0::Payload::PStr(vec![]),
                ))
            }
            current::ExpressionDesc::Pexp_continue => {
                let full_loc = self.loc(loc);
                pt0::ExpressionDesc::Extension((
                    OldLocated::new("res.continue".to_string(), full_loc),
                    pt0::Payload::PStr(vec![]),
                ))
            }
            current::ExpressionDesc::Pexp_while(e1_idx, e2_idx) => pt0::ExpressionDesc::While(
                Box::new(self.map_expr_idx(*e1_idx)),
                Box::new(self.map_expr_idx(*e2_idx)),
            ),
            current::ExpressionDesc::Pexp_for(inner) => {
                let (ref pat_idx, ref e1_idx, ref e2_idx, ref flag, ref e3_idx) = **inner;
                pt0::ExpressionDesc::For(
                    Box::new(self.map_pat_idx(*pat_idx)),
                    Box::new(self.map_expr_idx(*e1_idx)),
                    Box::new(self.map_expr_idx(*e2_idx)),
                    self.map_direction_flag(*flag),
                    Box::new(self.map_expr_idx(*e3_idx)),
                )
            }
            // Upstream #7887: encode for-of / for-await-of as a regular `for`
            // loop with dummy 0..0 bounds — the iterable is carried by the
            // `_res.for_of` / `_res.for_await_of` attribute attached to the
            // outer expression in `map_expression_with_owner`.
            current::ExpressionDesc::Pexp_for_of(inner)
            | current::ExpressionDesc::Pexp_for_await_of(inner) => {
                let (pat_idx, _iterable_idx, body_idx) = inner.as_ref();
                let dummy_loc = self.loc(loc);
                let dummy_int = || pt0::Expression {
                    pexp_desc: pt0::ExpressionDesc::Constant(pt0::Constant::Integer(
                        "0".to_string(),
                        None,
                    )),
                    pexp_loc: dummy_loc.clone(),
                    pexp_attributes: vec![],
                };
                pt0::ExpressionDesc::For(
                    Box::new(self.map_pat_idx(*pat_idx)),
                    Box::new(dummy_int()),
                    Box::new(dummy_int()),
                    pt0::DirectionFlag::Upto,
                    Box::new(self.map_expr_idx(*body_idx)),
                )
            }
            current::ExpressionDesc::Pexp_constraint(inner) => {
                let (ref e_idx, ref ty_idx) = **inner;
                pt0::ExpressionDesc::Constraint(
                    Box::new(self.map_expr_idx(*e_idx)),
                    Box::new(self.map_core_type_idx(*ty_idx)),
                )
            }
            current::ExpressionDesc::Pexp_coerce(inner) => {
                let (ref e_idx, _, ref ty_idx) = **inner;
                let _from_type = owner_idx.and_then(|owner| self.arena.coerce_from_type(owner));
                // parsetree0 has unit instead of Option<CoreType> for the middle arg
                pt0::ExpressionDesc::Coerce(
                    Box::new(self.map_expr_idx(*e_idx)),
                    (),
                    Box::new(self.map_core_type_idx(*ty_idx)),
                )
            }
            current::ExpressionDesc::Pexp_send(inner) => {
                let (ref e_idx, ref label) = **inner;
                pt0::ExpressionDesc::Send(
                    Box::new(self.map_expr_idx(*e_idx)),
                    self.map_label_loc(label),
                )
            }
            current::ExpressionDesc::Pexp_letmodule(inner) => {
                let (ref name, ref me_idx, ref body_idx) = **inner;
                pt0::ExpressionDesc::Letmodule(
                    self.map_string_loc(name),
                    Box::new(self.map_mod_expr_idx(*me_idx)),
                    Box::new(self.map_expr_idx(*body_idx)),
                )
            }
            current::ExpressionDesc::Pexp_letexception(inner) => {
                let (ref ext, ref body_idx) = **inner;
                pt0::ExpressionDesc::Letexception(
                    self.map_extension_constructor(ext),
                    Box::new(self.map_expr_idx(*body_idx)),
                )
            }
            current::ExpressionDesc::Pexp_assert(e_idx) => {
                pt0::ExpressionDesc::Assert(Box::new(self.map_expr_idx(*e_idx)))
            }
            current::ExpressionDesc::Pexp_newtype(inner) => {
                let (ref name, ref body_idx) = **inner;
                pt0::ExpressionDesc::Newtype(
                    self.map_string_loc(name),
                    Box::new(self.map_expr_idx(*body_idx)),
                )
            }
            current::ExpressionDesc::Pexp_pack(me_idx) => {
                pt0::ExpressionDesc::Pack(Box::new(self.map_mod_expr_idx(*me_idx)))
            }
            current::ExpressionDesc::Pexp_open(inner) => {
                let (ref flag, ref lid, ref body_idx) = **inner;
                pt0::ExpressionDesc::Open(
                    self.map_override_flag(*flag),
                    self.map_longident_loc(lid),
                    Box::new(self.map_expr_idx(*body_idx)),
                )
            }
            current::ExpressionDesc::Pexp_extension(ext) => {
                pt0::ExpressionDesc::Extension(self.map_extension(ext))
            }
            current::ExpressionDesc::Pexp_await(e_idx) => {
                // The complete inner expression receives [@res.await] in
                // map_expression_with_owner, matching OCaml's mapper.
                self.map_expr_idx(*e_idx).pexp_desc
            }
            current::ExpressionDesc::Pexp_jsx_element(jsx) => {
                // Convert JSX element to old-style function application with [@JSX] attribute
                let _full_loc = self.loc(loc);
                match &**jsx {
                    current::JsxElement::Fragment(fragment) => {
                        // Fragment becomes a list with JSX attribute
                        let list_expr = self.map_jsx_children_to_list(&fragment.children, loc);
                        // The JSX attribute will be added by the caller
                        list_expr.pexp_desc
                    }
                    current::JsxElement::Unary(unary) => {
                        // Unary element: <Tag props /> -> Tag(~props, ~children=[], ())
                        let tag_ident = self.jsx_tag_to_longident(&unary.tag_name.txt);
                        let tag_loc = self.loc(unary.tag_name.loc);
                        let mapped_props = self.map_jsx_props(&unary.props, loc);
                        let children_expr = self.mk_nil_expr(loc);
                        let unit_expr = self.mk_unit_expr(loc);
                        let children_idx = self.intern("children");

                        let mut args = mapped_props;
                        args.push((pt0::ArgLabel::Labelled(children_idx), children_expr));
                        args.push((pt0::ArgLabel::Nolabel, unit_expr));

                        pt0::ExpressionDesc::Apply {
                            funct: Box::new(pt0::Expression {
                                pexp_desc: pt0::ExpressionDesc::Ident(OldLocated::new(
                                    tag_ident,
                                    tag_loc.clone(),
                                )),
                                pexp_loc: tag_loc,
                                pexp_attributes: vec![],
                            }),
                            args,
                            partial: false,
                            transformed_jsx: false,
                        }
                    }
                    current::JsxElement::Container(container) => {
                        // Container element: <Tag props>children</Tag> -> Tag(~props, ~children=list{...}, ())
                        let tag_ident = self.jsx_tag_to_longident(&container.tag_name_start.txt);
                        let tag_loc = self.loc(container.tag_name_start.loc);
                        let mapped_props = self.map_jsx_props(&container.props, loc);
                        let children_expr = self.map_jsx_children_to_list(&container.children, loc);
                        let unit_expr = self.mk_unit_expr(loc);
                        let children_idx = self.intern("children");

                        let mut args = mapped_props;
                        args.push((pt0::ArgLabel::Labelled(children_idx), children_expr));
                        args.push((pt0::ArgLabel::Nolabel, unit_expr));

                        pt0::ExpressionDesc::Apply {
                            funct: Box::new(pt0::Expression {
                                pexp_desc: pt0::ExpressionDesc::Ident(OldLocated::new(
                                    tag_ident,
                                    tag_loc.clone(),
                                )),
                                pexp_loc: tag_loc,
                                pexp_attributes: vec![],
                            }),
                            args,
                            partial: false,
                            transformed_jsx: false,
                        }
                    }
                }
            }
            current::ExpressionDesc::Pexp_inline_for(_)
            | current::ExpressionDesc::Pexp_comptime_typeinfo(_)
            | current::ExpressionDesc::Pexp_comptime_field(_)
            | current::ExpressionDesc::Pexp_comptime_compile_error(_)
            | current::ExpressionDesc::Pexp_comptime_typename(_)
            | current::ExpressionDesc::Pexp_comptime_record(_)
            | current::ExpressionDesc::Pexp_comptime_variant(_)
            | current::ExpressionDesc::Pexp_comptime_build_variant(_)
            | current::ExpressionDesc::Pexp_comptime_variant_case(_)
            | current::ExpressionDesc::Pexp_comptime_build_record(_)
            | current::ExpressionDesc::Pexp_comptime_record_field(_) => {
                unreachable!("comptime builtins eliminated before mapping to pt0")
            }
        }
    }

    fn map_case(
        &mut self,
        case: &current::Case,
        owner_idx: Option<ExprIdx>,
        case_index: usize,
    ) -> pt0::Case {
        let guard = owner_idx
            .and_then(|owner| self.arena.case_guard(owner, case_index))
            .or(case.pc_guard);
        pt0::Case {
            pc_lhs: self.map_pat_idx(case.pc_lhs),
            pc_guard: guard.map(|e| self.map_expr_idx(e)),
            pc_rhs: self.map_expr_idx(case.pc_rhs),
        }
    }

    fn map_value_binding(&mut self, vb: &current::ValueBinding) -> pt0::ValueBinding {
        pt0::ValueBinding {
            pvb_pat: self.map_pat_idx(vb.pvb_pat),
            pvb_expr: self.map_expr_idx(vb.pvb_expr),
            pvb_attributes: self.map_attributes(&vb.pvb_attributes),
            pvb_loc: self.loc(vb.pvb_loc),
        }
    }

    // ========== Type declarations ==========

    fn map_type_declaration(&mut self, td: &current::TypeDeclaration) -> pt0::TypeDeclaration {
        pt0::TypeDeclaration {
            ptype_name: self.map_string_loc(&td.ptype_name),
            ptype_params: td
                .ptype_params
                .iter()
                .map(|(ty_idx, var)| (self.map_core_type_idx(*ty_idx), self.map_variance(*var)))
                .collect(),
            ptype_cstrs: td
                .ptype_cstrs
                .iter()
                .map(|(ty1_idx, ty2_idx, loc)| {
                    (
                        self.map_core_type_idx(*ty1_idx),
                        self.map_core_type_idx(*ty2_idx),
                        self.loc(*loc),
                    )
                })
                .collect(),
            ptype_kind: self.map_type_kind(&td.ptype_kind),
            ptype_private: self.map_private_flag(td.ptype_private),
            ptype_manifest: td.ptype_manifest.map(|t| self.map_core_type_idx(t)),
            ptype_attributes: self.map_attributes(&td.ptype_attributes),
            ptype_loc: self.loc(td.ptype_loc),
        }
    }

    fn map_type_kind(&mut self, kind: &current::TypeKind) -> pt0::TypeKind {
        match kind {
            current::TypeKind::Ptype_abstract => pt0::TypeKind::Abstract,
            current::TypeKind::Ptype_variant(ctors) => pt0::TypeKind::Variant(
                ctors
                    .iter()
                    .map(|c| self.map_constructor_declaration(c))
                    .collect(),
            ),
            current::TypeKind::Ptype_record(labels) => pt0::TypeKind::Record(
                labels
                    .iter()
                    .map(|l| self.map_label_declaration(l))
                    .collect(),
            ),
            current::TypeKind::Ptype_open => pt0::TypeKind::Open,
        }
    }

    fn map_label_declaration(&mut self, ld: &current::LabelDeclaration) -> pt0::LabelDeclaration {
        pt0::LabelDeclaration {
            pld_name: self.map_string_loc(&ld.pld_name),
            pld_mutable: self.map_mutable_flag(ld.pld_mutable),
            pld_type: self.map_core_type_idx(ld.pld_type),
            pld_loc: self.loc(ld.pld_loc),
            pld_attributes: self.map_attributes(&ld.pld_attributes),
        }
    }

    fn map_constructor_declaration(
        &mut self,
        cd: &current::ConstructorDeclaration,
    ) -> pt0::ConstructorDeclaration {
        pt0::ConstructorDeclaration {
            pcd_name: self.map_string_loc(&cd.pcd_name),
            pcd_args: self.map_constructor_arguments(&cd.pcd_args),
            pcd_res: cd.pcd_res.map(|t| self.map_core_type_idx(t)),
            pcd_loc: self.loc(cd.pcd_loc),
            pcd_attributes: self.map_attributes(&cd.pcd_attributes),
        }
    }

    fn map_constructor_arguments(
        &mut self,
        args: &current::ConstructorArguments,
    ) -> pt0::ConstructorArguments {
        match args {
            current::ConstructorArguments::Pcstr_tuple(types) => pt0::ConstructorArguments::Tuple(
                types.iter().map(|t| self.map_core_type_idx(*t)).collect(),
            ),
            current::ConstructorArguments::Pcstr_record(labels) => {
                pt0::ConstructorArguments::Record(
                    labels
                        .iter()
                        .map(|l| self.map_label_declaration(l))
                        .collect(),
                )
            }
        }
    }

    fn map_extension_constructor(
        &mut self,
        ec: &current::ExtensionConstructor,
    ) -> pt0::ExtensionConstructor {
        pt0::ExtensionConstructor {
            pext_name: self.map_string_loc(&ec.pext_name),
            pext_kind: self.map_extension_constructor_kind(&ec.pext_kind),
            pext_loc: self.loc(ec.pext_loc),
            pext_attributes: self.map_attributes(&ec.pext_attributes),
        }
    }

    fn map_extension_constructor_kind(
        &mut self,
        kind: &current::ExtensionConstructorKind,
    ) -> pt0::ExtensionConstructorKind {
        match kind {
            current::ExtensionConstructorKind::Pext_decl(args, res) => {
                pt0::ExtensionConstructorKind::Decl(
                    self.map_constructor_arguments(args),
                    res.map(|t| self.map_core_type_idx(t)),
                )
            }
            current::ExtensionConstructorKind::Pext_rebind(lid) => {
                pt0::ExtensionConstructorKind::Rebind(self.map_longident_loc(lid))
            }
        }
    }

    fn map_type_extension(&mut self, te: &current::TypeExtension) -> pt0::TypeExtension {
        pt0::TypeExtension {
            ptyext_path: self.map_longident_loc(&te.ptyext_path),
            ptyext_params: te
                .ptyext_params
                .iter()
                .map(|(ty_idx, var)| (self.map_core_type_idx(*ty_idx), self.map_variance(*var)))
                .collect(),
            ptyext_constructors: te
                .ptyext_constructors
                .iter()
                .map(|ec| self.map_extension_constructor(ec))
                .collect(),
            ptyext_private: self.map_private_flag(te.ptyext_private),
            ptyext_attributes: self.map_attributes(&te.ptyext_attributes),
        }
    }

    // ========== Module types ==========

    fn map_module_type(&mut self, mt: &current::ModuleType) -> pt0::ModuleType {
        pt0::ModuleType {
            pmty_desc: self.map_module_type_desc(&*mt.pmty_desc),
            pmty_loc: self.loc(mt.pmty_loc),
            pmty_attributes: self.map_attributes(&mt.pmty_attributes),
        }
    }

    fn map_module_type_desc(&mut self, desc: &current::ModuleTypeDesc) -> pt0::ModuleTypeDesc {
        match desc {
            current::ModuleTypeDesc::Pmty_ident(lid) => {
                pt0::ModuleTypeDesc::Ident(self.map_longident_loc(lid))
            }
            current::ModuleTypeDesc::Pmty_signature(items) => pt0::ModuleTypeDesc::Signature(
                items.iter().map(|i| self.map_signature_item(i)).collect(),
            ),
            current::ModuleTypeDesc::Pmty_functor(inner) => {
                let (ref name, ref mty_idx, ref body_idx) = **inner;
                pt0::ModuleTypeDesc::Functor(
                    self.map_string_loc(name),
                    mty_idx
                        .as_ref()
                        .map(|m| Box::new(self.map_mod_type_idx(*m))),
                    Box::new(self.map_mod_type_idx(*body_idx)),
                )
            }
            current::ModuleTypeDesc::Pmty_with(inner) => {
                let (ref mty_idx, ref constraints) = **inner;
                pt0::ModuleTypeDesc::With(
                    Box::new(self.map_mod_type_idx(*mty_idx)),
                    constraints
                        .iter()
                        .map(|wc| self.map_with_constraint(wc))
                        .collect(),
                )
            }
            current::ModuleTypeDesc::Pmty_typeof(me_idx) => {
                pt0::ModuleTypeDesc::Typeof(Box::new(self.map_mod_expr_idx(*me_idx)))
            }
            current::ModuleTypeDesc::Pmty_extension(ext) => {
                pt0::ModuleTypeDesc::Extension(self.map_extension(ext))
            }
            current::ModuleTypeDesc::Pmty_alias(lid) => {
                pt0::ModuleTypeDesc::Alias(self.map_longident_loc(lid))
            }
        }
    }

    fn map_with_constraint(&mut self, wc: &current::WithConstraint) -> pt0::WithConstraint {
        match wc {
            current::WithConstraint::Pwith_type(lid, td) => pt0::WithConstraint::Type(
                self.map_longident_loc(lid),
                self.map_type_declaration(td),
            ),
            current::WithConstraint::Pwith_module(lid1, lid2) => pt0::WithConstraint::Module(
                self.map_longident_loc(lid1),
                self.map_longident_loc(lid2),
            ),
            current::WithConstraint::Pwith_typesubst(lid, td) => pt0::WithConstraint::TypeSubst(
                self.map_longident_loc(lid),
                self.map_type_declaration(td),
            ),
            current::WithConstraint::Pwith_modsubst(lid1, lid2) => pt0::WithConstraint::ModSubst(
                self.map_longident_loc(lid1),
                self.map_longident_loc(lid2),
            ),
        }
    }

    // ========== Module expressions ==========

    fn map_module_expr(&mut self, me: &current::ModuleExpr) -> pt0::ModuleExpr {
        pt0::ModuleExpr {
            pmod_desc: self.map_module_expr_desc(&*me.pmod_desc),
            pmod_loc: self.loc(me.pmod_loc),
            pmod_attributes: self.map_attributes(&me.pmod_attributes),
        }
    }

    fn map_module_expr_desc(&mut self, desc: &current::ModuleExprDesc) -> pt0::ModuleExprDesc {
        match desc {
            current::ModuleExprDesc::Pmod_ident(lid) => {
                pt0::ModuleExprDesc::Ident(self.map_longident_loc(lid))
            }
            current::ModuleExprDesc::Pmod_structure(items) => pt0::ModuleExprDesc::Structure(
                items.iter().map(|i| self.map_structure_item(i)).collect(),
            ),
            current::ModuleExprDesc::Pmod_functor(inner) => {
                let (ref name, ref mty_idx, ref body_idx) = **inner;
                pt0::ModuleExprDesc::Functor(
                    self.map_string_loc(name),
                    mty_idx
                        .as_ref()
                        .map(|m| Box::new(self.map_mod_type_idx(*m))),
                    Box::new(self.map_mod_expr_idx(*body_idx)),
                )
            }
            current::ModuleExprDesc::Pmod_apply(me1_idx, me2_idx) => pt0::ModuleExprDesc::Apply(
                Box::new(self.map_mod_expr_idx(*me1_idx)),
                Box::new(self.map_mod_expr_idx(*me2_idx)),
            ),
            current::ModuleExprDesc::Pmod_constraint(me_idx, mty_idx) => {
                pt0::ModuleExprDesc::Constraint(
                    Box::new(self.map_mod_expr_idx(*me_idx)),
                    Box::new(self.map_mod_type_idx(*mty_idx)),
                )
            }
            current::ModuleExprDesc::Pmod_unpack(e_idx) => {
                pt0::ModuleExprDesc::Unpack(Box::new(self.map_expr_idx(*e_idx)))
            }
            current::ModuleExprDesc::Pmod_extension(ext) => {
                pt0::ModuleExprDesc::Extension(self.map_extension(ext))
            }
        }
    }

    fn map_module_binding(&mut self, mb: &current::ModuleBinding) -> pt0::ModuleBinding {
        pt0::ModuleBinding {
            pmb_name: self.map_string_loc(&mb.pmb_name),
            pmb_expr: self.map_mod_expr_idx(mb.pmb_expr),
            pmb_attributes: self.map_attributes(&mb.pmb_attributes),
            pmb_loc: self.loc(mb.pmb_loc),
        }
    }

    fn map_module_declaration(
        &mut self,
        md: &current::ModuleDeclaration,
    ) -> pt0::ModuleDeclaration {
        pt0::ModuleDeclaration {
            pmd_name: self.map_string_loc(&md.pmd_name),
            pmd_type: self.map_mod_type_idx(md.pmd_type),
            pmd_attributes: self.map_attributes(&md.pmd_attributes),
            pmd_loc: self.loc(md.pmd_loc),
        }
    }

    fn map_module_type_declaration(
        &mut self,
        mtd: &current::ModuleTypeDeclaration,
    ) -> pt0::ModuleTypeDeclaration {
        pt0::ModuleTypeDeclaration {
            pmtd_name: self.map_string_loc(&mtd.pmtd_name),
            pmtd_type: mtd.pmtd_type.map(|mt| self.map_mod_type_idx(mt)),
            pmtd_attributes: self.map_attributes(&mtd.pmtd_attributes),
            pmtd_loc: self.loc(mtd.pmtd_loc),
        }
    }

    fn map_open_description(&mut self, od: &current::OpenDescription) -> pt0::OpenDescription {
        pt0::OpenDescription {
            popen_lid: self.map_longident_loc(&od.popen_lid),
            popen_override: self.map_override_flag(od.popen_override),
            popen_loc: self.loc(od.popen_loc),
            popen_attributes: self.map_attributes(&od.popen_attributes),
        }
    }

    fn map_include_declaration(
        &mut self,
        id: &current::IncludeDeclaration,
    ) -> pt0::IncludeDeclaration {
        pt0::IncludeInfos {
            pincl_mod: self.map_mod_expr_idx(id.pincl_mod),
            pincl_loc: self.loc(id.pincl_loc),
            pincl_attributes: self.map_attributes(&id.pincl_attributes),
        }
    }

    fn map_include_description(
        &mut self,
        id: &current::IncludeDescription,
    ) -> pt0::IncludeDescription {
        pt0::IncludeInfos {
            pincl_mod: self.map_mod_type_idx(id.pincl_mod),
            pincl_loc: self.loc(id.pincl_loc),
            pincl_attributes: self.map_attributes(&id.pincl_attributes),
        }
    }

    fn map_value_description(&mut self, vd: &current::ValueDescription) -> pt0::ValueDescription {
        pt0::ValueDescription {
            pval_name: self.map_string_loc(&vd.pval_name),
            pval_type: self.map_core_type_idx(vd.pval_type),
            pval_prim: vd
                .pval_prim
                .iter()
                .map(|idx| self.get_str(*idx).to_string())
                .collect(),
            pval_attributes: self.map_attributes(&vd.pval_attributes),
            pval_loc: self.loc(vd.pval_loc),
        }
    }

    // ========== Structure items ==========

    fn map_structure_item(&mut self, item: &current::StructureItem) -> pt0::StructureItem {
        pt0::StructureItem {
            pstr_desc: self.map_structure_item_desc(&*item.pstr_desc),
            pstr_loc: self.loc(item.pstr_loc),
        }
    }

    fn map_structure_item_desc(
        &mut self,
        desc: &current::StructureItemDesc,
    ) -> pt0::StructureItemDesc {
        match desc {
            current::StructureItemDesc::Pstr_eval(inner) => {
                let (ref e_idx, ref attrs) = **inner;
                pt0::StructureItemDesc::Eval(self.map_expr_idx(*e_idx), self.map_attributes(attrs))
            }
            current::StructureItemDesc::Pstr_value(inner) => {
                let (ref flag, ref bindings) = **inner;
                pt0::StructureItemDesc::Value(
                    self.map_rec_flag(*flag),
                    bindings
                        .iter()
                        .map(|vb| self.map_value_binding(vb))
                        .collect(),
                )
            }
            current::StructureItemDesc::Pstr_primitive(vd) => {
                pt0::StructureItemDesc::Primitive(self.map_value_description(vd))
            }
            current::StructureItemDesc::Pstr_type(inner) => {
                let (ref flag, ref decls) = **inner;
                pt0::StructureItemDesc::Type(
                    self.map_rec_flag(*flag),
                    decls
                        .iter()
                        .map(|td| self.map_type_declaration(td))
                        .collect(),
                )
            }
            current::StructureItemDesc::Pstr_typext(te) => {
                pt0::StructureItemDesc::Typext(self.map_type_extension(te))
            }
            current::StructureItemDesc::Pstr_exception(ec) => {
                pt0::StructureItemDesc::Exception(self.map_extension_constructor(ec))
            }
            current::StructureItemDesc::Pstr_module(mb) => {
                pt0::StructureItemDesc::Module(self.map_module_binding(mb))
            }
            current::StructureItemDesc::Pstr_recmodule(mbs) => pt0::StructureItemDesc::Recmodule(
                mbs.iter().map(|mb| self.map_module_binding(mb)).collect(),
            ),
            current::StructureItemDesc::Pstr_modtype(mtd) => {
                pt0::StructureItemDesc::Modtype(self.map_module_type_declaration(mtd))
            }
            current::StructureItemDesc::Pstr_open(od) => {
                pt0::StructureItemDesc::Open(self.map_open_description(od))
            }
            current::StructureItemDesc::Pstr_include(ii) => {
                pt0::StructureItemDesc::Include(self.map_include_declaration(ii))
            }
            current::StructureItemDesc::Pstr_attribute(attr) => {
                pt0::StructureItemDesc::Attribute(self.map_attribute(attr))
            }
            current::StructureItemDesc::Pstr_extension(inner) => {
                let (ref ext, ref attrs) = **inner;
                pt0::StructureItemDesc::Extension(
                    self.map_extension(ext),
                    self.map_attributes(attrs),
                )
            }
        }
    }

    // ========== Signature items ==========

    fn map_signature_item(&mut self, item: &current::SignatureItem) -> pt0::SignatureItem {
        pt0::SignatureItem {
            psig_desc: self.map_signature_item_desc(&*item.psig_desc),
            psig_loc: self.loc(item.psig_loc),
        }
    }

    fn map_signature_item_desc(
        &mut self,
        desc: &current::SignatureItemDesc,
    ) -> pt0::SignatureItemDesc {
        match desc {
            current::SignatureItemDesc::Psig_value(vd) => {
                pt0::SignatureItemDesc::Value(self.map_value_description(vd))
            }
            current::SignatureItemDesc::Psig_type(inner) => {
                let (ref flag, ref decls) = **inner;
                pt0::SignatureItemDesc::Type(
                    self.map_rec_flag(*flag),
                    decls
                        .iter()
                        .map(|td| self.map_type_declaration(td))
                        .collect(),
                )
            }
            current::SignatureItemDesc::Psig_typext(te) => {
                pt0::SignatureItemDesc::Typext(self.map_type_extension(te))
            }
            current::SignatureItemDesc::Psig_exception(ec) => {
                pt0::SignatureItemDesc::Exception(self.map_extension_constructor(ec))
            }
            current::SignatureItemDesc::Psig_module(md) => {
                pt0::SignatureItemDesc::Module(self.map_module_declaration(md))
            }
            current::SignatureItemDesc::Psig_recmodule(mds) => pt0::SignatureItemDesc::Recmodule(
                mds.iter()
                    .map(|md| self.map_module_declaration(md))
                    .collect(),
            ),
            current::SignatureItemDesc::Psig_modtype(mtd) => {
                pt0::SignatureItemDesc::Modtype(self.map_module_type_declaration(mtd))
            }
            current::SignatureItemDesc::Psig_open(od) => {
                pt0::SignatureItemDesc::Open(self.map_open_description(od))
            }
            current::SignatureItemDesc::Psig_include(ii) => {
                pt0::SignatureItemDesc::Include(self.map_include_description(ii))
            }
            current::SignatureItemDesc::Psig_attribute(attr) => {
                pt0::SignatureItemDesc::Attribute(self.map_attribute(attr))
            }
            current::SignatureItemDesc::Psig_extension(inner) => {
                let (ref ext, ref attrs) = **inner;
                pt0::SignatureItemDesc::Extension(
                    self.map_extension(ext),
                    self.map_attributes(attrs),
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_rec_flag() {
        let mut arena = ParseArena::new();
        let mut mapper = Mapper::new(&mut arena);
        assert!(matches!(
            mapper.map_rec_flag(current::RecFlag::Nonrecursive),
            pt0::RecFlag::Nonrecursive
        ));
        assert!(matches!(
            mapper.map_rec_flag(current::RecFlag::Recursive),
            pt0::RecFlag::Recursive
        ));
    }

    #[test]
    fn test_map_arg_label() {
        let mut arena = ParseArena::new();
        let x_idx = arena.intern("x");
        let y_idx = arena.intern("y");
        let mut mapper = Mapper::new(&mut arena);

        assert!(matches!(
            mapper.map_arg_label(&current::ArgLabel::Nolabel),
            pt0::ArgLabel::Nolabel
        ));

        let label = mapper.map_arg_label(&current::ArgLabel::Labelled(Located::mknoloc(x_idx)));
        if let pt0::ArgLabel::Labelled(idx) = label {
            assert_eq!(mapper.arena.get_string(idx), "x");
        } else {
            panic!("Expected Labelled");
        }

        let opt = mapper.map_arg_label(&current::ArgLabel::Optional(Located::mknoloc(y_idx)));
        if let pt0::ArgLabel::Optional(idx) = opt {
            assert_eq!(mapper.arena.get_string(idx), "y");
        } else {
            panic!("Expected Optional");
        }
    }

    #[test]
    fn test_map_constant() {
        use std::borrow::Cow;
        let mut arena = ParseArena::new();
        let mut mapper = Mapper::new(&mut arena);

        let c1 = mapper.map_constant(&current::Constant::Integer(Cow::Borrowed("42"), None));
        assert!(matches!(c1, pt0::Constant::Integer(s, None) if s == "42"));

        let c2 = mapper.map_constant(&current::Constant::Char(65));
        assert!(matches!(c2, pt0::Constant::Char(65)));

        // Note: None delimiter is mapped to Some("js") for OCaml parsetree0 parity
        let c3 = mapper.map_constant(&current::Constant::String(Cow::Borrowed("hello"), None));
        assert!(matches!(c3, pt0::Constant::String(s, Some(d)) if s == "hello" && d == "js"));
    }
}
