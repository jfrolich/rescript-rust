//! Sexp printer for Typedtree - used for parity testing between OCaml and Rust compilers

use crate::ident::Ident;
use crate::location::Location;
use crate::parse_arena::{LocIdx, ParseArena, LidentIdx, Located as Loc};
use crate::parser::ast::{ArgLabel, Arity, Attribute, ClosedFlag, DirectionFlag, MutableFlag, OverrideFlag, Payload, PrivateFlag, RecFlag};
use crate::parser::longident::Longident;
use crate::types::asttypes::ArgLabel as TypeArgLabel;
use crate::types::context::TypeContext;
use crate::types::path::Path;
use crate::types::type_expr::{FieldKind, RowDesc, RowField, TypeDesc, TypeExprRef};
use crate::types::typedtree::{
    Case, Constant, Expression, ExpressionDesc, ExtensionConstructor,
    ExtensionConstructorKind, FunctionParam, FunctionParamPattern, IncludeDeclaration, ModuleBinding, ModuleExpr, ModuleExprDesc,
    ModuleTypeConstraint, ModuleTypeDeclaration, OpenDeclaration, Partial, Pattern, PatternDesc,
    RecordLabelDefinition, Structure, StructureItem, StructureItemDesc,
    TypedCoreType, TypedCoreTypeDesc, ValueBinding, TypeExtension,
    TypedTypeDeclaration, TypedTypeKind, TypedConstructorDeclaration, TypedConstructorArguments,
    TypedLabelDeclaration, ModuleType, ModuleTypeDesc, WithConstraint, Signature, SignatureItem,
    SignatureItemDesc, TypedModuleDeclaration, TypedOpenDescription, TypedIncludeDescription,
    TypedValueDescription,
};
use crate::types::decl::{
    TypeDeclaration, TypeKind, ConstructorDeclaration, LabelDeclaration, ConstructorArguments,
    Attribute as DeclAttribute,
};
use crate::types::asttypes::{PrivateFlag as DeclPrivateFlag, MutableFlag as DeclMutableFlag};
use crate::types::variance::Variance;
use crate::types::btype;
use std::collections::HashSet;
use std::io::Write;

// ============================================================================
// Sexp Module - simple string-based pretty printing
// ============================================================================

/// S-expression type
#[derive(Debug, Clone)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    pub fn atom(s: &str) -> Self {
        Sexp::Atom(s.to_string())
    }

    pub fn list(items: Vec<Sexp>) -> Self {
        Sexp::List(items)
    }

    fn to_string_indent(&self, indent: usize) -> String {
        let spaces: String = " ".repeat(indent * 2);
        match self {
            Sexp::Atom(s) => s.clone(),
            Sexp::List(items) if items.is_empty() => "()".to_string(),
            Sexp::List(items) if items.len() == 1 => {
                if let Sexp::Atom(s) = &items[0] {
                    format!("({})", s)
                } else {
                    format!("({})", items[0].to_string_indent(indent))
                }
            }
            Sexp::List(items) => {
                let inner: Vec<String> = items
                    .iter()
                    .map(|item| item.to_string_indent(indent + 1))
                    .collect();
                let sep = format!("\n{}  ", spaces);
                format!("({})", inner.join(&sep))
            }
        }
    }

    pub fn to_string(&self) -> String {
        self.to_string_indent(0)
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

fn string(txt: &str) -> Sexp {
    Sexp::atom(&format!("\"{}\"", txt))
}

fn opt_string(opt: &Option<String>) -> Sexp {
    match opt {
        None => Sexp::atom("None"),
        Some(s) => Sexp::list(vec![Sexp::atom("Some"), string(s)]),
    }
}

fn opt<T, F>(f: F, opt: &Option<T>) -> Sexp
where
    F: Fn(&T) -> Sexp,
{
    match opt {
        None => Sexp::atom("None"),
        Some(x) => Sexp::list(vec![Sexp::atom("Some"), f(x)]),
    }
}

/// Convert a LocIdx to a Sexp location representation.
/// Used for types that use arena-based location storage (LocIdx).
fn location_idx(arena: &ParseArena, with_locs: bool, loc: LocIdx) -> Sexp {
    if with_locs {
        let full_loc = arena.to_location(loc);
        Sexp::list(vec![
            Sexp::atom("loc"),
            Sexp::atom(&full_loc.loc_start.line.to_string()),
            Sexp::atom(&full_loc.loc_start.column().to_string()),
            Sexp::atom(&full_loc.loc_end.line.to_string()),
            Sexp::atom(&full_loc.loc_end.column().to_string()),
        ])
    } else {
        Sexp::list(vec![])
    }
}

/// Convert a Location to a Sexp location representation.
/// Used for types that use full Location values (from decl.rs).
fn location(with_locs: bool, loc: &Location) -> Sexp {
    if with_locs {
        Sexp::list(vec![
            Sexp::atom("loc"),
            Sexp::atom(&loc.loc_start.line.to_string()),
            Sexp::atom(&loc.loc_start.column().to_string()),
            Sexp::atom(&loc.loc_end.line.to_string()),
            Sexp::atom(&loc.loc_end.column().to_string()),
        ])
    } else {
        Sexp::list(vec![])
    }
}

// ============================================================================
// Path Printer
// ============================================================================

fn sexp_path(p: &Path) -> Sexp {
    match p {
        Path::Pident(id) => Sexp::list(vec![Sexp::atom("Pident"), string(id.name())]),
        Path::Pdot(parent, s, _) => {
            Sexp::list(vec![Sexp::atom("Pdot"), sexp_path(parent), string(s)])
        }
        Path::Papply(p1, p2) => {
            Sexp::list(vec![Sexp::atom("Papply"), sexp_path(p1), sexp_path(p2)])
        }
    }
}

// ============================================================================
// Longident Printer
// ============================================================================

fn sexp_longident(arena: &ParseArena, li: &Longident) -> Sexp {
    match li {
        Longident::Lident(s_idx) => {
            let s = arena.get_string(*s_idx);
            Sexp::list(vec![Sexp::atom("Lident"), string(s)])
        }
        Longident::Ldot(parent, s_idx) => {
            let s = arena.get_string(*s_idx);
            Sexp::list(vec![Sexp::atom("Ldot"), sexp_longident(arena, parent), string(s)])
        }
        Longident::Lapply(l1, l2) => {
            Sexp::list(vec![Sexp::atom("Lapply"), sexp_longident(arena, l1), sexp_longident(arena, l2)])
        }
    }
}

fn sexp_longident_idx(arena: &ParseArena, idx: crate::parse_arena::LidentIdx) -> Sexp {
    sexp_longident(arena, arena.get_longident(idx))
}

// ============================================================================
// Ident Printer - just the name, skip stamp for determinism
// ============================================================================

fn sexp_ident(id: &Ident) -> Sexp {
    string(id.name())
}

// ============================================================================
// Constant Printer
// ============================================================================

fn sexp_constant(c: &Constant) -> Sexp {
    match c {
        Constant::Int(i) => Sexp::list(vec![Sexp::atom("Const_int"), Sexp::atom(&i.to_string())]),
        Constant::Char(c) => Sexp::list(vec![Sexp::atom("Const_char"), Sexp::atom(&c.to_string())]),
        Constant::String(s, delim) => {
            Sexp::list(vec![Sexp::atom("Const_string"), string(s), opt(|d: &String| string(d), delim)])
        }
        Constant::Float(s) => Sexp::list(vec![Sexp::atom("Const_float"), string(s)]),
        Constant::BigInt(positive, s) => {
            let sign_str = if *positive { "+" } else { "-" };
            Sexp::list(vec![Sexp::atom("Const_bigint"), Sexp::atom(sign_str), string(s)])
        }
    }
}

// ============================================================================
// Flags
// ============================================================================

fn sexp_rec_flag(flag: &RecFlag) -> Sexp {
    match flag {
        RecFlag::Nonrecursive => Sexp::atom("Nonrecursive"),
        RecFlag::Recursive => Sexp::atom("Recursive"),
    }
}

fn sexp_direction_flag(flag: &DirectionFlag) -> Sexp {
    match flag {
        DirectionFlag::Upto => Sexp::atom("Upto"),
        DirectionFlag::Downto => Sexp::atom("Downto"),
    }
}

fn sexp_private_flag(flag: &PrivateFlag) -> Sexp {
    match flag {
        PrivateFlag::Public => Sexp::atom("Public"),
        PrivateFlag::Private => Sexp::atom("Private"),
    }
}

fn sexp_mutable_flag(flag: &MutableFlag) -> Sexp {
    match flag {
        MutableFlag::Immutable => Sexp::atom("Immutable"),
        MutableFlag::Mutable => Sexp::atom("Mutable"),
    }
}

// Versions for decl.rs types (asttypes module)
fn sexp_decl_private_flag(flag: &DeclPrivateFlag) -> Sexp {
    match flag {
        DeclPrivateFlag::Public => Sexp::atom("Public"),
        DeclPrivateFlag::Private => Sexp::atom("Private"),
    }
}

fn sexp_decl_mutable_flag(flag: &DeclMutableFlag) -> Sexp {
    match flag {
        DeclMutableFlag::Immutable => Sexp::atom("Immutable"),
        DeclMutableFlag::Mutable => Sexp::atom("Mutable"),
    }
}

/// Convert Arity to OCaml-style Option<int> sexp
fn sexp_arity(arity: &Arity) -> Sexp {
    match arity {
        Arity::Full(n) => Sexp::list(vec![Sexp::atom("Some"), Sexp::atom(&n.to_string())]),
        Arity::Unknown => Sexp::atom("None"),
    }
}

/// Extract the param ident from a function param pattern.
/// Returns the ident from Tpat_var, or creates a dummy ident for other patterns.
fn extract_param_ident(param: &FunctionParam) -> Ident {
    match &param.pat {
        FunctionParamPattern::Simple(pat) => {
            match &pat.pat_desc {
                PatternDesc::Tpat_var(id, _) => id.clone(),
                PatternDesc::Tpat_alias(_, id, _) => id.clone(),
                // For other patterns, create a synthetic ident
                _ => Ident::create_persistent("param"),
            }
        }
        FunctionParamPattern::Nested(_) => Ident::create_persistent("param"),
    }
}

// Attribute helper for decl.rs Attribute type
fn sexp_decl_attributes(_with_locs: bool, attrs: &[DeclAttribute]) -> Sexp {
    if attrs.is_empty() {
        Sexp::list(vec![Sexp::atom("attributes")])
    } else {
        Sexp::list(vec![
            Sexp::atom("attributes"),
            Sexp::list(attrs.iter().map(|attr| {
                Sexp::list(vec![
                    string(&attr.attr_name.txt),
                    Sexp::atom("<payload>"),  // Simplified payload
                ])
            }).collect()),
        ])
    }
}

fn sexp_override_flag(flag: &OverrideFlag) -> Sexp {
    match flag {
        OverrideFlag::Override => Sexp::atom("Override"),
        OverrideFlag::Fresh => Sexp::atom("Fresh"),
    }
}

fn sexp_closed_flag(flag: &ClosedFlag) -> Sexp {
    match flag {
        ClosedFlag::Closed => Sexp::atom("Closed"),
        ClosedFlag::Open => Sexp::atom("Open"),
    }
}

fn sexp_arg_label(arena: &ParseArena, lbl: &ArgLabel) -> Sexp {
    match lbl {
        ArgLabel::Nolabel => Sexp::atom("Nolabel"),
        ArgLabel::Labelled(s) => Sexp::list(vec![Sexp::atom("Labelled"), string(arena.get_string(s.txt))]),
        ArgLabel::Optional(s) => Sexp::list(vec![Sexp::atom("Optional"), string(arena.get_string(s.txt))]),
    }
}

// Separate function for type-level ArgLabel (from asttypes)
fn sexp_type_arg_label(lbl: &TypeArgLabel) -> Sexp {
    match lbl {
        TypeArgLabel::Nolabel => Sexp::atom("Nolabel"),
        TypeArgLabel::Labelled(s) => Sexp::list(vec![Sexp::atom("Labelled"), string(&s.txt)]),
        TypeArgLabel::Optional(s) => Sexp::list(vec![Sexp::atom("Optional"), string(&s.txt)]),
    }
}

fn sexp_variance(v: &Variance) -> Sexp {
    if v.is_covariant() {
        Sexp::atom("Covariant")
    } else if v.is_contravariant() {
        Sexp::atom("Contravariant")
    } else {
        Sexp::atom("Invariant")
    }
}

fn sexp_partial(p: &Partial) -> Sexp {
    match p {
        Partial::Partial => Sexp::atom("Partial"),
        Partial::Total => Sexp::atom("Total"),
    }
}

// ============================================================================
// Type Expression Printer - follows Tlink chains via ctx.repr
// Uses a visited set to prevent infinite recursion on cyclic types
// ============================================================================

/// Print a type expression with cycle detection.
/// Each call creates a FRESH visited set - this matches OCaml exactly.
/// OCaml's type_expr function (line 127-196 of sexp_typedtree.ml) creates
/// a new visited hash table for each type expression, not shared across
/// the structure.
fn sexp_type_expr(arena: &ParseArena, ctx: &TypeContext<'_>, te: TypeExprRef) -> Sexp {
    // Create a FRESH visited set for this type expression
    // This matches OCaml: `let visited = Hashtbl.create 16 in`
    let mut visited = HashSet::new();
    sexp_type_expr_aux(arena, ctx, te, &mut visited)
}

/// Recursive helper for type expression printing with shared visited set.
/// Uses physical identity (repr index) for cycle detection, matching OCaml's
/// `Hashtbl.mem visited (Obj.repr te)` after `Btype.repr`.
fn sexp_type_expr_aux(arena: &ParseArena, ctx: &TypeContext<'_>, te: TypeExprRef, visited: &mut HashSet<usize>) -> Sexp {
    // Follow Tlink chains first, then use that for cycle detection.
    // This matches OCaml: `let te = Btype.repr te in` then `Obj.repr te`
    let te = ctx.repr(te);

    // Check if we've already visited this type (cycle detection)
    // Uses the repr's index as physical identity
    if visited.contains(&te.0) {
        return Sexp::atom("<cycle>");
    }
    visited.insert(te.0);

    let desc = ctx.get_desc(te);
    match &*desc {
        TypeDesc::Tvar(name) => Sexp::list(vec![Sexp::atom("Tvar"), opt_string(name)]),
        TypeDesc::Tarrow { arg, ret, arity, .. } => {
            Sexp::list(vec![
                Sexp::atom("Tarrow"),
                sexp_type_arg_label(&arg.lbl),
                sexp_type_expr_aux(arena, ctx, arg.typ, visited),
                sexp_type_expr_aux(arena, ctx, *ret, visited),
                opt(|a: &i32| Sexp::atom(&a.to_string()), arity),
            ])
        }
        TypeDesc::Ttuple(types) => {
            let mut items = vec![Sexp::atom("Ttuple")];
            items.extend(types.iter().map(|t| sexp_type_expr_aux(arena, ctx, *t, visited)));
            Sexp::list(items)
        }
        TypeDesc::Tconstr { path, args, .. } => {
            Sexp::list(vec![
                Sexp::atom("Tconstr"),
                sexp_path(path),
                Sexp::list(args.iter().map(|t| sexp_type_expr_aux(arena, ctx, *t, visited)).collect()),
            ])
        }
        TypeDesc::Tobject { fields, .. } => {
            Sexp::list(vec![Sexp::atom("Tobject"), sexp_type_expr_aux(arena, ctx, *fields, visited)])
        }
        TypeDesc::Tfield { name, kind, typ, rest } => {
            let kind_str = match kind {
                FieldKind::Fpresent => "Fpresent",
                FieldKind::Fabsent => "Fabsent",
                FieldKind::Fvar(_) => "Fvar",
            };
            Sexp::list(vec![
                Sexp::atom("Tfield"),
                string(name),
                Sexp::atom(kind_str),
                sexp_type_expr_aux(arena, ctx, *typ, visited),
                sexp_type_expr_aux(arena, ctx, *rest, visited),
            ])
        }
        TypeDesc::Tnil => Sexp::atom("Tnil"),
        TypeDesc::Tlink(_) => Sexp::atom("Tlink"), // Should not happen after ctx.repr
        TypeDesc::Tsubst(ty) => Sexp::list(vec![Sexp::atom("Tsubst"), sexp_type_expr_aux(arena, ctx, *ty, visited)]),
        TypeDesc::Tvariant(row) => sexp_row_desc(arena, ctx, row, visited),
        TypeDesc::Tunivar(name) => Sexp::list(vec![Sexp::atom("Tunivar"), opt_string(name)]),
        TypeDesc::Tpoly { body, vars } => {
            Sexp::list(vec![
                Sexp::atom("Tpoly"),
                sexp_type_expr_aux(arena, ctx, *body, visited),
                Sexp::list(vars.iter().map(|t| sexp_type_expr_aux(arena, ctx, *t, visited)).collect()),
            ])
        }
        TypeDesc::Tpackage { path, lids, args } => {
            Sexp::list(vec![
                Sexp::atom("Tpackage"),
                sexp_path(path),
                Sexp::list(lids.iter().map(|li| sexp_longident(arena, li)).collect()),
                Sexp::list(args.iter().map(|t| sexp_type_expr_aux(arena, ctx, *t, visited)).collect()),
            ])
        }
    }
}

fn sexp_row_desc(arena: &ParseArena, ctx: &TypeContext<'_>, row: &RowDesc, visited: &mut HashSet<usize>) -> Sexp {
    let row = btype::row_repr(ctx, row);
    Sexp::list(vec![
        Sexp::atom("Tvariant"),
        Sexp::list(
            row.row_fields
                .iter()
                .map(|(l, rf)| Sexp::list(vec![string(l), sexp_row_field(arena, ctx, rf, visited)]))
                .collect(),
        ),
        Sexp::atom(if row.row_closed { "closed" } else { "open" }),
        Sexp::atom(if row.row_fixed { "fixed" } else { "not_fixed" }),
    ])
}

fn sexp_row_field(arena: &ParseArena, ctx: &TypeContext<'_>, rf: &RowField, visited: &mut HashSet<usize>) -> Sexp {
    let rf = btype::row_field_repr(rf);
    match rf {
        RowField::Rpresent(None) => Sexp::atom("Rpresent_none"),
        RowField::Rpresent(Some(ty)) => {
            Sexp::list(vec![Sexp::atom("Rpresent"), sexp_type_expr_aux(arena, ctx, ty, visited)])
        }
        RowField::Reither { constant, types, .. } => {
            Sexp::list(vec![
                Sexp::atom("Reither"),
                Sexp::atom(if constant { "const" } else { "non_const" }),
                Sexp::list(types.iter().map(|t| sexp_type_expr_aux(arena, ctx, *t, visited)).collect()),
            ])
        }
        RowField::Rabsent => Sexp::atom("Rabsent"),
    }
}

// ============================================================================
// Pattern
// ============================================================================

fn sexp_pattern(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, p: &Pattern, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, p.pat_loc)]
    } else {
        vec![]
    };
    let extras: Vec<Sexp> = p.pat_extra.iter().map(|(extra, loc, attrs)| {
        sexp_pat_extra(arena, ctx, with_locs, extra, *loc, attrs, visited)
    }).collect();
    let desc = sexp_pattern_desc(arena, ctx, with_locs, &p.pat_desc, visited);
    // Each type expression gets its own fresh visited set (matches OCaml exactly)
    let ty = sexp_type_expr(arena, ctx, p.pat_type);

    let mut items = vec![Sexp::atom("pattern")];
    items.extend(loc_sexp);
    items.extend(extras);
    items.push(desc);
    items.push(Sexp::list(vec![Sexp::atom("type"), ty]));
    Sexp::list(items)
}

fn sexp_pat_extra(
    arena: &ParseArena,
    ctx: &TypeContext<'_>,
    with_locs: bool,
    extra: &crate::types::typedtree::PatExtra,
    loc: LocIdx,
    attrs: &[Attribute],
    visited: &mut HashSet<usize>,
) -> Sexp {
    use crate::types::typedtree::PatExtra;

    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, loc)]
    } else {
        vec![]
    };
    let attrs_sexp = sexp_attributes(with_locs, attrs);

    match extra {
        PatExtra::Tpat_constraint(ct) => {
            let mut items = vec![Sexp::atom("Tpat_constraint"), sexp_core_type(arena, ctx, with_locs, ct, visited)];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
        PatExtra::Tpat_type(p, _) => {
            let mut items = vec![Sexp::atom("Tpat_type"), sexp_path(p)];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
        PatExtra::Tpat_open(p, _, _) => {
            let mut items = vec![Sexp::atom("Tpat_open"), sexp_path(p)];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
        PatExtra::Tpat_unpack => {
            let mut items = vec![Sexp::atom("Tpat_unpack")];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
    }
}

fn sexp_pattern_desc(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, desc: &PatternDesc, visited: &mut HashSet<usize>) -> Sexp {
    match desc {
        PatternDesc::Tpat_any => Sexp::atom("Tpat_any"),
        PatternDesc::Tpat_var(id, _) => {
            Sexp::list(vec![Sexp::atom("Tpat_var"), sexp_ident(id)])
        }
        PatternDesc::Tpat_alias(p, id, _) => {
            Sexp::list(vec![
                Sexp::atom("Tpat_alias"),
                sexp_pattern(arena, ctx, with_locs, p, visited),
                sexp_ident(id),
            ])
        }
        PatternDesc::Tpat_constant(c) => {
            Sexp::list(vec![Sexp::atom("Tpat_constant"), sexp_constant(c)])
        }
        PatternDesc::Tpat_tuple(pats) => {
            let mut items = vec![Sexp::atom("Tpat_tuple")];
            for p in pats {
                items.push(sexp_pattern(arena, ctx, with_locs, p, visited));
            }
            Sexp::list(items)
        }
        PatternDesc::Tpat_construct(li, _, args) => {
            let mut arg_items = Vec::new();
            for p in args {
                arg_items.push(sexp_pattern(arena, ctx, with_locs, p, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Tpat_construct"),
                sexp_longident_idx(arena, li.txt),
                Sexp::list(arg_items),
            ])
        }
        PatternDesc::Tpat_variant(label, arg, _) => {
            let arg_sexp = match arg {
                None => Sexp::atom("None"),
                Some(p) => Sexp::list(vec![Sexp::atom("Some"), sexp_pattern(arena, ctx, with_locs, p, visited)]),
            };
            Sexp::list(vec![
                Sexp::atom("Tpat_variant"),
                string(label),
                arg_sexp,
            ])
        }
        PatternDesc::Tpat_record(fields, flag) => {
            let mut field_items = Vec::new();
            for (li, _, p, opt_flag) in fields {
                field_items.push(Sexp::list(vec![
                    sexp_longident_idx(arena, li.txt),
                    sexp_pattern(arena, ctx, with_locs, p, visited),
                    Sexp::atom(if *opt_flag { "optional" } else { "required" }),
                ]));
            }
            Sexp::list(vec![
                Sexp::atom("Tpat_record"),
                Sexp::list(field_items),
                sexp_closed_flag(flag),
            ])
        }
        PatternDesc::Tpat_array(pats) => {
            let mut items = vec![Sexp::atom("Tpat_array")];
            for p in pats {
                items.push(sexp_pattern(arena, ctx, with_locs, p, visited));
            }
            Sexp::list(items)
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            Sexp::list(vec![
                Sexp::atom("Tpat_or"),
                sexp_pattern(arena, ctx, with_locs, p1, visited),
                sexp_pattern(arena, ctx, with_locs, p2, visited),
            ])
        }
    }
}

// ============================================================================
// Expression
// ============================================================================

fn sexp_expression(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, e: &Expression, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, e.exp_loc)]
    } else {
        vec![]
    };
    let mut extras = Vec::new();
    for (extra, loc, attrs) in &e.exp_extra {
        extras.push(sexp_exp_extra(arena, ctx, with_locs, extra, *loc, attrs, visited));
    }
    let desc = sexp_expression_desc(arena, ctx, with_locs, &e.exp_desc, visited);
    // Each type expression gets its own fresh visited set (matches OCaml exactly)
    let ty = sexp_type_expr(arena, ctx, e.exp_type);
    let attrs = sexp_attributes(with_locs, &e.exp_attributes);

    let mut items = vec![Sexp::atom("expression")];
    items.extend(loc_sexp);
    items.extend(extras);
    items.push(desc);
    items.push(Sexp::list(vec![Sexp::atom("type"), ty]));
    items.push(attrs);
    Sexp::list(items)
}

fn sexp_exp_extra(
    arena: &ParseArena,
    ctx: &TypeContext<'_>,
    with_locs: bool,
    extra: &crate::types::typedtree::ExpExtra,
    loc: LocIdx,
    attrs: &[Attribute],
    visited: &mut HashSet<usize>,
) -> Sexp {
    use crate::types::typedtree::ExpExtra;

    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, loc)]
    } else {
        vec![]
    };
    let attrs_sexp = sexp_attributes(with_locs, attrs);

    match extra {
        ExpExtra::Texp_constraint(ct) => {
            let mut items = vec![Sexp::atom("Texp_constraint"), sexp_core_type(arena, ctx, with_locs, ct, visited)];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
        ExpExtra::Texp_coerce(ct) => {
            let mut items = vec![Sexp::atom("Texp_coerce"), sexp_core_type(arena, ctx, with_locs, ct, visited)];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
        ExpExtra::Texp_open(flag, p, _, _) => {
            let mut items = vec![Sexp::atom("Texp_open"), sexp_override_flag(flag), sexp_path(p)];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
        ExpExtra::Texp_newtype(s) => {
            let mut items = vec![Sexp::atom("Texp_newtype"), string(s)];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
    }
}

fn sexp_expression_desc(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, desc: &ExpressionDesc, visited: &mut HashSet<usize>) -> Sexp {
    match desc {
        ExpressionDesc::Texp_ident(p, li, _) => {
            Sexp::list(vec![Sexp::atom("Texp_ident"), sexp_path(p), sexp_longident_idx(arena, li.txt)])
        }
        ExpressionDesc::Texp_constant(c) => {
            Sexp::list(vec![Sexp::atom("Texp_constant"), sexp_constant(c)])
        }
        ExpressionDesc::Texp_let(flag, vbs, body) => {
            let mut vb_items = Vec::new();
            for vb in vbs {
                vb_items.push(sexp_value_binding(arena, ctx, with_locs, vb, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_let"),
                sexp_rec_flag(flag),
                Sexp::list(vb_items),
                sexp_expression(arena, ctx, with_locs, body, visited),
            ])
        }
        ExpressionDesc::Texp_function { params, body, partial, arity, async_ } => {
            // OCaml Texp_function has: arg_label, arity (Option<int>), param (Ident), case, partial, async
            // Rust has: params (Vec), body (Vec<Case>), partial, arity, async_
            // For parity, we need to output in OCaml's format

            // Handle single-param single-case (common case)
            if params.len() == 1 && body.len() == 1 {
                let param = &params[0];
                let case = &body[0];
                let param_ident = extract_param_ident(param);

                Sexp::list(vec![
                    Sexp::atom("Texp_function"),
                    sexp_arg_label(arena, &param.label),
                    sexp_arity(arity),
                    sexp_ident(&param_ident),
                    sexp_case(arena, ctx, with_locs, case, visited),
                    sexp_partial(partial),
                    Sexp::atom(if *async_ { "async" } else { "sync" }),
                ])
            } else {
                // Fallback for complex cases - output in a way that shows the structure
                // This won't match OCaml for multi-param functions, but provides debugging info
                let mut param_items = Vec::new();
                for p in params {
                    let default_sexp = match &p.default {
                        None => Sexp::atom("None"),
                        Some(e) => Sexp::list(vec![Sexp::atom("Some"), sexp_expression(arena, ctx, with_locs, e, visited)]),
                    };
                    param_items.push(Sexp::list(vec![
                        sexp_arg_label(arena, &p.label),
                        default_sexp,
                    ]));
                }
                let mut case_items = Vec::new();
                for c in body {
                    case_items.push(sexp_case(arena, ctx, with_locs, c, visited));
                }
                Sexp::list(vec![
                    Sexp::atom("Texp_function"),
                    Sexp::list(param_items),
                    Sexp::list(case_items),
                    sexp_partial(partial),
                    sexp_arity(arity),
                    Sexp::atom(if *async_ { "async" } else { "sync" }),
                ])
            }
        }
        ExpressionDesc::Texp_apply { funct, args, partial, transformed_jsx } => {
            let mut arg_items = Vec::new();
            for arg in args {
                // OCaml has (arg_label * expression option), so we wrap expression in Some
                arg_items.push(Sexp::list(vec![
                    sexp_arg_label(arena, &arg.label),
                    Sexp::list(vec![
                        Sexp::atom("Some"),
                        sexp_expression(arena, ctx, with_locs, &arg.expression, visited),
                    ]),
                ]));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_apply"),
                sexp_expression(arena, ctx, with_locs, funct, visited),
                Sexp::list(arg_items),
                Sexp::atom(if *partial { "partial" } else { "total" }),
                Sexp::atom(if *transformed_jsx { "jsx" } else { "not_jsx" }),
            ])
        }
        ExpressionDesc::Texp_match(e, cases, exn_cases, p) => {
            let mut case_items = Vec::new();
            for c in cases {
                case_items.push(sexp_case(arena, ctx, with_locs, c, visited));
            }
            let mut exn_case_items = Vec::new();
            for c in exn_cases {
                exn_case_items.push(sexp_case(arena, ctx, with_locs, c, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_match"),
                sexp_expression(arena, ctx, with_locs, e, visited),
                Sexp::list(case_items),
                Sexp::list(exn_case_items),
                sexp_partial(p),
            ])
        }
        ExpressionDesc::Texp_try(e, cases) => {
            let mut case_items = Vec::new();
            for c in cases {
                case_items.push(sexp_case(arena, ctx, with_locs, c, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_try"),
                sexp_expression(arena, ctx, with_locs, e, visited),
                Sexp::list(case_items),
            ])
        }
        ExpressionDesc::Texp_tuple(exprs) => {
            let mut items = vec![Sexp::atom("Texp_tuple")];
            for e in exprs {
                items.push(sexp_expression(arena, ctx, with_locs, e, visited));
            }
            Sexp::list(items)
        }
        ExpressionDesc::Texp_construct(li, cstr_desc, args) => {
            // When the longident is a placeholder (from generated code like optional field defaults),
            // use the constructor name from the description instead
            let lid_sexp = if li.txt.0 == 0 {
                // Placeholder longident - use constructor name
                Sexp::list(vec![Sexp::atom("Lident"), string(&cstr_desc.cstr_name)])
            } else {
                sexp_longident_idx(arena, li.txt)
            };
            let mut arg_items = Vec::new();
            for e in args {
                arg_items.push(sexp_expression(arena, ctx, with_locs, e, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_construct"),
                lid_sexp,
                Sexp::list(arg_items),
            ])
        }
        ExpressionDesc::Texp_variant(label, arg) => {
            let arg_sexp = match arg {
                None => Sexp::atom("None"),
                Some(e) => Sexp::list(vec![Sexp::atom("Some"), sexp_expression(arena, ctx, with_locs, e, visited)]),
            };
            Sexp::list(vec![
                Sexp::atom("Texp_variant"),
                string(label),
                arg_sexp,
            ])
        }
        ExpressionDesc::Texp_record { fields, extended_expression } => {
            let mut field_items = Vec::new();
            for (_li, ld, def) in fields {
                let def_sexp = match def {
                    RecordLabelDefinition::Kept(ty) => {
                        Sexp::list(vec![Sexp::atom("Kept"), sexp_type_expr_aux(arena, ctx, *ty, visited)])
                    }
                    RecordLabelDefinition::Overridden(li, e) => {
                        // When the longident is a placeholder (from generated default values),
                        // use the label name from the description instead
                        let lid_sexp = if li.txt.0 == 0 {
                            Sexp::list(vec![Sexp::atom("Lident"), string(&ld.lbl_name)])
                        } else {
                            sexp_longident_idx(arena, li.txt)
                        };
                        Sexp::list(vec![
                            Sexp::atom("Overridden"),
                            lid_sexp,
                            sexp_expression(arena, ctx, with_locs, e, visited),
                        ])
                    }
                };
                // OCaml format: (lbl_name def_sexp "optional"/"required")
                field_items.push(Sexp::list(vec![
                    string(&ld.lbl_name),
                    def_sexp,
                    Sexp::atom(if ld.lbl_optional { "optional" } else { "required" }),
                ]));
            }
            let ext_sexp = match extended_expression {
                None => Sexp::atom("None"),
                Some(e) => Sexp::list(vec![Sexp::atom("Some"), sexp_expression(arena, ctx, with_locs, e, visited)]),
            };
            Sexp::list(vec![
                Sexp::atom("Texp_record"),
                Sexp::list(field_items),
                ext_sexp,
            ])
        }
        ExpressionDesc::Texp_field(e, li, _) => {
            Sexp::list(vec![
                Sexp::atom("Texp_field"),
                sexp_expression(arena, ctx, with_locs, e, visited),
                sexp_longident_idx(arena, li.txt),
            ])
        }
        ExpressionDesc::Texp_setfield(e1, li, _, e2) => {
            Sexp::list(vec![
                Sexp::atom("Texp_setfield"),
                sexp_expression(arena, ctx, with_locs, e1, visited),
                sexp_longident_idx(arena, li.txt),
                sexp_expression(arena, ctx, with_locs, e2, visited),
            ])
        }
        ExpressionDesc::Texp_array(exprs) => {
            let mut items = vec![Sexp::atom("Texp_array")];
            for e in exprs {
                items.push(sexp_expression(arena, ctx, with_locs, e, visited));
            }
            Sexp::list(items)
        }
        ExpressionDesc::Texp_ifthenelse(e1, e2, e3) => {
            let e3_sexp = match e3 {
                None => Sexp::atom("None"),
                Some(e) => Sexp::list(vec![Sexp::atom("Some"), sexp_expression(arena, ctx, with_locs, e, visited)]),
            };
            Sexp::list(vec![
                Sexp::atom("Texp_ifthenelse"),
                sexp_expression(arena, ctx, with_locs, e1, visited),
                sexp_expression(arena, ctx, with_locs, e2, visited),
                e3_sexp,
            ])
        }
        ExpressionDesc::Texp_sequence(e1, e2) => {
            Sexp::list(vec![
                Sexp::atom("Texp_sequence"),
                sexp_expression(arena, ctx, with_locs, e1, visited),
                sexp_expression(arena, ctx, with_locs, e2, visited),
            ])
        }
        ExpressionDesc::Texp_while(e1, e2) => {
            Sexp::list(vec![
                Sexp::atom("Texp_while"),
                sexp_expression(arena, ctx, with_locs, e1, visited),
                sexp_expression(arena, ctx, with_locs, e2, visited),
            ])
        }
        ExpressionDesc::Texp_for(id, _, e1, e2, flag, e3) => {
            Sexp::list(vec![
                Sexp::atom("Texp_for"),
                sexp_ident(id),
                sexp_expression(arena, ctx, with_locs, e1, visited),
                sexp_expression(arena, ctx, with_locs, e2, visited),
                sexp_direction_flag(flag),
                sexp_expression(arena, ctx, with_locs, e3, visited),
            ])
        }
        ExpressionDesc::Texp_send(e, meth, meth_expr) => {
            use crate::types::typedtree::MethKind;
            let meth_sexp = match meth {
                MethKind::Tmeth_name(name) => string(name),
                MethKind::Tmeth_val(id) => sexp_ident(id),
            };
            let meth_expr_sexp = match meth_expr {
                Some(expr) => Sexp::list(vec![Sexp::atom("Some"), sexp_expression(arena, ctx, with_locs, expr, visited)]),
                None => Sexp::atom("None"),
            };
            Sexp::list(vec![Sexp::atom("Texp_send"), sexp_expression(arena, ctx, with_locs, e, visited), meth_sexp, meth_expr_sexp])
        }
        ExpressionDesc::Texp_letmodule(id, _, me, e) => {
            Sexp::list(vec![
                Sexp::atom("Texp_letmodule"),
                sexp_ident(id),
                sexp_module_expr(arena, ctx, with_locs, me, visited),
                sexp_expression(arena, ctx, with_locs, e, visited),
            ])
        }
        ExpressionDesc::Texp_letexception(ec, e) => {
            Sexp::list(vec![
                Sexp::atom("Texp_letexception"),
                sexp_extension_constructor(arena, ctx, with_locs, ec, visited),
                sexp_expression(arena, ctx, with_locs, e, visited),
            ])
        }
        ExpressionDesc::Texp_assert(e) => {
            Sexp::list(vec![Sexp::atom("Texp_assert"), sexp_expression(arena, ctx, with_locs, e, visited)])
        }
        ExpressionDesc::Texp_pack(me) => {
            Sexp::list(vec![Sexp::atom("Texp_pack"), sexp_module_expr(arena, ctx, with_locs, me, visited)])
        }
    }
}

fn sexp_case(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, c: &Case, visited: &mut HashSet<usize>) -> Sexp {
    let guard_sexp = match &c.c_guard {
        None => Sexp::atom("None"),
        Some(e) => Sexp::list(vec![Sexp::atom("Some"), sexp_expression(arena, ctx, with_locs, e, visited)]),
    };
    Sexp::list(vec![
        Sexp::atom("case"),
        sexp_pattern(arena, ctx, with_locs, &c.c_lhs, visited),
        guard_sexp,
        sexp_expression(arena, ctx, with_locs, &c.c_rhs, visited),
    ])
}

fn sexp_value_binding(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, vb: &ValueBinding, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, vb.vb_loc)]
    } else {
        vec![]
    };
    let mut items = vec![Sexp::atom("value_binding")];
    items.extend(loc_sexp);
    items.push(sexp_pattern(arena, ctx, with_locs, &vb.vb_pat, visited));
    items.push(sexp_expression(arena, ctx, with_locs, &vb.vb_expr, visited));
    items.push(sexp_attributes(with_locs, &vb.vb_attributes));
    Sexp::list(items)
}

// ============================================================================
// Core Type
// ============================================================================

fn sexp_core_type(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, ct: &TypedCoreType, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, ct.ctyp_loc)]
    } else {
        vec![]
    };
    let desc = sexp_core_type_desc(arena, ctx, with_locs, &ct.ctyp_desc, visited);
    // If ctyp_type is a placeholder (0), derive type from ctyp_desc instead
    // Each type expression gets its own fresh visited set (matches OCaml exactly)
    let ty = if ct.ctyp_type.0 == 0 {
        sexp_type_from_core_type_desc(&ct.ctyp_desc)
    } else {
        sexp_type_expr(arena, ctx, ct.ctyp_type)
    };
    let attrs = sexp_attributes(with_locs, &ct.ctyp_attributes);

    let mut items = vec![Sexp::atom("core_type")];
    items.extend(loc_sexp);
    items.push(desc);
    items.push(Sexp::list(vec![Sexp::atom("type"), ty]));
    items.push(attrs);
    Sexp::list(items)
}

/// Derive a type sexp from a core type description (for placeholder types in signatures)
fn sexp_type_from_core_type_desc(desc: &TypedCoreTypeDesc) -> Sexp {
    match desc {
        TypedCoreTypeDesc::Ttyp_constr(path, _, _) => {
            // Output Tconstr with the path from the core type
            Sexp::list(vec![
                Sexp::atom("Tconstr"),
                sexp_path(path),
                Sexp::list(vec![]), // Empty type arguments for now
            ])
        }
        TypedCoreTypeDesc::Ttyp_var(Some(name)) => {
            Sexp::list(vec![Sexp::atom("Tvar"), Sexp::list(vec![Sexp::atom("Some"), string(name)])])
        }
        TypedCoreTypeDesc::Ttyp_var(None) => {
            Sexp::list(vec![Sexp::atom("Tvar"), Sexp::atom("None")])
        }
        _ => {
            // Fallback for other types - output a placeholder
            Sexp::list(vec![Sexp::atom("Tvar"), Sexp::atom("None")])
        }
    }
}

fn sexp_core_type_desc(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, desc: &TypedCoreTypeDesc, visited: &mut HashSet<usize>) -> Sexp {
    match desc {
        TypedCoreTypeDesc::Ttyp_var(s) => {
            match s {
                None => Sexp::atom("Ttyp_any"),
                Some(s) => Sexp::list(vec![Sexp::atom("Ttyp_var"), string(s)]),
            }
        }
        TypedCoreTypeDesc::Ttyp_arrow(arg, ret, arity) => {
            Sexp::list(vec![
                Sexp::atom("Ttyp_arrow"),
                sexp_arg_label(arena, &arg.lbl),
                sexp_attributes(with_locs, &arg.attrs),
                sexp_core_type(arena, ctx, with_locs, &*arg.typ, visited),
                sexp_core_type(arena, ctx, with_locs, ret, visited),
                opt(|a: &i32| Sexp::atom(&a.to_string()), arity),
            ])
        }
        TypedCoreTypeDesc::Ttyp_tuple(types) => {
            let mut items = vec![Sexp::atom("Ttyp_tuple")];
            for t in types {
                items.push(sexp_core_type(arena, ctx, with_locs, t, visited));
            }
            Sexp::list(items)
        }
        TypedCoreTypeDesc::Ttyp_constr(p, _, args) => {
            let mut arg_items = Vec::new();
            for t in args {
                arg_items.push(sexp_core_type(arena, ctx, with_locs, t, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Ttyp_constr"),
                sexp_path(p),
                Sexp::list(arg_items),
            ])
        }
        TypedCoreTypeDesc::Ttyp_object(fields, flag) => {
            let mut field_items = Vec::new();
            for f in fields {
                field_items.push(sexp_object_field(arena, ctx, with_locs, f, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Ttyp_object"),
                Sexp::list(field_items),
                sexp_closed_flag(flag),
            ])
        }
        TypedCoreTypeDesc::Ttyp_alias(ct, s) => {
            Sexp::list(vec![
                Sexp::atom("Ttyp_alias"),
                sexp_core_type(arena, ctx, with_locs, ct, visited),
                string(s),
            ])
        }
        TypedCoreTypeDesc::Ttyp_variant(fields, flag, labels) => {
            let mut field_items = Vec::new();
            for f in fields {
                field_items.push(sexp_row_field_type(arena, ctx, with_locs, f, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Ttyp_variant"),
                Sexp::list(field_items),
                sexp_closed_flag(flag),
                opt(
                    |l: &Vec<String>| Sexp::list(l.iter().map(|s| string(s)).collect()),
                    labels,
                ),
            ])
        }
        TypedCoreTypeDesc::Ttyp_poly(vars, ct) => {
            Sexp::list(vec![
                Sexp::atom("Ttyp_poly"),
                Sexp::list(vars.iter().map(|s| string(s)).collect()),
                sexp_core_type(arena, ctx, with_locs, ct, visited),
            ])
        }
        TypedCoreTypeDesc::Ttyp_package(pkg) => {
            let mut field_items = Vec::new();
            for (li, ct) in &pkg.pack_fields {
                field_items.push(Sexp::list(vec![sexp_longident_idx(arena, li.txt), sexp_core_type(arena, ctx, with_locs, ct, visited)]));
            }
            Sexp::list(vec![
                Sexp::atom("Ttyp_package"),
                sexp_path(&pkg.pack_path),
                Sexp::list(field_items),
            ])
        }
    }
}

fn sexp_object_field(
    arena: &ParseArena,
    ctx: &TypeContext<'_>,
    with_locs: bool,
    field: &crate::types::typedtree::ObjectField,
    visited: &mut HashSet<usize>,
) -> Sexp {
    use crate::types::typedtree::ObjectFieldDesc;
    match &field.of_desc {
        ObjectFieldDesc::OTtag(name, ct) => {
            Sexp::list(vec![
                Sexp::atom("OTtag"),
                string(&name.txt),
                sexp_attributes(with_locs, &field.of_attributes),
                sexp_core_type(arena, ctx, with_locs, ct, visited),
            ])
        }
        ObjectFieldDesc::OTinherit(ct) => {
            Sexp::list(vec![Sexp::atom("OTinherit"), sexp_core_type(arena, ctx, with_locs, ct, visited)])
        }
    }
}

fn sexp_row_field_type(
    arena: &ParseArena,
    ctx: &TypeContext<'_>,
    with_locs: bool,
    field: &crate::types::typedtree::RowFieldType,
    visited: &mut HashSet<usize>,
) -> Sexp {
    use crate::types::typedtree::RowFieldDesc;
    match &field.rf_desc {
        RowFieldDesc::Rtag(name, constant, args) => {
            let mut arg_items = Vec::new();
            for ct in args {
                arg_items.push(sexp_core_type(arena, ctx, with_locs, ct, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Ttag"),
                string(&name.txt),
                sexp_attributes(with_locs, &field.rf_attributes),
                Sexp::atom(if *constant { "const" } else { "non_const" }),
                Sexp::list(arg_items),
            ])
        }
        RowFieldDesc::Rinherit(ct) => {
            Sexp::list(vec![Sexp::atom("Tinherit"), sexp_core_type(arena, ctx, with_locs, ct, visited)])
        }
    }
}

// ============================================================================
// Attributes
// ============================================================================

fn sexp_payload(payload: &Payload) -> Sexp {
    match payload {
        Payload::PStr(_) => Sexp::list(vec![Sexp::atom("PStr"), Sexp::atom("<structure>")]),
        Payload::PSig(_) => Sexp::list(vec![Sexp::atom("PSig"), Sexp::atom("<signature>")]),
        Payload::PTyp(_) => Sexp::list(vec![Sexp::atom("PTyp"), Sexp::atom("<core_type>")]),
        Payload::PPat(_, _) => Sexp::list(vec![Sexp::atom("PPat"), Sexp::atom("<pattern>")]),
    }
}

fn sexp_attribute(with_locs: bool, attr: &Attribute) -> Sexp {
    let _ = with_locs;
    let (name, payload) = attr;
    Sexp::list(vec![
        Sexp::atom("attribute"),
        string(&name.txt),
        sexp_payload(payload),
    ])
}

fn sexp_attributes(with_locs: bool, attrs: &[Attribute]) -> Sexp {
    let mut items = vec![Sexp::atom("attributes")];
    items.extend(attrs.iter().map(|a| sexp_attribute(with_locs, a)));
    Sexp::list(items)
}

// ============================================================================
// Module Expression
// ============================================================================

fn sexp_module_expr(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, me: &ModuleExpr, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, me.mod_loc)]
    } else {
        vec![]
    };
    let desc = sexp_module_expr_desc(arena, ctx, with_locs, &me.mod_desc, visited);
    let attrs = sexp_attributes(with_locs, &me.mod_attributes);

    let mut items = vec![Sexp::atom("module_expr")];
    items.extend(loc_sexp);
    items.push(desc);
    items.push(attrs);
    Sexp::list(items)
}

fn sexp_module_expr_desc(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, desc: &ModuleExprDesc, visited: &mut HashSet<usize>) -> Sexp {
    match desc {
        ModuleExprDesc::Tmod_ident(p, _) => {
            Sexp::list(vec![Sexp::atom("Tmod_ident"), sexp_path(p)])
        }
        ModuleExprDesc::Tmod_structure(str) => {
            Sexp::list(vec![Sexp::atom("Tmod_structure"), sexp_structure(arena, ctx, with_locs, str, visited)])
        }
        ModuleExprDesc::Tmod_functor(id, _, mt_arg, me) => {
            let mt_arg_sexp = match mt_arg {
                None => Sexp::atom("None"),
                Some(mt) => Sexp::list(vec![Sexp::atom("Some"), sexp_module_type(arena, ctx, with_locs, mt, visited)]),
            };
            Sexp::list(vec![
                Sexp::atom("Tmod_functor"),
                sexp_ident(id),
                mt_arg_sexp,
                sexp_module_expr(arena, ctx, with_locs, me, visited),
            ])
        }
        ModuleExprDesc::Tmod_apply(me1, me2, _) => {
            Sexp::list(vec![
                Sexp::atom("Tmod_apply"),
                sexp_module_expr(arena, ctx, with_locs, me1, visited),
                sexp_module_expr(arena, ctx, with_locs, me2, visited),
            ])
        }
        ModuleExprDesc::Tmod_constraint(me, _, constraint_, _) => {
            let constraint_sexp = match constraint_ {
                ModuleTypeConstraint::Tmodtype_implicit => Sexp::atom("implicit"),
                ModuleTypeConstraint::Tmodtype_explicit(mt) => {
                    Sexp::list(vec![Sexp::atom("explicit"), sexp_module_type(arena, ctx, with_locs, mt, visited)])
                }
            };
            Sexp::list(vec![
                Sexp::atom("Tmod_constraint"),
                sexp_module_expr(arena, ctx, with_locs, me, visited),
                constraint_sexp,
            ])
        }
        ModuleExprDesc::Tmod_unpack(e, _) => {
            Sexp::list(vec![Sexp::atom("Tmod_unpack"), sexp_expression(arena, ctx, with_locs, e, visited)])
        }
    }
}

// ============================================================================
// Type Declarations (from decl.rs)
// ============================================================================

fn sexp_type_declaration(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, td: &TypeDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    // Note: This prints TypeDeclaration from decl.rs, which is the internal representation.
    // OCaml's Typedtree.type_declaration has more fields (typ_id, typ_name, typ_params as core_type, etc.)
    // We print what we have available.
    let loc_sexp = if with_locs {
        vec![location(with_locs, &td.type_loc)]
    } else {
        vec![]
    };
    let mut param_items = Vec::new();
    for te in &td.type_params {
        param_items.push(sexp_type_expr(arena, ctx, *te));
    }
    let manifest_sexp = match &td.type_manifest {
        None => Sexp::atom("None"),
        Some(te) => Sexp::list(vec![Sexp::atom("Some"), sexp_type_expr(arena, ctx, *te)]),
    };
    let mut items = vec![Sexp::atom("type_declaration")];
    items.extend(loc_sexp);
    items.push(Sexp::list(vec![
        Sexp::atom("params"),
        Sexp::list(param_items),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("kind"),
        sexp_type_kind(arena, ctx, with_locs, &td.type_kind, visited),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("private"),
        sexp_decl_private_flag(&td.type_private),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("manifest"),
        manifest_sexp,
    ]));
    items.push(sexp_decl_attributes(with_locs, &td.type_attributes));
    Sexp::list(items)
}

fn sexp_type_kind(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, kind: &TypeKind, visited: &mut HashSet<usize>) -> Sexp {
    match kind {
        TypeKind::TypeAbstract => Sexp::atom("Ttype_abstract"),
        TypeKind::TypeVariant(cds) => {
            let mut items = vec![Sexp::atom("Ttype_variant")];
            for cd in cds {
                items.push(sexp_constructor_decl(arena, ctx, with_locs, cd, visited));
            }
            Sexp::list(items)
        }
        TypeKind::TypeRecord(lds, _repr) => {
            let mut items = vec![Sexp::atom("Ttype_record")];
            for ld in lds {
                items.push(sexp_label_decl(arena, ctx, with_locs, ld, visited));
            }
            Sexp::list(items)
        }
        TypeKind::TypeOpen => Sexp::atom("Ttype_open"),
    }
}

fn sexp_constructor_decl(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, cd: &ConstructorDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location(with_locs, &cd.cd_loc)]
    } else {
        vec![]
    };
    let res_sexp = match &cd.cd_res {
        None => Sexp::atom("None"),
        Some(te) => Sexp::list(vec![Sexp::atom("Some"), sexp_type_expr(arena, ctx, *te)]),
    };
    let mut items = vec![
        Sexp::atom("constructor_declaration"),
        sexp_ident(&cd.cd_id),
        string(&cd.cd_id.name()),
    ];
    items.extend(loc_sexp);
    items.push(sexp_constructor_args(arena, ctx, with_locs, &cd.cd_args, visited));
    items.push(res_sexp);
    items.push(sexp_decl_attributes(with_locs, &cd.cd_attributes));
    Sexp::list(items)
}

fn sexp_constructor_args(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, args: &ConstructorArguments, visited: &mut HashSet<usize>) -> Sexp {
    match args {
        ConstructorArguments::CstrTuple(types) => {
            let mut items = vec![Sexp::atom("Cstr_tuple")];
            for te in types {
                items.push(sexp_type_expr(arena, ctx, *te));
            }
            Sexp::list(items)
        }
        ConstructorArguments::CstrRecord(lds) => {
            let mut items = vec![Sexp::atom("Cstr_record")];
            for ld in lds {
                items.push(sexp_label_decl(arena, ctx, with_locs, ld, visited));
            }
            Sexp::list(items)
        }
    }
}

fn sexp_label_decl(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, ld: &LabelDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location(with_locs, &ld.ld_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("label_declaration"),
        sexp_ident(&ld.ld_id),
        string(&ld.ld_id.name()),
    ];
    items.extend(loc_sexp);
    items.push(sexp_decl_mutable_flag(&ld.ld_mutable));
    items.push(Sexp::atom(if ld.ld_optional { "optional" } else { "required" }));
    items.push(sexp_type_expr(arena, ctx, ld.ld_type));
    items.push(sexp_decl_attributes(with_locs, &ld.ld_attributes));
    Sexp::list(items)
}

// ============================================================================
// Typed Tree Type Declarations (from typedtree.rs)
// ============================================================================

fn sexp_typed_type_declaration(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, td: &TypedTypeDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, td.typ_loc)]
    } else {
        vec![]
    };
    let mut param_items = Vec::new();
    for (ct, v) in &td.typ_params {
        param_items.push(Sexp::list(vec![sexp_core_type(arena, ctx, with_locs, ct, visited), sexp_variance(v)]));
    }
    let mut cstr_items = Vec::new();
    for (ct1, ct2, _loc) in &td.typ_cstrs {
        cstr_items.push(Sexp::list(vec![
            sexp_core_type(arena, ctx, with_locs, ct1, visited),
            sexp_core_type(arena, ctx, with_locs, ct2, visited),
        ]));
    }
    let manifest_sexp = match &td.typ_manifest {
        None => Sexp::atom("None"),
        Some(ct) => Sexp::list(vec![Sexp::atom("Some"), sexp_core_type(arena, ctx, with_locs, ct, visited)]),
    };
    let mut items = vec![
        Sexp::atom("type_declaration"),
        sexp_ident(&td.typ_id),
        string(&td.typ_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(Sexp::list(vec![
        Sexp::atom("params"),
        Sexp::list(param_items),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("cstrs"),
        Sexp::list(cstr_items),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("kind"),
        sexp_typed_type_kind(arena, ctx, with_locs, &td.typ_kind, visited),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("private"),
        sexp_private_flag(&td.typ_private),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("manifest"),
        manifest_sexp,
    ]));
    items.push(sexp_attributes(with_locs, &td.typ_attributes));
    Sexp::list(items)
}

fn sexp_typed_type_kind(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, kind: &TypedTypeKind, visited: &mut HashSet<usize>) -> Sexp {
    match kind {
        TypedTypeKind::Ttype_abstract => Sexp::atom("Ttype_abstract"),
        TypedTypeKind::Ttype_variant(cds) => {
            let mut items = vec![Sexp::atom("Ttype_variant")];
            for cd in cds {
                items.push(sexp_typed_constructor_decl(arena, ctx, with_locs, cd, visited));
            }
            Sexp::list(items)
        }
        TypedTypeKind::Ttype_record(lds) => {
            let mut items = vec![Sexp::atom("Ttype_record")];
            for ld in lds {
                items.push(sexp_typed_label_decl(arena, ctx, with_locs, ld, visited));
            }
            Sexp::list(items)
        }
        TypedTypeKind::Ttype_open => Sexp::atom("Ttype_open"),
    }
}

fn sexp_typed_constructor_decl(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, cd: &TypedConstructorDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, cd.cd_loc)]
    } else {
        vec![]
    };
    let res_sexp = match &cd.cd_res {
        None => Sexp::atom("None"),
        Some(ct) => Sexp::list(vec![Sexp::atom("Some"), sexp_core_type(arena, ctx, with_locs, ct, visited)]),
    };
    let mut items = vec![
        Sexp::atom("constructor_declaration"),
        sexp_ident(&cd.cd_id),
        string(&cd.cd_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_typed_constructor_args(arena, ctx, with_locs, &cd.cd_args, visited));
    items.push(res_sexp);
    items.push(sexp_attributes(with_locs, &cd.cd_attributes));
    Sexp::list(items)
}

fn sexp_typed_constructor_args(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, args: &TypedConstructorArguments, visited: &mut HashSet<usize>) -> Sexp {
    match args {
        TypedConstructorArguments::Cstr_tuple(types) => {
            let mut items = vec![Sexp::atom("Cstr_tuple")];
            for ct in types {
                items.push(sexp_core_type(arena, ctx, with_locs, ct, visited));
            }
            Sexp::list(items)
        }
        TypedConstructorArguments::Cstr_record(lds) => {
            let mut items = vec![Sexp::atom("Cstr_record")];
            for ld in lds {
                items.push(sexp_typed_label_decl(arena, ctx, with_locs, ld, visited));
            }
            Sexp::list(items)
        }
    }
}

fn sexp_typed_label_decl(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, ld: &TypedLabelDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, ld.ld_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("label_declaration"),
        sexp_ident(&ld.ld_id),
        string(&ld.ld_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_mutable_flag(&ld.ld_mutable));
    items.push(Sexp::atom(if ld.ld_optional { "optional" } else { "required" }));
    items.push(sexp_core_type(arena, ctx, with_locs, &ld.ld_type, visited));
    items.push(sexp_attributes(with_locs, &ld.ld_attributes));
    Sexp::list(items)
}

fn sexp_type_extension(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, te: &TypeExtension, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, te.tyext_loc)]
    } else {
        vec![]
    };
    let mut param_items = Vec::new();
    for (ct, v) in &te.tyext_params {
        param_items.push(Sexp::list(vec![sexp_core_type(arena, ctx, with_locs, ct, visited), sexp_variance(v)]));
    }
    let mut constr_items = Vec::new();
    for ec in &te.tyext_constructors {
        constr_items.push(sexp_extension_constructor(arena, ctx, with_locs, ec, visited));
    }
    let mut items = vec![
        Sexp::atom("type_extension"),
        sexp_path(&te.tyext_path),
        sexp_longident_idx(arena, te.tyext_txt.txt),
    ];
    items.extend(loc_sexp);
    items.push(Sexp::list(vec![
        Sexp::atom("params"),
        Sexp::list(param_items),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("constructors"),
        Sexp::list(constr_items),
    ]));
    items.push(sexp_private_flag(&te.tyext_private));
    items.push(sexp_attributes(with_locs, &te.tyext_attributes));
    Sexp::list(items)
}

// ============================================================================
// Extension Constructor
// ============================================================================

fn sexp_extension_constructor(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, ec: &ExtensionConstructor, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, ec.ext_loc)]
    } else {
        vec![]
    };
    let kind = match &ec.ext_kind {
        ExtensionConstructorKind::Text_decl(args, ret) => {
            // OCaml's Text_decl takes a single constructor_arguments (Cstr_tuple or Cstr_record)
            let ret_sexp = match ret {
                None => Sexp::atom("None"),
                Some(ct) => Sexp::list(vec![Sexp::atom("Some"), sexp_core_type(arena, ctx, with_locs, ct, visited)]),
            };
            Sexp::list(vec![
                Sexp::atom("Text_decl"),
                sexp_constructor_argument(arena, ctx, with_locs, args, visited),
                ret_sexp,
            ])
        }
        ExtensionConstructorKind::Text_rebind(p, _) => {
            Sexp::list(vec![Sexp::atom("Text_rebind"), sexp_path(p)])
        }
    };

    let mut items = vec![
        Sexp::atom("extension_constructor"),
        sexp_ident(&ec.ext_id),
        string(&ec.ext_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(kind);
    items.push(sexp_attributes(with_locs, &ec.ext_attributes));
    Sexp::list(items)
}

fn sexp_constructor_argument(
    arena: &ParseArena,
    ctx: &TypeContext<'_>,
    with_locs: bool,
    arg: &crate::types::typedtree::ConstructorArgument,
    visited: &mut HashSet<usize>,
) -> Sexp {
    use crate::types::typedtree::ConstructorArgument;
    match arg {
        ConstructorArgument::Cstr_tuple(cts) => {
            let mut items = vec![Sexp::atom("Cstr_tuple")];
            for ct in cts {
                items.push(sexp_core_type(arena, ctx, with_locs, ct, visited));
            }
            Sexp::list(items)
        }
        ConstructorArgument::Cstr_record(lds) => {
            let mut items = vec![Sexp::atom("Cstr_record")];
            for ld in lds {
                items.push(sexp_label_declaration(arena, ctx, with_locs, ld, visited));
            }
            Sexp::list(items)
        }
    }
}

fn sexp_label_declaration(
    arena: &ParseArena,
    ctx: &TypeContext<'_>,
    with_locs: bool,
    ld: &crate::types::typedtree::LabelDeclaration,
    visited: &mut HashSet<usize>,
) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, ld.ld_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("label_declaration"),
        sexp_ident(&ld.ld_id),
        string(&ld.ld_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_mutable_flag(&ld.ld_mutable));
    items.push(sexp_core_type(arena, ctx, with_locs, &ld.ld_type, visited));
    items.push(sexp_attributes(with_locs, &ld.ld_attributes));
    Sexp::list(items)
}

// ============================================================================
// Structure
// ============================================================================

fn sexp_structure(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, str: &Structure, visited: &mut HashSet<usize>) -> Sexp {
    let mut items = vec![Sexp::atom("structure")];
    for si in &str.str_items {
        items.push(sexp_structure_item(arena, ctx, with_locs, si, visited));
    }
    Sexp::list(items)
}

fn sexp_structure_item(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, si: &StructureItem, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, si.str_loc)]
    } else {
        vec![]
    };
    let desc = sexp_structure_item_desc(arena, ctx, with_locs, &si.str_desc, visited);
    let mut items = vec![Sexp::atom("structure_item")];
    items.extend(loc_sexp);
    items.push(desc);
    Sexp::list(items)
}

fn sexp_structure_item_desc(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, desc: &StructureItemDesc, visited: &mut HashSet<usize>) -> Sexp {
    match desc {
        StructureItemDesc::Tstr_eval(e, attrs) => {
            Sexp::list(vec![
                Sexp::atom("Tstr_eval"),
                sexp_expression(arena, ctx, with_locs, e, visited),
                sexp_attributes(with_locs, attrs),
            ])
        }
        StructureItemDesc::Tstr_value(flag, vbs) => {
            let mut vb_items = Vec::new();
            for vb in vbs {
                vb_items.push(sexp_value_binding(arena, ctx, with_locs, vb, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Tstr_value"),
                sexp_rec_flag(flag),
                Sexp::list(vb_items),
            ])
        }
        StructureItemDesc::Tstr_primitive(vd) => {
            Sexp::list(vec![
                Sexp::atom("Tstr_primitive"),
                sexp_typed_value_description(arena, ctx, with_locs, vd, visited),
            ])
        }
        StructureItemDesc::Tstr_type(flag, tds) => {
            let mut td_items = Vec::new();
            for td in tds {
                td_items.push(sexp_typed_type_declaration(arena, ctx, with_locs, td, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Tstr_type"),
                sexp_rec_flag(flag),
                Sexp::list(td_items),
            ])
        }
        StructureItemDesc::Tstr_typext(te) => {
            Sexp::list(vec![Sexp::atom("Tstr_typext"), sexp_type_extension(arena, ctx, with_locs, te, visited)])
        }
        StructureItemDesc::Tstr_exception(ec) => {
            Sexp::list(vec![
                Sexp::atom("Tstr_exception"),
                sexp_extension_constructor(arena, ctx, with_locs, ec, visited),
            ])
        }
        StructureItemDesc::Tstr_module(mb) => {
            Sexp::list(vec![
                Sexp::atom("Tstr_module"),
                sexp_module_binding(arena, ctx, with_locs, mb, visited),
            ])
        }
        StructureItemDesc::Tstr_recmodule(mbs) => {
            let mut mb_items = Vec::new();
            for mb in mbs {
                mb_items.push(sexp_module_binding(arena, ctx, with_locs, mb, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Tstr_recmodule"),
                Sexp::list(mb_items),
            ])
        }
        StructureItemDesc::Tstr_modtype(mtd) => {
            Sexp::list(vec![Sexp::atom("Tstr_modtype"), sexp_module_type_declaration(arena, ctx, with_locs, mtd, visited)])
        }
        StructureItemDesc::Tstr_open(od) => {
            Sexp::list(vec![
                Sexp::atom("Tstr_open"),
                sexp_open_declaration(arena, ctx, with_locs, od, visited),
            ])
        }
        StructureItemDesc::Tstr_include(incl) => {
            Sexp::list(vec![Sexp::atom("Tstr_include"), sexp_include_declaration(arena, ctx, with_locs, incl, visited)])
        }
        StructureItemDesc::Tstr_attribute(attr) => {
            Sexp::list(vec![Sexp::atom("Tstr_attribute"), sexp_attribute(with_locs, attr)])
        }
    }
}

fn sexp_module_binding(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, mb: &ModuleBinding, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, mb.mb_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("module_binding"),
        sexp_ident(&mb.mb_id),
        string(&mb.mb_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_module_expr(arena, ctx, with_locs, &mb.mb_expr, visited));
    items.push(sexp_attributes(with_locs, &mb.mb_attributes));
    Sexp::list(items)
}

fn sexp_include_declaration(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, incl: &IncludeDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, incl.incl_loc)]
    } else {
        vec![]
    };
    let mut items = vec![Sexp::atom("include_declaration")];
    items.extend(loc_sexp);
    items.push(sexp_module_expr(arena, ctx, with_locs, &incl.incl_mod, visited));
    items.push(sexp_attributes(with_locs, &incl.incl_attributes));
    Sexp::list(items)
}

fn sexp_open_declaration(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, od: &OpenDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, od.open_loc)]
    } else {
        vec![]
    };
    let mut items = vec![Sexp::atom("open_declaration")];
    items.extend(loc_sexp);
    items.push(sexp_module_expr(arena, ctx, with_locs, &od.open_expr, visited));
    items.push(sexp_override_flag(&od.open_override));
    items.push(sexp_attributes(with_locs, &od.open_attributes));
    Sexp::list(items)
}

fn sexp_module_type_declaration(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, mtd: &ModuleTypeDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, mtd.mtd_loc)]
    } else {
        vec![]
    };
    let type_sexp = match &mtd.mtd_type {
        None => Sexp::atom("None"),
        Some(mt) => Sexp::list(vec![Sexp::atom("Some"), sexp_module_type(arena, ctx, with_locs, mt, visited)]),
    };
    let mut items = vec![
        Sexp::atom("module_type_declaration"),
        sexp_ident(&mtd.mtd_id),
        string(&mtd.mtd_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(type_sexp);
    items.push(sexp_attributes(with_locs, &mtd.mtd_attributes));
    Sexp::list(items)
}

fn sexp_module_type(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, mt: &ModuleType, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, mt.mty_loc)]
    } else {
        vec![]
    };
    let desc = sexp_module_type_desc(arena, ctx, with_locs, &mt.mty_desc, visited);
    let attrs = sexp_attributes(with_locs, &mt.mty_attributes);
    let mut items = vec![Sexp::atom("module_type")];
    items.extend(loc_sexp);
    items.push(desc);
    items.push(attrs);
    Sexp::list(items)
}

fn sexp_module_type_desc(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, desc: &ModuleTypeDesc, visited: &mut HashSet<usize>) -> Sexp {
    use crate::types::typedtree::ModuleTypeDesc;
    match desc {
        ModuleTypeDesc::Tmty_ident(path, _lid) => {
            Sexp::list(vec![Sexp::atom("Tmty_ident"), sexp_path(path)])
        }
        ModuleTypeDesc::Tmty_signature(sig) => {
            Sexp::list(vec![Sexp::atom("Tmty_signature"), sexp_signature(arena, ctx, with_locs, sig, visited)])
        }
        ModuleTypeDesc::Tmty_functor(id, _name, mt_arg, mt_res) => {
            let mt_arg_sexp = match mt_arg.as_ref().map(|b| b.as_ref()) {
                None => Sexp::atom("None"),
                Some(mt) => Sexp::list(vec![Sexp::atom("Some"), sexp_module_type(arena, ctx, with_locs, mt, visited)]),
            };
            Sexp::list(vec![
                Sexp::atom("Tmty_functor"),
                sexp_ident(id),
                mt_arg_sexp,
                sexp_module_type(arena, ctx, with_locs, mt_res, visited),
            ])
        }
        ModuleTypeDesc::Tmty_with(mt, constraints) => {
            let mut constraint_items = Vec::new();
            for (path, _lid, wc) in constraints {
                constraint_items.push(Sexp::list(vec![sexp_path(path), sexp_with_constraint(arena, ctx, with_locs, wc, visited)]));
            }
            Sexp::list(vec![
                Sexp::atom("Tmty_with"),
                sexp_module_type(arena, ctx, with_locs, mt, visited),
                Sexp::list(constraint_items),
            ])
        }
        ModuleTypeDesc::Tmty_typeof(me) => {
            Sexp::list(vec![Sexp::atom("Tmty_typeof"), sexp_module_expr(arena, ctx, with_locs, me, visited)])
        }
        ModuleTypeDesc::Tmty_alias(path, _lid) => {
            Sexp::list(vec![Sexp::atom("Tmty_alias"), sexp_path(path)])
        }
    }
}

fn sexp_with_constraint(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, wc: &WithConstraint, visited: &mut HashSet<usize>) -> Sexp {
    use crate::types::typedtree::WithConstraint;
    match wc {
        WithConstraint::Twith_type(td) => {
            Sexp::list(vec![Sexp::atom("Twith_type"), sexp_typed_type_declaration(arena, ctx, with_locs, td, visited)])
        }
        WithConstraint::Twith_module(path, _lid) => {
            Sexp::list(vec![Sexp::atom("Twith_module"), sexp_path(path)])
        }
        WithConstraint::Twith_typesubst(td) => {
            Sexp::list(vec![Sexp::atom("Twith_typesubst"), sexp_typed_type_declaration(arena, ctx, with_locs, td, visited)])
        }
        WithConstraint::Twith_modsubst(path, _lid) => {
            Sexp::list(vec![Sexp::atom("Twith_modsubst"), sexp_path(path)])
        }
    }
}

fn sexp_signature(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, sig: &Signature, visited: &mut HashSet<usize>) -> Sexp {
    let mut items = vec![Sexp::atom("signature")];
    for item in &sig.sig_items {
        items.push(sexp_signature_item(arena, ctx, with_locs, item, visited));
    }
    Sexp::list(items)
}

fn sexp_signature_item(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, item: &SignatureItem, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, item.sig_loc)]
    } else {
        vec![]
    };
    let desc = sexp_signature_item_desc(arena, ctx, with_locs, &item.sig_desc, visited);
    let mut items = vec![Sexp::atom("signature_item")];
    items.extend(loc_sexp);
    items.push(desc);
    Sexp::list(items)
}

fn sexp_signature_item_desc(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, desc: &SignatureItemDesc, visited: &mut HashSet<usize>) -> Sexp {
    use crate::types::typedtree::SignatureItemDesc;
    match desc {
        SignatureItemDesc::Tsig_value(vd) => {
            Sexp::list(vec![Sexp::atom("Tsig_value"), sexp_typed_value_description(arena, ctx, with_locs, vd, visited)])
        }
        SignatureItemDesc::Tsig_type(flag, tds) => {
            let mut td_items = Vec::new();
            for td in tds {
                td_items.push(sexp_typed_type_declaration(arena, ctx, with_locs, td, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Tsig_type"),
                sexp_rec_flag(flag),
                Sexp::list(td_items),
            ])
        }
        SignatureItemDesc::Tsig_typext(te) => {
            Sexp::list(vec![Sexp::atom("Tsig_typext"), sexp_type_extension(arena, ctx, with_locs, te, visited)])
        }
        SignatureItemDesc::Tsig_exception(ec) => {
            Sexp::list(vec![Sexp::atom("Tsig_exception"), sexp_extension_constructor(arena, ctx, with_locs, ec, visited)])
        }
        SignatureItemDesc::Tsig_module(md) => {
            Sexp::list(vec![Sexp::atom("Tsig_module"), sexp_typed_module_declaration(arena, ctx, with_locs, md, visited)])
        }
        SignatureItemDesc::Tsig_recmodule(mds) => {
            let mut md_items = Vec::new();
            for md in mds {
                md_items.push(sexp_typed_module_declaration(arena, ctx, with_locs, md, visited));
            }
            Sexp::list(vec![
                Sexp::atom("Tsig_recmodule"),
                Sexp::list(md_items),
            ])
        }
        SignatureItemDesc::Tsig_modtype(mtd) => {
            Sexp::list(vec![Sexp::atom("Tsig_modtype"), sexp_module_type_declaration(arena, ctx, with_locs, mtd, visited)])
        }
        SignatureItemDesc::Tsig_open(od) => {
            Sexp::list(vec![Sexp::atom("Tsig_open"), sexp_typed_open_description(arena, with_locs, od)])
        }
        SignatureItemDesc::Tsig_include(incl) => {
            Sexp::list(vec![Sexp::atom("Tsig_include"), sexp_typed_include_description(arena, ctx, with_locs, incl, visited)])
        }
        SignatureItemDesc::Tsig_attribute(attr) => {
            Sexp::list(vec![Sexp::atom("Tsig_attribute"), sexp_attribute(with_locs, attr)])
        }
    }
}

fn sexp_typed_value_description(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, vd: &TypedValueDescription, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, vd.val_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("value_description"),
        sexp_ident(&vd.val_id),
        string(&vd.val_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_core_type(arena, ctx, with_locs, &vd.val_desc, visited));
    items.push(Sexp::list(std::iter::once(Sexp::atom("prim")).chain(vd.val_prim.iter().map(|s| string(s))).collect()));
    items.push(sexp_attributes(with_locs, &vd.val_attributes));
    Sexp::list(items)
}

fn sexp_typed_module_declaration(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, md: &TypedModuleDeclaration, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, md.md_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("module_declaration"),
        sexp_ident(&md.md_id),
        string(&md.md_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_module_type(arena, ctx, with_locs, &md.md_type, visited));
    items.push(sexp_attributes(with_locs, &md.md_attributes));
    Sexp::list(items)
}

fn sexp_typed_open_description(arena: &ParseArena, with_locs: bool, od: &TypedOpenDescription) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, od.open_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("open_description"),
        sexp_path(&od.open_path),
        sexp_longident_loc(arena, od.open_txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_override_flag(&od.open_override));
    items.push(sexp_attributes(with_locs, &od.open_attributes));
    Sexp::list(items)
}

fn sexp_typed_include_description(arena: &ParseArena, ctx: &TypeContext<'_>, with_locs: bool, incl: &TypedIncludeDescription, visited: &mut HashSet<usize>) -> Sexp {
    let loc_sexp = if with_locs {
        vec![location_idx(arena, with_locs, incl.incl_loc)]
    } else {
        vec![]
    };
    let mut items = vec![Sexp::atom("include_description")];
    items.extend(loc_sexp);
    items.push(sexp_module_type(arena, ctx, with_locs, &incl.incl_mod, visited));
    items.push(sexp_attributes(with_locs, &incl.incl_attributes));
    Sexp::list(items)
}

fn sexp_longident_loc(arena: &ParseArena, lid: Loc<LidentIdx>) -> Sexp {
    let longident = arena.get_longident(lid.txt);
    sexp_longident(arena, &longident)
}

// ============================================================================
// Public API
// ============================================================================

/// Print a typed structure as sexp (without locations)
pub fn print_typed_structure<W: Write>(arena: &ParseArena, ctx: &TypeContext<'_>, str: &Structure, out: &mut W) -> std::io::Result<()> {
    let mut visited = HashSet::new();
    let sexp = sexp_structure(arena, ctx, false, str, &mut visited);
    writeln!(out, "{}", sexp.to_string())
}

/// Print a typed structure as sexp (with locations)
pub fn print_typed_structure_with_locs<W: Write>(arena: &ParseArena, ctx: &TypeContext<'_>, str: &Structure, out: &mut W) -> std::io::Result<()> {
    let mut visited = HashSet::new();
    let sexp = sexp_structure(arena, ctx, true, str, &mut visited);
    writeln!(out, "{}", sexp.to_string())
}
