//! Sexp printer for Typedtree - used for parity testing between OCaml and Rust compilers

use crate::ident::Ident;
use crate::parse_arena::{LidentIdx, LocIdx, ParseArena};
use crate::parser::ast::{
    Attribute, ClosedFlag, DirectionFlag, MutableFlag, OverrideFlag, Payload, PrivateFlag, RecFlag,
};
use crate::parser::longident::Longident;
use crate::types::asttypes::ArgLabel as TypeArgLabel;
use crate::types::btype;
use crate::types::context::TypeContext;
use crate::types::path::Path;
use crate::types::tast_arena::{TExprIdx, TypedArena};
use crate::types::type_expr::{RowDesc, RowField, TypeDesc, TypeExprRef};
use crate::types::typedtree::{
    Case, Constant, Expression, ExpressionDesc, ExtensionConstructor, ExtensionConstructorKind,
    Loc, ModuleBinding, ModuleExpr, ModuleExprDesc, ModuleTypeConstraint, OpenDeclaration, Partial,
    Pattern, PatternDesc, RecordField, RecordLabelDefinition, Structure, StructureItem,
    StructureItemDesc, TypeExtension, TypedConstructorArguments, TypedConstructorDeclaration,
    TypedCoreType, TypedCoreTypeDesc, TypedLabelDeclaration, TypedTypeDeclaration, TypedTypeKind,
    ValueBinding,
};
use crate::types::variance::Variance;
use std::collections::HashMap;
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

    /// Append the rendering at nesting depth `indent` to `out`. Lists of two
    /// or more items put each item after the first on its own line,
    /// indented two spaces per level past the opening parenthesis.
    fn write_indent(&self, out: &mut String, indent: usize) {
        match self {
            Sexp::Atom(s) => out.push_str(s),
            Sexp::List(items) => {
                out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push('\n');
                        for _ in 0..indent + 1 {
                            out.push_str("  ");
                        }
                    }
                    // A one-item list keeps its item at the same depth.
                    let depth = if items.len() == 1 { indent } else { indent + 1 };
                    item.write_indent(out, depth);
                }
                out.push(')');
            }
        }
    }
}

impl std::fmt::Display for Sexp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut out = String::new();
        self.write_indent(&mut out, 0);
        f.write_str(&out)
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Write one output line while preserving OCaml-style raw Latin-1 bytes.
fn write_latin1_line<W: Write>(out: &mut W, s: &str) -> std::io::Result<()> {
    let mut bytes = Vec::with_capacity(s.len() + 1);
    for ch in s.chars() {
        let code = ch as u32;
        if code <= 0xFF {
            bytes.push(code as u8);
        } else {
            let mut buf = [0u8; 4];
            bytes.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
        }
    }
    bytes.push(b'\n');
    out.write_all(&bytes)
}

fn string(txt: &str) -> Sexp {
    Sexp::atom(&format!("\"{}\"", txt))
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

/// What every printer function reads besides the parse arena and the type
/// context: the typed tree's node storage and whether locations are printed.
#[derive(Clone, Copy)]
struct Cx<'t> {
    ta: &'t TypedArena,
    with_locs: bool,
}

impl<'t> Cx<'t> {
    fn new(ta: &'t TypedArena, with_locs: bool) -> Self {
        Self { ta, with_locs }
    }
}

/// Convert a LocIdx to a Sexp location representation.
/// Used for types that use arena-based location storage (LocIdx).
fn location_idx(arena: &ParseArena, cx: Cx<'_>, loc: LocIdx) -> Sexp {
    if cx.with_locs {
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

// ============================================================================
// Path Printer
// ============================================================================

fn sexp_path(p: &Path) -> Sexp {
    match p {
        Path::Pident(id) => Sexp::list(vec![Sexp::atom("Pident"), sexp_ident(id)]),
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

fn sexp_longident(arena: &ParseArena, ctx: &TypeContext, li: &Longident) -> Sexp {
    match li {
        Longident::Lident(s_idx) => {
            let s = ctx.resolve_longident_component(arena, *s_idx);
            Sexp::list(vec![Sexp::atom("Lident"), string(&s)])
        }
        Longident::Ldot(parent, s_idx) => {
            let s = ctx.resolve_longident_component(arena, *s_idx);
            Sexp::list(vec![
                Sexp::atom("Ldot"),
                sexp_longident(arena, ctx, parent),
                string(&s),
            ])
        }
        Longident::Lapply(l1, l2) => Sexp::list(vec![
            Sexp::atom("Lapply"),
            sexp_longident(arena, ctx, l1),
            sexp_longident(arena, ctx, l2),
        ]),
    }
}

fn sexp_longident_idx(
    arena: &ParseArena,
    ctx: &TypeContext,
    idx: crate::parse_arena::LidentIdx,
) -> Sexp {
    sexp_longident(arena, ctx, arena.get_longident(idx))
}

fn sexp_lident_name(name: &str) -> Sexp {
    Sexp::list(vec![Sexp::atom("Lident"), string(name)])
}

// ============================================================================
// Ident Printer - name/stamp for full parity
// ============================================================================

fn sexp_ident(id: &Ident) -> Sexp {
    string(&format!("{}/{}", id.name(), id.stamp()))
}

// ============================================================================
// Constant Printer
// ============================================================================

fn sexp_constant(c: &Constant) -> Sexp {
    match c {
        Constant::Int(i) => Sexp::list(vec![Sexp::atom("Const_int"), Sexp::atom(&i.to_string())]),
        Constant::Char(c) => Sexp::list(vec![Sexp::atom("Const_char"), Sexp::atom(&c.to_string())]),
        Constant::String(s) => Sexp::list(vec![Sexp::atom("Const_string"), string(s)]),
        Constant::Float(s) => Sexp::list(vec![Sexp::atom("Const_float"), string(s)]),
        Constant::BigInt(positive, s) => {
            let sign_str = if *positive { "+" } else { "-" };
            Sexp::list(vec![
                Sexp::atom("Const_bigint"),
                Sexp::atom(sign_str),
                string(s),
            ])
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
// Attribute helper for decl.rs Attribute type
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
// Type Expression Serializer
//
// Each typedtree occurrence of a type is serialized inline with a fresh
// `TypeSexpState` (see `sexp_type_expr`):
// - non-cyclic sharing is not recorded; shared nodes are printed structurally
// - Tvar/Tunivar identity is numbered locally within that occurrence
// - real recursion is printed with inline mu/ref binders
// ============================================================================

#[derive(Clone, Copy)]
struct ActiveMuBinding {
    ty: TypeExprRef,
    id: usize,
    used: bool,
}

struct TypeSexpState {
    tvars: HashMap<TypeExprRef, usize>,
    tunivars: HashMap<TypeExprRef, usize>,
    active_bindings: HashMap<TypeExprRef, usize>,
    mu_stack: Vec<ActiveMuBinding>,
    next_tvar_id: usize,
    next_tunivar_id: usize,
    next_mu_id: usize,
}

impl TypeSexpState {
    fn new() -> Self {
        TypeSexpState {
            tvars: HashMap::new(),
            tunivars: HashMap::new(),
            active_bindings: HashMap::new(),
            mu_stack: Vec::new(),
            next_tvar_id: 0,
            next_tunivar_id: 0,
            next_mu_id: 0,
        }
    }

    fn tvar_id(&mut self, te: TypeExprRef) -> usize {
        if let Some(&id) = self.tvars.get(&te) {
            id
        } else {
            let id = self.next_tvar_id;
            self.next_tvar_id += 1;
            self.tvars.insert(te, id);
            id
        }
    }

    fn tunivar_id(&mut self, te: TypeExprRef) -> usize {
        if let Some(&id) = self.tunivars.get(&te) {
            id
        } else {
            let id = self.next_tunivar_id;
            self.next_tunivar_id += 1;
            self.tunivars.insert(te, id);
            id
        }
    }

    fn push_active_binding(&mut self, te: TypeExprRef) -> usize {
        let stack_idx = self.mu_stack.len();
        let id = self.next_mu_id;
        self.next_mu_id += 1;
        self.active_bindings.insert(te, stack_idx);
        self.mu_stack.push(ActiveMuBinding {
            ty: te,
            id,
            used: false,
        });
        stack_idx
    }

    fn lookup_active_binding(&mut self, te: TypeExprRef) -> Option<usize> {
        let stack_idx = *self.active_bindings.get(&te)?;
        self.mu_stack[stack_idx].used = true;
        Some(self.mu_stack[stack_idx].id)
    }

    fn pop_active_binding(&mut self, stack_idx: usize) -> ActiveMuBinding {
        let binding = self
            .mu_stack
            .pop()
            .expect("active mu binding stack underflow");
        debug_assert_eq!(stack_idx, self.mu_stack.len());
        self.active_bindings.remove(&binding.ty);
        binding
    }
}

fn sexp_type_expr_inline(
    arena: &ParseArena,
    ctx: &TypeContext,
    state: &mut TypeSexpState,
    te: TypeExprRef,
) -> Sexp {
    let te = ctx.repr(te); // Follow Tlink chains, but keep Tsubst visible.
    let desc = ctx.get_desc(te);
    match &*desc {
        TypeDesc::Tvar(_) => {
            let id = state.tvar_id(te);
            return Sexp::list(vec![Sexp::atom("Tvar"), Sexp::atom(&id.to_string())]);
        }
        TypeDesc::Tunivar(_) => {
            let id = state.tunivar_id(te);
            return Sexp::list(vec![Sexp::atom("Tunivar"), Sexp::atom(&id.to_string())]);
        }
        _ => {}
    }
    drop(desc);

    if let Some(id) = state.lookup_active_binding(te) {
        return Sexp::list(vec![Sexp::atom("ref"), Sexp::atom(&id.to_string())]);
    }

    let stack_idx = state.push_active_binding(te);
    let sexp = sexp_type_expr_body_inline(arena, ctx, state, te);
    let binding = state.pop_active_binding(stack_idx);

    if binding.used {
        Sexp::list(vec![
            Sexp::atom("mu"),
            Sexp::atom(&binding.id.to_string()),
            sexp,
        ])
    } else {
        sexp
    }
}

fn sexp_type_expr_body_inline(
    arena: &ParseArena,
    ctx: &TypeContext,
    state: &mut TypeSexpState,
    te: TypeExprRef,
) -> Sexp {
    let desc = ctx.get_desc(te);
    match &*desc {
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => {
            unreachable!("variable nodes handled before body serialization")
        }
        TypeDesc::Tarrow { args, ret } => {
            // compiler/ml/sexp_typedtree.ml emits each argument as
            // [arg_label; typ], followed by the return type.
            let mut items = vec![Sexp::atom("Tarrow")];
            for arg in args {
                items.push(Sexp::list(vec![
                    sexp_type_arg_label(arg.label()),
                    sexp_type_expr_inline(arena, ctx, state, arg.typ),
                ]));
            }
            items.push(sexp_type_expr_inline(arena, ctx, state, *ret));
            Sexp::list(items)
        }
        TypeDesc::Ttuple(types) => {
            let mut items = vec![Sexp::atom("Ttuple")];
            for t in types.iter() {
                items.push(sexp_type_expr_inline(arena, ctx, state, *t));
            }
            Sexp::list(items)
        }
        TypeDesc::Tconstr { path, args, .. } => {
            let mut arg_sexps = Vec::new();
            for t in args.iter() {
                arg_sexps.push(sexp_type_expr_inline(arena, ctx, state, *t));
            }
            Sexp::list(vec![
                Sexp::atom("Tconstr"),
                sexp_path(path),
                Sexp::list(arg_sexps),
            ])
        }
        TypeDesc::Tobject { fields, .. } => {
            let fields_sexp = sexp_type_expr_inline(arena, ctx, state, *fields);
            Sexp::list(vec![Sexp::atom("Tobject"), fields_sexp])
        }
        TypeDesc::Tfield {
            name,
            mutability,
            typ,
            rest,
        } => {
            let kind_str = match ctx.mutability_repr(*mutability) {
                crate::types::asttypes::MutableFlag::Immutable => "Immutable",
                crate::types::asttypes::MutableFlag::Mutable => "Mutable",
            };
            let typ_sexp = sexp_type_expr_inline(arena, ctx, state, *typ);
            let rest_sexp = sexp_type_expr_inline(arena, ctx, state, *rest);
            Sexp::list(vec![
                Sexp::atom("Tfield"),
                string(name),
                Sexp::atom(kind_str),
                typ_sexp,
                rest_sexp,
            ])
        }
        TypeDesc::Tnil => Sexp::atom("Tnil"),
        TypeDesc::Tlink(_) => Sexp::atom("Tlink"), // Should not happen after ctx.repr
        TypeDesc::Tsubst(ty) => {
            let s = sexp_type_expr_inline(arena, ctx, state, *ty);
            Sexp::list(vec![Sexp::atom("Tsubst"), s])
        }
        TypeDesc::Tvariant(row) => sexp_row_desc(arena, ctx, state, row),
        TypeDesc::Tpoly { body, vars } => {
            let body_sexp = sexp_type_expr_inline(arena, ctx, state, *body);
            let mut var_sexps = Vec::new();
            for t in vars.iter() {
                var_sexps.push(sexp_type_expr_inline(arena, ctx, state, *t));
            }
            Sexp::list(vec![Sexp::atom("Tpoly"), body_sexp, Sexp::list(var_sexps)])
        }
        TypeDesc::Tpackage { path, lids, args } => {
            let mut arg_sexps = Vec::new();
            for t in args.iter() {
                arg_sexps.push(sexp_type_expr_inline(arena, ctx, state, *t));
            }
            Sexp::list(vec![
                Sexp::atom("Tpackage"),
                sexp_path(path),
                Sexp::list(
                    lids.iter()
                        .map(|li| sexp_longident(arena, ctx, li))
                        .collect(),
                ),
                Sexp::list(arg_sexps),
            ])
        }
    }
}

fn sexp_type_expr(arena: &ParseArena, ctx: &TypeContext, te: TypeExprRef) -> Sexp {
    let mut state = TypeSexpState::new();
    sexp_type_expr_inline(arena, ctx, &mut state, te)
}

fn sexp_row_desc(
    arena: &ParseArena,
    ctx: &TypeContext,
    state: &mut TypeSexpState,
    row: &RowDesc,
) -> Sexp {
    let row = btype::row_repr(ctx, row);
    let mut field_sexps = Vec::new();
    for (l, rf) in row.row_fields.iter() {
        let rf_sexp = sexp_row_field(arena, ctx, state, rf);
        field_sexps.push(Sexp::list(vec![string(l), rf_sexp]));
    }
    Sexp::list(vec![
        Sexp::atom("Tvariant"),
        Sexp::list(field_sexps),
        Sexp::atom(if row.row_closed { "closed" } else { "open" }),
        Sexp::atom(if row.row_fixed { "fixed" } else { "not_fixed" }),
    ])
}

fn sexp_row_field(
    arena: &ParseArena,
    ctx: &TypeContext,
    state: &mut TypeSexpState,
    rf: &RowField,
) -> Sexp {
    let rf = btype::row_field_repr(ctx, rf);
    match rf {
        RowField::Rpresent(None) => Sexp::atom("Rpresent_none"),
        RowField::Rpresent(Some(ty)) => {
            let s = sexp_type_expr_inline(arena, ctx, state, ty);
            Sexp::list(vec![Sexp::atom("Rpresent"), s])
        }
        RowField::Reither {
            constant, types, ..
        } => {
            let mut type_sexps = Vec::new();
            for t in types.iter() {
                type_sexps.push(sexp_type_expr_inline(arena, ctx, state, *t));
            }
            Sexp::list(vec![
                Sexp::atom("Reither"),
                Sexp::atom(if constant { "const" } else { "non_const" }),
                Sexp::list(type_sexps),
            ])
        }
        RowField::Rabsent => Sexp::atom("Rabsent"),
    }
}

// ============================================================================
// Pattern
// ============================================================================

fn sexp_pattern(arena: &ParseArena, ctx: &TypeContext, cx: Cx<'_>, p: &Pattern) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, p.pat_loc)]
    } else {
        vec![]
    };
    let mut extras = Vec::new();
    for (extra, loc, attrs) in p.pat_extra.iter() {
        extras.push(sexp_pat_extra(arena, ctx, cx, extra, *loc, attrs));
    }
    let desc = sexp_pattern_desc(arena, ctx, cx, &p.pat_desc);
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
    ctx: &TypeContext,
    cx: Cx<'_>,
    extra: &crate::types::typedtree::PatExtra,
    loc: LocIdx,
    attrs: &[Attribute],
) -> Sexp {
    use crate::types::typedtree::PatExtra;

    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, loc)]
    } else {
        vec![]
    };
    let attrs_sexp = sexp_attributes(arena, cx, attrs);

    match extra {
        PatExtra::Tpat_constraint(ct) => {
            let mut items = vec![
                Sexp::atom("Tpat_constraint"),
                sexp_core_type(arena, ctx, cx, ct),
            ];
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
        PatExtra::Tpat_unpack => {
            let mut items = vec![Sexp::atom("Tpat_unpack")];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
    }
}

fn sexp_pattern_desc(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    desc: &PatternDesc,
) -> Sexp {
    match desc {
        PatternDesc::Tpat_any => Sexp::atom("Tpat_any"),
        PatternDesc::Tpat_var(id, _) => Sexp::list(vec![Sexp::atom("Tpat_var"), sexp_ident(id)]),
        PatternDesc::Tpat_alias(p, id, _) => Sexp::list(vec![
            Sexp::atom("Tpat_alias"),
            sexp_pattern(arena, ctx, cx, p),
            sexp_ident(id),
        ]),
        PatternDesc::Tpat_constant(c) => {
            Sexp::list(vec![Sexp::atom("Tpat_constant"), sexp_constant(c)])
        }
        PatternDesc::Tpat_tuple(pats) => {
            let mut items = vec![Sexp::atom("Tpat_tuple")];
            for p in pats.iter() {
                items.push(sexp_pattern(arena, ctx, cx, p));
            }
            Sexp::list(items)
        }
        PatternDesc::Tpat_construct(li, _, args) => {
            let mut arg_items = Vec::new();
            for p in args.iter() {
                arg_items.push(sexp_pattern(arena, ctx, cx, p));
            }
            Sexp::list(vec![
                Sexp::atom("Tpat_construct"),
                sexp_longident_idx(arena, ctx, li.txt),
                Sexp::list(arg_items),
            ])
        }
        PatternDesc::Tpat_variant(label, arg, _) => {
            let arg_sexp = match arg {
                None => Sexp::atom("None"),
                Some(p) => Sexp::list(vec![Sexp::atom("Some"), sexp_pattern(arena, ctx, cx, p)]),
            };
            Sexp::list(vec![Sexp::atom("Tpat_variant"), string(label), arg_sexp])
        }
        PatternDesc::Tpat_record(fields, flag, rest) => {
            let mut field_items = Vec::new();
            for (li, _, p, opt_flag) in fields.iter() {
                field_items.push(Sexp::list(vec![
                    sexp_longident_idx(arena, ctx, li.txt),
                    sexp_pattern(arena, ctx, cx, p),
                    Sexp::atom(if *opt_flag { "optional" } else { "required" }),
                ]));
            }
            // Match compiler/ml/sexp_typedtree.ml: the rest component is
            // intentionally not serialized (pattern `Tpat_record (fields, flag, _rest)`).
            let _ = rest;
            Sexp::list(vec![
                Sexp::atom("Tpat_record"),
                Sexp::list(field_items),
                sexp_closed_flag(flag),
            ])
        }
        PatternDesc::Tpat_array(pats) => {
            let mut items = vec![Sexp::atom("Tpat_array")];
            for p in pats.iter() {
                items.push(sexp_pattern(arena, ctx, cx, p));
            }
            Sexp::list(items)
        }
        PatternDesc::Tpat_or(p1, p2, _) => Sexp::list(vec![
            Sexp::atom("Tpat_or"),
            sexp_pattern(arena, ctx, cx, p1),
            sexp_pattern(arena, ctx, cx, p2),
        ]),
    }
}

// ============================================================================
// Expression
// ============================================================================

fn sexp_expression(arena: &ParseArena, ctx: &TypeContext, cx: Cx<'_>, e: TExprIdx) -> Sexp {
    let e = cx.ta.expr(e);
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, e.exp_loc)]
    } else {
        vec![]
    };
    let mut extras = Vec::new();
    for (extra, loc, attrs) in e.exp_extra.iter() {
        extras.push(sexp_exp_extra(arena, ctx, cx, extra, *loc, attrs));
    }
    let desc = sexp_expression_desc(arena, ctx, cx, &e.exp_desc, e.exp_type);
    let ty = sexp_type_expr(arena, ctx, e.exp_type);
    let attrs = sexp_attributes(arena, cx, &e.exp_attributes);

    let mut items = vec![Sexp::atom("expression")];
    items.extend(loc_sexp);
    items.extend(extras);
    items.push(desc);
    items.push(Sexp::list(vec![Sexp::atom("type"), ty]));
    items.push(attrs);
    Sexp::list(items)
}

fn sexp_omitted_optional_none_expression(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    li: &Loc<LidentIdx>,
    option_ty: TypeExprRef,
) -> Sexp {
    sexp_omitted_optional_none_expression_at_loc(arena, ctx, cx, li.loc, option_ty)
}

fn sexp_omitted_optional_none_expression_at_loc(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    loc: LocIdx,
    option_ty: TypeExprRef,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, loc)]
    } else {
        vec![]
    };
    let desc = Sexp::list(vec![
        Sexp::atom("Texp_construct"),
        sexp_longident_idx(arena, ctx, arena.none_lid()),
        Sexp::list(Vec::new()),
    ]);
    let ty = sexp_type_expr(arena, ctx, option_ty);

    let mut items = vec![Sexp::atom("expression")];
    items.extend(loc_sexp);
    items.push(desc);
    items.push(Sexp::list(vec![Sexp::atom("type"), ty]));
    items.push(Sexp::list(vec![Sexp::atom("attributes")]));
    Sexp::list(items)
}

fn sexp_exp_extra(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    extra: &crate::types::typedtree::ExpExtra,
    loc: LocIdx,
    attrs: &[Attribute],
) -> Sexp {
    use crate::types::typedtree::ExpExtra;

    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, loc)]
    } else {
        vec![]
    };
    let attrs_sexp = sexp_attributes(arena, cx, attrs);

    match extra {
        ExpExtra::Texp_constraint(ct) => {
            let mut items = vec![
                Sexp::atom("Texp_constraint"),
                sexp_core_type(arena, ctx, cx, ct),
            ];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
        ExpExtra::Texp_coerce {
            source_type,
            target,
            target_type,
        } => {
            let source_sexp = Sexp::list(vec![
                Sexp::atom("source"),
                sexp_type_expr(arena, ctx, *source_type),
            ]);
            let ct_sexp = sexp_core_type(arena, ctx, cx, target);
            let target_sexp = Sexp::list(vec![
                Sexp::atom("target"),
                sexp_type_expr(arena, ctx, *target_type),
            ]);
            let mut items = vec![Sexp::atom("Texp_coerce"), source_sexp, ct_sexp, target_sexp];
            items.extend(loc_sexp);
            items.push(attrs_sexp);
            Sexp::list(items)
        }
        ExpExtra::Texp_open(flag, p, _, _) => {
            let mut items = vec![
                Sexp::atom("Texp_open"),
                sexp_override_flag(flag),
                sexp_path(p),
            ];
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

fn sexp_record_definition(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    def: &RecordLabelDefinition,
) -> Sexp {
    match def {
        RecordLabelDefinition::Kept(ty) => {
            Sexp::list(vec![Sexp::atom("Kept"), sexp_type_expr(arena, ctx, *ty)])
        }
        RecordLabelDefinition::Overridden(li, e) => Sexp::list(vec![
            Sexp::atom("Overridden"),
            sexp_longident_idx(arena, ctx, li.txt),
            sexp_expression(arena, ctx, cx, *e),
        ]),
        // Intentional Rust performance representation: `OmittedOptionalNone`
        // is the sparse internal form of the `option_none` expression that
        // OCaml compiler/ml/typecore.ml:2833-2842 materializes. Sexp output
        // must expand it here, not remove the sparse storage optimization.
        RecordLabelDefinition::OmittedOptionalNone(li, option_ty) => Sexp::list(vec![
            Sexp::atom("Overridden"),
            sexp_longident_idx(arena, ctx, li.txt),
            sexp_omitted_optional_none_expression(arena, ctx, cx, li, *option_ty),
        ]),
    }
}

fn sexp_record_field(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    field_name: &str,
    def: &RecordLabelDefinition,
    opt_flag: bool,
) -> Sexp {
    Sexp::list(vec![
        string(field_name),
        sexp_record_definition(arena, ctx, cx, def),
        Sexp::atom(if opt_flag { "optional" } else { "required" }),
    ])
}

fn sexp_expression_desc(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    desc: &ExpressionDesc,
    _exp_type: TypeExprRef,
) -> Sexp {
    match desc {
        ExpressionDesc::Texp_ident(p, li, _) => Sexp::list(vec![
            Sexp::atom("Texp_ident"),
            sexp_path(p),
            sexp_longident_idx(arena, ctx, li.txt),
        ]),
        ExpressionDesc::Texp_constant(c) => {
            Sexp::list(vec![Sexp::atom("Texp_constant"), sexp_constant(c)])
        }
        ExpressionDesc::Texp_break => Sexp::list(vec![Sexp::atom("Texp_break")]),
        ExpressionDesc::Texp_continue => Sexp::list(vec![Sexp::atom("Texp_continue")]),
        ExpressionDesc::Texp_let(flag, vbs, body) => {
            let mut vb_items = Vec::new();
            for vb in vbs.iter() {
                vb_items.push(sexp_value_binding(arena, ctx, cx, vb));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_let"),
                sexp_rec_flag(flag),
                Sexp::list(vb_items),
                sexp_expression(arena, ctx, cx, *body),
            ])
        }
        ExpressionDesc::Texp_function {
            params,
            body,
            async_,
        } => {
            // compiler/ml/sexp_typedtree.ml:382-400.
            let params = params
                .iter()
                .map(|param| {
                    Sexp::list(vec![
                        sexp_type_arg_label(&param.fp_lbl),
                        sexp_ident(&param.fp_param),
                        sexp_pattern(arena, ctx, cx, &param.fp_pat),
                        sexp_partial(&param.fp_partial),
                    ])
                })
                .collect();
            Sexp::list(vec![
                Sexp::atom("Texp_function"),
                Sexp::list(params),
                sexp_expression(arena, ctx, cx, *body),
                Sexp::atom(if *async_ { "async" } else { "sync" }),
            ])
        }
        ExpressionDesc::Texp_apply {
            funct,
            args,
            partial,
            transformed_jsx,
        } => {
            let funct_sexp = sexp_expression(arena, ctx, cx, *funct);
            let mut arg_items = Vec::new();
            for arg in args.iter() {
                let expr_sexp = match &arg.expression {
                    Some(e) => Sexp::list(vec![
                        Sexp::atom("Some"),
                        sexp_expression(arena, ctx, cx, *e),
                    ]),
                    None => Sexp::atom("None"),
                };
                arg_items.push(Sexp::list(vec![sexp_type_arg_label(&arg.label), expr_sexp]));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_apply"),
                funct_sexp,
                Sexp::list(arg_items),
                Sexp::atom(if *partial { "partial" } else { "total" }),
                Sexp::atom(if *transformed_jsx { "jsx" } else { "not_jsx" }),
            ])
        }
        ExpressionDesc::Texp_match(e, cases, exn_cases, p) => {
            let e_sexp = sexp_expression(arena, ctx, cx, *e);
            let mut case_items = Vec::new();
            for c in cases.iter() {
                case_items.push(sexp_case(arena, ctx, cx, c));
            }
            let mut exn_case_items = Vec::new();
            for c in exn_cases.iter() {
                exn_case_items.push(sexp_case(arena, ctx, cx, c));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_match"),
                e_sexp,
                Sexp::list(case_items),
                Sexp::list(exn_case_items),
                sexp_partial(p),
            ])
        }
        ExpressionDesc::Texp_try(e, cases) => {
            let e_sexp = sexp_expression(arena, ctx, cx, *e);
            let mut case_items = Vec::new();
            for c in cases.iter() {
                case_items.push(sexp_case(arena, ctx, cx, c));
            }
            Sexp::list(vec![Sexp::atom("Texp_try"), e_sexp, Sexp::list(case_items)])
        }
        ExpressionDesc::Texp_tuple(exprs) => {
            let mut items = vec![Sexp::atom("Texp_tuple")];
            for e in cx.ta.expr_list(*exprs).iter() {
                items.push(sexp_expression(arena, ctx, cx, *e));
            }
            Sexp::list(items)
        }
        ExpressionDesc::Texp_construct(li, _, args) => {
            let mut arg_items = Vec::new();
            for e in cx.ta.expr_list(*args).iter() {
                arg_items.push(sexp_expression(arena, ctx, cx, *e));
            }
            Sexp::list(vec![
                Sexp::atom("Texp_construct"),
                sexp_longident_idx(arena, ctx, li.txt),
                Sexp::list(arg_items),
            ])
        }
        ExpressionDesc::Texp_variant(label, arg) => {
            let arg_sexp = match arg {
                None => Sexp::atom("None"),
                Some(e) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    sexp_expression(arena, ctx, cx, *e),
                ]),
            };
            Sexp::list(vec![Sexp::atom("Texp_variant"), string(label), arg_sexp])
        }
        ExpressionDesc::Texp_record {
            fields,
            extended_expression,
            ..
        } => {
            let mut field_items = Vec::new();
            for (_li, ld, def, opt_flag) in fields.iter() {
                field_items.push(sexp_record_field(
                    arena,
                    ctx,
                    cx,
                    &ld.lbl_name,
                    def,
                    *opt_flag,
                ));
            }
            let ext_sexp = match extended_expression {
                None => Sexp::atom("None"),
                Some(e) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    sexp_expression(arena, ctx, cx, *e),
                ]),
            };
            Sexp::list(vec![
                Sexp::atom("Texp_record"),
                Sexp::list(field_items),
                ext_sexp,
            ])
        }
        ExpressionDesc::Texp_record_sparse {
            fields,
            all_labels,
            omitted_loc,
            extended_expression,
        } => {
            // Intentional Rust performance representation: this is the
            // typedtree boundary that expands sparse records back to OCaml's
            // full record-field shape for parity output.
            let mut explicit_by_pos: HashMap<usize, &RecordField> =
                HashMap::with_capacity(fields.len());
            for field in fields.iter() {
                let pos = field.1.lbl_pos;
                if pos >= 0 {
                    explicit_by_pos.insert(pos as usize, field);
                }
            }

            // OCaml compiler/ml/typecore.ml:2833-2842 builds definitions from
            // the complete label array before translcore.ml:1145-1191 walks
            // every slot. Serialize the carried shared array rather than
            // rediscovering labels through potentially alias-expanded types.
            let mut field_items = Vec::with_capacity(all_labels.len());
            for (idx, label) in all_labels.iter().enumerate() {
                let pos = if label.lbl_pos >= 0 {
                    label.lbl_pos as usize
                } else {
                    idx
                };
                if let Some((_li, ld, def, opt_flag)) = explicit_by_pos.get(&pos) {
                    field_items.push(sexp_record_field(
                        arena,
                        ctx,
                        cx,
                        &ld.lbl_name,
                        def,
                        *opt_flag,
                    ));
                } else if label.lbl_optional {
                    let def = Sexp::list(vec![
                        Sexp::atom("Overridden"),
                        sexp_lident_name(&label.lbl_name),
                        sexp_omitted_optional_none_expression_at_loc(
                            arena,
                            ctx,
                            cx,
                            *omitted_loc,
                            label.lbl_arg,
                        ),
                    ]);
                    field_items.push(Sexp::list(vec![
                        string(&label.lbl_name),
                        def,
                        Sexp::atom("required"),
                    ]));
                }
            }
            let ext_sexp = match extended_expression {
                None => Sexp::atom("None"),
                Some(e) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    sexp_expression(arena, ctx, cx, *e),
                ]),
            };
            Sexp::list(vec![
                Sexp::atom("Texp_record"),
                Sexp::list(field_items),
                ext_sexp,
            ])
        }
        ExpressionDesc::Texp_field(e, li, _) => Sexp::list(vec![
            Sexp::atom("Texp_field"),
            sexp_expression(arena, ctx, cx, *e),
            sexp_longident_idx(arena, ctx, li.txt),
        ]),
        ExpressionDesc::Texp_setfield(e1, li, _, e2) => Sexp::list(vec![
            Sexp::atom("Texp_setfield"),
            sexp_expression(arena, ctx, cx, *e1),
            sexp_longident_idx(arena, ctx, li.txt),
            sexp_expression(arena, ctx, cx, *e2),
        ]),
        ExpressionDesc::Texp_array(exprs) => {
            let mut items = vec![Sexp::atom("Texp_array")];
            for e in cx.ta.expr_list(*exprs).iter() {
                items.push(sexp_expression(arena, ctx, cx, *e));
            }
            Sexp::list(items)
        }
        ExpressionDesc::Texp_ifthenelse(e1, e2, e3) => {
            // Match OCaml eval order: e1, e2, e3
            let e1_sexp = sexp_expression(arena, ctx, cx, *e1);
            let e2_sexp = sexp_expression(arena, ctx, cx, *e2);
            let e3_sexp = match e3 {
                None => Sexp::atom("None"),
                Some(e) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    sexp_expression(arena, ctx, cx, *e),
                ]),
            };
            Sexp::list(vec![
                Sexp::atom("Texp_ifthenelse"),
                e1_sexp,
                e2_sexp,
                e3_sexp,
            ])
        }
        ExpressionDesc::Texp_sequence(e1, e2) => Sexp::list(vec![
            Sexp::atom("Texp_sequence"),
            sexp_expression(arena, ctx, cx, *e1),
            sexp_expression(arena, ctx, cx, *e2),
        ]),
        ExpressionDesc::Texp_while(e1, e2) => Sexp::list(vec![
            Sexp::atom("Texp_while"),
            sexp_expression(arena, ctx, cx, *e1),
            sexp_expression(arena, ctx, cx, *e2),
        ]),
        ExpressionDesc::Texp_for(id, _, e1, e2, flag, e3) => Sexp::list(vec![
            Sexp::atom("Texp_for"),
            sexp_ident(id),
            sexp_expression(arena, ctx, cx, *e1),
            sexp_expression(arena, ctx, cx, *e2),
            sexp_direction_flag(flag),
            sexp_expression(arena, ctx, cx, *e3),
        ]),
        ExpressionDesc::Texp_for_of(_, _, _, _) => Sexp::list(vec![Sexp::atom("Texp_for_of")]),
        ExpressionDesc::Texp_for_await_of(_, _, _, _) => {
            Sexp::list(vec![Sexp::atom("Texp_for_await_of")])
        }
        ExpressionDesc::Texp_tagged_template {
            tag,
            raw_sources,
            values,
        } => {
            let tag_sexp = sexp_expression(arena, ctx, cx, *tag);
            let values_sexp: Vec<Sexp> = cx
                .ta
                .expr_list(*values)
                .iter()
                .map(|value| sexp_expression(arena, ctx, cx, *value))
                .collect();
            Sexp::list(vec![
                Sexp::atom("Texp_tagged_template"),
                tag_sexp,
                Sexp::list(raw_sources.iter().map(|source| string(source)).collect()),
                Sexp::list(values_sexp),
            ])
        }
        ExpressionDesc::Texp_template { segments, values } => {
            let values_sexp: Vec<Sexp> = cx
                .ta
                .expr_list(*values)
                .iter()
                .map(|value| sexp_expression(arena, ctx, cx, *value))
                .collect();
            Sexp::list(vec![
                Sexp::atom("Texp_template"),
                Sexp::list(
                    segments
                        .iter()
                        .map(|segment| {
                            Sexp::list(vec![string(segment.source()), string(segment.semantic())])
                        })
                        .collect(),
                ),
                Sexp::list(values_sexp),
            ])
        }
        ExpressionDesc::Texp_object_get(e, name) => {
            let e_sexp = sexp_expression(arena, ctx, cx, *e);
            Sexp::list(vec![
                Sexp::atom("Texp_object_get"),
                e_sexp,
                string(&name.txt),
            ])
        }
        ExpressionDesc::Texp_object_set(e1, name, e2) => {
            let e1_sexp = sexp_expression(arena, ctx, cx, *e1);
            let e2_sexp = sexp_expression(arena, ctx, cx, *e2);
            Sexp::list(vec![
                Sexp::atom("Texp_object_set"),
                e1_sexp,
                string(&name.txt),
                e2_sexp,
            ])
        }
        ExpressionDesc::Texp_object_literal(fields) => {
            let mut items = vec![Sexp::atom("Texp_object_literal")];
            for (s, e) in fields {
                items.push(Sexp::list(vec![
                    string(&s.txt),
                    sexp_expression(arena, ctx, cx, *e),
                ]));
            }
            Sexp::list(items)
        }
        ExpressionDesc::Texp_letmodule(id, _, me, e) => Sexp::list(vec![
            Sexp::atom("Texp_letmodule"),
            sexp_ident(id),
            sexp_module_expr(arena, ctx, cx, me),
            sexp_expression(arena, ctx, cx, *e),
        ]),
        ExpressionDesc::Texp_letexception(ec, e) => Sexp::list(vec![
            Sexp::atom("Texp_letexception"),
            sexp_extension_constructor(arena, ctx, cx, ec),
            sexp_expression(arena, ctx, cx, *e),
        ]),
        ExpressionDesc::Texp_assert(e) => Sexp::list(vec![
            Sexp::atom("Texp_assert"),
            sexp_expression(arena, ctx, cx, *e),
        ]),
        ExpressionDesc::Texp_pack(me) => Sexp::list(vec![
            Sexp::atom("Texp_pack"),
            sexp_module_expr(arena, ctx, cx, me),
        ]),
        ExpressionDesc::Texp_extension_constructor(lid, path) => Sexp::list(vec![
            Sexp::atom("Texp_extension_constructor"),
            sexp_longident_idx(arena, ctx, lid.txt),
            sexp_path(path),
        ]),
    }
}

fn sexp_case(arena: &ParseArena, ctx: &TypeContext, cx: Cx<'_>, c: &Case) -> Sexp {
    // Match OCaml eval order: lhs first, then guard, then rhs
    let lhs_sexp = sexp_pattern(arena, ctx, cx, &c.c_lhs);
    let guard_sexp = match &c.c_guard {
        None => Sexp::atom("None"),
        Some(e) => Sexp::list(vec![
            Sexp::atom("Some"),
            sexp_expression(arena, ctx, cx, *e),
        ]),
    };
    let rhs_sexp = sexp_expression(arena, ctx, cx, c.c_rhs);
    Sexp::list(vec![Sexp::atom("case"), lhs_sexp, guard_sexp, rhs_sexp])
}

fn sexp_value_binding(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    vb: &ValueBinding,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, vb.vb_loc)]
    } else {
        vec![]
    };
    let mut items = vec![Sexp::atom("value_binding")];
    items.extend(loc_sexp);
    items.push(sexp_pattern(arena, ctx, cx, &vb.vb_pat));
    items.push(sexp_expression(arena, ctx, cx, vb.vb_expr));
    items.push(sexp_attributes(arena, cx, &vb.vb_attributes));
    Sexp::list(items)
}

// ============================================================================
// Core Type
// ============================================================================

fn sexp_core_type(arena: &ParseArena, ctx: &TypeContext, cx: Cx<'_>, ct: &TypedCoreType) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, ct.ctyp_loc)]
    } else {
        vec![]
    };
    let desc = sexp_core_type_desc(arena, ctx, cx, &ct.ctyp_desc);
    let ty = sexp_type_expr(arena, ctx, ct.ctyp_type);
    let attrs = sexp_attributes(arena, cx, &ct.ctyp_attributes);

    let mut items = vec![Sexp::atom("core_type")];
    items.extend(loc_sexp);
    items.push(desc);
    items.push(Sexp::list(vec![Sexp::atom("type"), ty]));
    items.push(attrs);
    Sexp::list(items)
}

fn sexp_core_type_desc(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    desc: &TypedCoreTypeDesc,
) -> Sexp {
    match desc {
        TypedCoreTypeDesc::Ttyp_var(s) => match s {
            None => Sexp::atom("Ttyp_any"),
            Some(s) => Sexp::list(vec![Sexp::atom("Ttyp_var"), string(s)]),
        },
        TypedCoreTypeDesc::Ttyp_arrow(args, ret) => {
            // compiler/ml/sexp_typedtree.ml emits each Parsetree.arg as
            // [label; attrs; core_type], followed by the return core type.
            let mut items = vec![Sexp::atom("Ttyp_arrow")];
            for arg in args {
                items.push(Sexp::list(vec![
                    sexp_type_arg_label(&arg.lbl),
                    sexp_attributes(arena, cx, &arg.attrs),
                    sexp_core_type(arena, ctx, cx, &arg.typ),
                ]));
            }
            items.push(sexp_core_type(arena, ctx, cx, ret));
            Sexp::list(items)
        }
        TypedCoreTypeDesc::Ttyp_tuple(types) => {
            let mut items = vec![Sexp::atom("Ttyp_tuple")];
            for t in types.iter() {
                items.push(sexp_core_type(arena, ctx, cx, t));
            }
            Sexp::list(items)
        }
        TypedCoreTypeDesc::Ttyp_constr(p, _, args) => {
            let mut arg_items = Vec::new();
            for t in args.iter() {
                arg_items.push(sexp_core_type(arena, ctx, cx, t));
            }
            Sexp::list(vec![
                Sexp::atom("Ttyp_constr"),
                sexp_path(p),
                Sexp::list(arg_items),
            ])
        }
        TypedCoreTypeDesc::Ttyp_object(fields, flag) => {
            let mut field_items = Vec::new();
            for f in fields.iter() {
                field_items.push(sexp_object_field(arena, ctx, cx, f));
            }
            Sexp::list(vec![
                Sexp::atom("Ttyp_object"),
                Sexp::list(field_items),
                sexp_closed_flag(flag),
            ])
        }
        TypedCoreTypeDesc::Ttyp_alias(ct, s) => Sexp::list(vec![
            Sexp::atom("Ttyp_alias"),
            sexp_core_type(arena, ctx, cx, ct),
            string(s),
        ]),
        TypedCoreTypeDesc::Ttyp_variant(fields, flag, labels) => {
            let mut field_items = Vec::new();
            for f in fields.iter() {
                field_items.push(sexp_row_field_type(arena, ctx, cx, f));
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
        TypedCoreTypeDesc::Ttyp_poly(vars, ct) => Sexp::list(vec![
            Sexp::atom("Ttyp_poly"),
            Sexp::list(vars.iter().map(|s| string(s)).collect()),
            sexp_core_type(arena, ctx, cx, ct),
        ]),
        TypedCoreTypeDesc::Ttyp_package(pkg) => {
            let mut field_items = Vec::new();
            for (li, ct) in pkg.pack_fields.iter() {
                field_items.push(Sexp::list(vec![
                    sexp_longident_idx(arena, ctx, li.txt),
                    sexp_core_type(arena, ctx, cx, ct),
                ]));
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
    ctx: &TypeContext,
    cx: Cx<'_>,
    field: &crate::types::typedtree::ObjectField,
) -> Sexp {
    use crate::types::typedtree::ObjectFieldDesc;
    match &field.of_desc {
        ObjectFieldDesc::OTtag(name, ct) => Sexp::list(vec![
            Sexp::atom("OTtag"),
            string(&name.txt),
            sexp_attributes(arena, cx, &field.of_attributes),
            sexp_core_type(arena, ctx, cx, ct),
        ]),
        ObjectFieldDesc::OTinherit(ct) => Sexp::list(vec![
            Sexp::atom("OTinherit"),
            sexp_core_type(arena, ctx, cx, ct),
        ]),
    }
}

fn sexp_row_field_type(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    field: &crate::types::typedtree::RowFieldType,
) -> Sexp {
    use crate::types::typedtree::RowFieldDesc;
    match &field.rf_desc {
        RowFieldDesc::Rtag(name, constant, args) => {
            let mut arg_items = Vec::new();
            for ct in args.iter() {
                arg_items.push(sexp_core_type(arena, ctx, cx, ct));
            }
            Sexp::list(vec![
                Sexp::atom("Ttag"),
                string(&name.txt),
                sexp_attributes(arena, cx, &field.rf_attributes),
                Sexp::atom(if *constant { "const" } else { "non_const" }),
                Sexp::list(arg_items),
            ])
        }
        RowFieldDesc::Rinherit(ct) => Sexp::list(vec![
            Sexp::atom("Tinherit"),
            sexp_core_type(arena, ctx, cx, ct),
        ]),
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
        Payload::PPat(_) => Sexp::list(vec![Sexp::atom("PPat"), Sexp::atom("<pattern>")]),
    }
}

fn sexp_attribute(arena: &ParseArena, cx: Cx<'_>, attr: &Attribute) -> Sexp {
    let _ = cx;
    let (name, payload) = attr;
    Sexp::list(vec![
        Sexp::atom("attribute"),
        string(arena.get_string(name.txt)),
        sexp_payload(payload),
    ])
}

fn sexp_attributes(arena: &ParseArena, cx: Cx<'_>, attrs: &[Attribute]) -> Sexp {
    let mut items = vec![Sexp::atom("attributes")];
    items.extend(attrs.iter().map(|a| sexp_attribute(arena, cx, a)));
    Sexp::list(items)
}

// ============================================================================
// Module Expression
// ============================================================================

fn sexp_module_expr(arena: &ParseArena, ctx: &TypeContext, cx: Cx<'_>, me: &ModuleExpr) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, me.mod_loc)]
    } else {
        vec![]
    };
    let desc = sexp_module_expr_desc(arena, ctx, cx, &me.mod_desc);
    let attrs = sexp_attributes(arena, cx, &me.mod_attributes);

    let mut items = vec![Sexp::atom("module_expr")];
    items.extend(loc_sexp);
    items.push(desc);
    items.push(attrs);
    Sexp::list(items)
}

fn sexp_module_expr_desc(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    desc: &ModuleExprDesc,
) -> Sexp {
    match desc {
        ModuleExprDesc::Tmod_ident(p, _) => {
            Sexp::list(vec![Sexp::atom("Tmod_ident"), sexp_path(p)])
        }
        ModuleExprDesc::Tmod_structure(str) => Sexp::list(vec![
            Sexp::atom("Tmod_structure"),
            sexp_structure(arena, ctx, cx, str),
        ]),
        ModuleExprDesc::Tmod_functor(id, _, mt_arg, me) => {
            let mt_arg_sexp = match mt_arg {
                None => Sexp::atom("None"),
                Some(mt) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    sexp_module_type(arena, ctx, cx, mt),
                ]),
            };
            let me_sexp = sexp_module_expr(arena, ctx, cx, me);
            Sexp::list(vec![
                Sexp::atom("Tmod_functor"),
                sexp_ident(id),
                mt_arg_sexp,
                me_sexp,
            ])
        }
        ModuleExprDesc::Tmod_apply(me1, me2, _) => Sexp::list(vec![
            Sexp::atom("Tmod_apply"),
            sexp_module_expr(arena, ctx, cx, me1),
            sexp_module_expr(arena, ctx, cx, me2),
        ]),
        ModuleExprDesc::Tmod_constraint(me, _, constraint_, _) => {
            // Match OCaml eval order: module_expr first, then constraint
            let me_sexp = sexp_module_expr(arena, ctx, cx, me);
            let constraint_sexp = match constraint_ {
                ModuleTypeConstraint::Tmodtype_implicit => Sexp::atom("implicit"),
                ModuleTypeConstraint::Tmodtype_explicit(mt) => {
                    let mt_sexp = sexp_module_type(arena, ctx, cx, mt);
                    Sexp::list(vec![Sexp::atom("explicit"), mt_sexp])
                }
            };
            Sexp::list(vec![
                Sexp::atom("Tmod_constraint"),
                me_sexp,
                constraint_sexp,
            ])
        }
        ModuleExprDesc::Tmod_unpack(e, _) => Sexp::list(vec![
            Sexp::atom("Tmod_unpack"),
            sexp_expression(arena, ctx, cx, *e),
        ]),
    }
}

// ============================================================================
// Type Declarations (from decl.rs)
// ============================================================================

// ============================================================================
// Typed Tree Type Declarations (from typedtree.rs)
// ============================================================================

fn sexp_typed_type_declaration(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    td: &TypedTypeDeclaration,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, td.typ_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("type_declaration"),
        sexp_ident(&td.typ_id),
        string(&td.typ_name.txt),
    ];
    items.extend(loc_sexp);
    let mut param_items = Vec::new();
    for (ct, v) in td.typ_params.iter() {
        param_items.push(Sexp::list(vec![
            sexp_core_type(arena, ctx, cx, ct),
            sexp_variance(v),
        ]));
    }
    items.push(Sexp::list(vec![
        Sexp::atom("params"),
        Sexp::list(param_items),
    ]));
    let mut cstr_items = Vec::new();
    for (ct1, ct2, _loc) in td.typ_cstrs.iter() {
        cstr_items.push(Sexp::list(vec![
            sexp_core_type(arena, ctx, cx, ct1),
            sexp_core_type(arena, ctx, cx, ct2),
        ]));
    }
    items.push(Sexp::list(vec![
        Sexp::atom("cstrs"),
        Sexp::list(cstr_items),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("kind"),
        sexp_typed_type_kind(arena, ctx, cx, &td.typ_kind),
    ]));
    items.push(Sexp::list(vec![
        Sexp::atom("private"),
        sexp_private_flag(&td.typ_private),
    ]));
    let manifest_sexp = match &td.typ_manifest {
        None => Sexp::atom("None"),
        Some(ct) => Sexp::list(vec![Sexp::atom("Some"), sexp_core_type(arena, ctx, cx, ct)]),
    };
    items.push(Sexp::list(vec![Sexp::atom("manifest"), manifest_sexp]));
    items.push(sexp_attributes(arena, cx, &td.typ_attributes));
    Sexp::list(items)
}

fn sexp_typed_type_kind(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    kind: &TypedTypeKind,
) -> Sexp {
    match kind {
        TypedTypeKind::Ttype_abstract => Sexp::atom("Ttype_abstract"),
        TypedTypeKind::Ttype_variant(cds) => {
            let mut items = vec![Sexp::atom("Ttype_variant")];
            for cd in cds.iter() {
                items.push(sexp_typed_constructor_decl(arena, ctx, cx, cd));
            }
            Sexp::list(items)
        }
        TypedTypeKind::Ttype_record(lds) => {
            let mut items = vec![Sexp::atom("Ttype_record")];
            for ld in lds.iter() {
                items.push(sexp_typed_label_decl(arena, ctx, cx, ld));
            }
            Sexp::list(items)
        }
        TypedTypeKind::Ttype_open => Sexp::atom("Ttype_open"),
    }
}

fn sexp_typed_constructor_decl(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    cd: &TypedConstructorDeclaration,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, cd.cd_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("constructor_declaration"),
        sexp_ident(&cd.cd_id),
        string(&cd.cd_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_typed_constructor_args(arena, ctx, cx, &cd.cd_args));
    let res_sexp = match &cd.cd_res {
        None => Sexp::atom("None"),
        Some(ct) => Sexp::list(vec![Sexp::atom("Some"), sexp_core_type(arena, ctx, cx, ct)]),
    };
    items.push(res_sexp);
    items.push(sexp_attributes(arena, cx, &cd.cd_attributes));
    Sexp::list(items)
}

fn sexp_typed_constructor_args(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    args: &TypedConstructorArguments,
) -> Sexp {
    match args {
        TypedConstructorArguments::Cstr_tuple(types) => {
            let mut items = vec![Sexp::atom("Cstr_tuple")];
            for ct in types.iter() {
                items.push(sexp_core_type(arena, ctx, cx, ct));
            }
            Sexp::list(items)
        }
        TypedConstructorArguments::Cstr_record(lds) => {
            let mut items = vec![Sexp::atom("Cstr_record")];
            for ld in lds.iter() {
                items.push(sexp_typed_label_decl(arena, ctx, cx, ld));
            }
            Sexp::list(items)
        }
    }
}

fn sexp_typed_label_decl(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    ld: &TypedLabelDeclaration,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, ld.ld_loc)]
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
    items.push(Sexp::atom(if ld.ld_optional {
        "optional"
    } else {
        "required"
    }));
    items.push(sexp_core_type(arena, ctx, cx, &ld.ld_type));
    items.push(sexp_attributes(arena, cx, &ld.ld_attributes));
    Sexp::list(items)
}

fn sexp_type_extension(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    te: &TypeExtension,
) -> Sexp {
    let mut items = vec![Sexp::atom("type_extension"), sexp_path(&te.tyext_path)];
    let mut param_items = Vec::new();
    for (ct, v) in te.tyext_params.iter() {
        param_items.push(Sexp::list(vec![
            sexp_core_type(arena, ctx, cx, ct),
            sexp_variance(v),
        ]));
    }
    items.push(Sexp::list(vec![
        Sexp::atom("params"),
        Sexp::list(param_items),
    ]));
    let mut constructor_items = Vec::new();
    for ec in te.tyext_constructors.iter() {
        constructor_items.push(sexp_extension_constructor(arena, ctx, cx, ec));
    }
    items.push(Sexp::list(vec![
        Sexp::atom("constructors"),
        Sexp::list(constructor_items),
    ]));
    items.push(sexp_private_flag(&te.tyext_private));
    items.push(sexp_attributes(arena, cx, &te.tyext_attributes));
    Sexp::list(items)
}

// ============================================================================
// Extension Constructor
// ============================================================================

fn sexp_extension_constructor(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    ec: &ExtensionConstructor,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, ec.ext_loc)]
    } else {
        vec![]
    };
    let kind = match &ec.ext_kind {
        ExtensionConstructorKind::Text_decl(args, ret) => {
            let args_sexp = sexp_constructor_argument(arena, ctx, cx, args);
            let ret_sexp = match ret {
                None => Sexp::atom("None"),
                Some(ct) => {
                    Sexp::list(vec![Sexp::atom("Some"), sexp_core_type(arena, ctx, cx, ct)])
                }
            };
            Sexp::list(vec![Sexp::atom("Text_decl"), args_sexp, ret_sexp])
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
    items.push(sexp_attributes(arena, cx, &ec.ext_attributes));
    Sexp::list(items)
}

fn sexp_constructor_argument(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    arg: &crate::types::typedtree::ConstructorArgument,
) -> Sexp {
    use crate::types::typedtree::ConstructorArgument;
    match arg {
        ConstructorArgument::Cstr_tuple(cts) => {
            let mut items = vec![Sexp::atom("Cstr_tuple")];
            for ct in cts.iter() {
                items.push(sexp_core_type(arena, ctx, cx, ct));
            }
            Sexp::list(items)
        }
        ConstructorArgument::Cstr_record(lds) => {
            let mut items = vec![Sexp::atom("Cstr_record")];
            for ld in lds.iter() {
                items.push(sexp_label_declaration(arena, ctx, cx, ld));
            }
            Sexp::list(items)
        }
    }
}

fn sexp_label_declaration(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    ld: &crate::types::typedtree::LabelDeclaration,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, ld.ld_loc)]
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
    items.push(Sexp::atom(if ld.ld_optional {
        "optional"
    } else {
        "required"
    }));
    items.push(sexp_core_type(arena, ctx, cx, &ld.ld_type));
    items.push(sexp_attributes(arena, cx, &ld.ld_attributes));
    Sexp::list(items)
}

// ============================================================================
// Structure
// ============================================================================

fn sexp_structure(arena: &ParseArena, ctx: &TypeContext, cx: Cx<'_>, str: &Structure) -> Sexp {
    let mut items = vec![Sexp::atom("structure")];
    for si in str.str_items.iter() {
        items.push(sexp_structure_item(arena, ctx, cx, si));
    }
    Sexp::list(items)
}

fn sexp_structure_item(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    si: &StructureItem,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, si.str_loc)]
    } else {
        vec![]
    };
    let desc = sexp_structure_item_desc(arena, ctx, cx, &si.str_desc);
    let mut items = vec![Sexp::atom("structure_item")];
    items.extend(loc_sexp);
    items.push(desc);
    Sexp::list(items)
}

fn sexp_structure_item_desc(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    desc: &StructureItemDesc,
) -> Sexp {
    match desc {
        StructureItemDesc::Tstr_eval(e, attrs) => Sexp::list(vec![
            Sexp::atom("Tstr_eval"),
            sexp_expression(arena, ctx, cx, *e),
            sexp_attributes(arena, cx, attrs),
        ]),
        StructureItemDesc::Tstr_value(flag, vbs) => {
            let mut vb_items = Vec::new();
            for vb in vbs.iter() {
                vb_items.push(sexp_value_binding(arena, ctx, cx, vb));
            }
            Sexp::list(vec![
                Sexp::atom("Tstr_value"),
                sexp_rec_flag(flag),
                Sexp::list(vb_items),
            ])
        }
        StructureItemDesc::Tstr_primitive(vd) => {
            let vd_sexp = sexp_value_description(arena, ctx, cx, vd);
            Sexp::list(vec![Sexp::atom("Tstr_primitive"), vd_sexp])
        }
        StructureItemDesc::Tstr_type(flag, tds) => {
            let mut td_items = Vec::new();
            for td in tds.iter() {
                td_items.push(sexp_typed_type_declaration(arena, ctx, cx, td));
            }
            Sexp::list(vec![
                Sexp::atom("Tstr_type"),
                sexp_rec_flag(flag),
                Sexp::list(td_items),
            ])
        }
        StructureItemDesc::Tstr_typext(te) => Sexp::list(vec![
            Sexp::atom("Tstr_typext"),
            sexp_type_extension(arena, ctx, cx, te),
        ]),
        StructureItemDesc::Tstr_exception(ec) => Sexp::list(vec![
            Sexp::atom("Tstr_exception"),
            sexp_extension_constructor(arena, ctx, cx, ec),
        ]),
        StructureItemDesc::Tstr_module(mb) => Sexp::list(vec![
            Sexp::atom("Tstr_module"),
            sexp_module_binding(arena, ctx, cx, mb),
        ]),
        StructureItemDesc::Tstr_recmodule(mbs) => {
            let mut mb_items = Vec::new();
            for mb in mbs.iter() {
                mb_items.push(sexp_module_binding(arena, ctx, cx, mb));
            }
            Sexp::list(vec![Sexp::atom("Tstr_recmodule"), Sexp::list(mb_items)])
        }
        StructureItemDesc::Tstr_modtype(mtd) => {
            let mtd_sexp = sexp_module_type_declaration(arena, ctx, cx, mtd);
            Sexp::list(vec![Sexp::atom("Tstr_modtype"), mtd_sexp])
        }
        StructureItemDesc::Tstr_open(od) => Sexp::list(vec![
            Sexp::atom("Tstr_open"),
            sexp_open_declaration(arena, ctx, cx, od),
        ]),
        StructureItemDesc::Tstr_include(incl) => Sexp::list(vec![
            Sexp::atom("Tstr_include"),
            sexp_include_declaration(arena, ctx, cx, incl),
        ]),
        StructureItemDesc::Tstr_attribute(attr) => Sexp::list(vec![
            Sexp::atom("Tstr_attribute"),
            sexp_attribute(arena, cx, attr),
        ]),
    }
}

fn sexp_module_binding(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    mb: &ModuleBinding,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, mb.mb_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("module_binding"),
        sexp_ident(&mb.mb_id),
        string(&mb.mb_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_module_expr(arena, ctx, cx, &mb.mb_expr));
    items.push(sexp_attributes(arena, cx, &mb.mb_attributes));
    Sexp::list(items)
}

fn sexp_open_declaration(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    od: &OpenDeclaration,
) -> Sexp {
    let mut items = vec![
        Sexp::atom("open_description"),
        sexp_path(&od.open_path),
        sexp_longident_idx(arena, ctx, od.open_txt.txt),
    ];
    items.push(sexp_override_flag(&od.open_override));
    items.push(sexp_attributes(arena, cx, &od.open_attributes));
    Sexp::list(items)
}

// ============================================================================
// Module Types
// ============================================================================

fn sexp_module_type(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    mt: &crate::types::typedtree::ModuleType,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, mt.mty_loc)]
    } else {
        vec![]
    };
    let desc = sexp_module_type_desc(arena, ctx, cx, &mt.mty_desc);
    let attrs = sexp_attributes(arena, cx, &mt.mty_attributes);
    let mut items = vec![Sexp::atom("module_type")];
    items.extend(loc_sexp);
    items.push(desc);
    items.push(attrs);
    Sexp::list(items)
}

fn sexp_module_type_desc(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    desc: &crate::types::typedtree::ModuleTypeDesc,
) -> Sexp {
    use crate::types::typedtree::ModuleTypeDesc;
    match desc {
        ModuleTypeDesc::Tmty_ident(p, _) => {
            Sexp::list(vec![Sexp::atom("Tmty_ident"), sexp_path(p)])
        }
        ModuleTypeDesc::Tmty_signature(sig) => Sexp::list(vec![
            Sexp::atom("Tmty_signature"),
            sexp_typed_signature(arena, ctx, cx, sig),
        ]),
        ModuleTypeDesc::Tmty_functor(id, _, mt_arg, mt_res) => {
            let mt_arg_sexp = match mt_arg {
                None => Sexp::atom("None"),
                Some(mt) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    sexp_module_type(arena, ctx, cx, mt),
                ]),
            };
            Sexp::list(vec![
                Sexp::atom("Tmty_functor"),
                sexp_ident(id),
                mt_arg_sexp,
                sexp_module_type(arena, ctx, cx, mt_res),
            ])
        }
        ModuleTypeDesc::Tmty_with(mt, constraints) => {
            // OCaml evaluates mt_sexp BEFORE constraints (via let binding).
            // Must match to get identical DFS encounter order for type nodes.
            let mt_sexp = sexp_module_type(arena, ctx, cx, mt);
            let mut constraint_sexps = Vec::new();
            for (p, _, wc) in constraints.iter() {
                constraint_sexps.push(Sexp::list(vec![
                    sexp_path(p),
                    sexp_with_constraint(arena, ctx, cx, wc),
                ]));
            }
            Sexp::list(vec![
                Sexp::atom("Tmty_with"),
                mt_sexp,
                Sexp::list(constraint_sexps),
            ])
        }
        ModuleTypeDesc::Tmty_typeof(me) => Sexp::list(vec![
            Sexp::atom("Tmty_typeof"),
            sexp_module_expr(arena, ctx, cx, me),
        ]),
        ModuleTypeDesc::Tmty_alias(p, _) => {
            Sexp::list(vec![Sexp::atom("Tmty_alias"), sexp_path(p)])
        }
    }
}

fn sexp_with_constraint(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    wc: &crate::types::typedtree::WithConstraint,
) -> Sexp {
    use crate::types::typedtree::WithConstraint;
    match wc {
        WithConstraint::Twith_type(td) => Sexp::list(vec![
            Sexp::atom("Twith_type"),
            sexp_typed_type_declaration(arena, ctx, cx, td),
        ]),
        WithConstraint::Twith_module(p, _) => {
            Sexp::list(vec![Sexp::atom("Twith_module"), sexp_path(p)])
        }
        WithConstraint::Twith_typesubst(td) => Sexp::list(vec![
            Sexp::atom("Twith_typesubst"),
            sexp_typed_type_declaration(arena, ctx, cx, td),
        ]),
        WithConstraint::Twith_modsubst(p, _) => {
            Sexp::list(vec![Sexp::atom("Twith_modsubst"), sexp_path(p)])
        }
    }
}

// ============================================================================
// Typed Signatures
// ============================================================================

fn sexp_typed_signature(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    sig: &crate::types::typedtree::TypedSignature,
) -> Sexp {
    let mut items = vec![Sexp::atom("signature")];
    for si in sig.sig_items.iter() {
        items.push(sexp_typed_signature_item(arena, ctx, cx, si));
    }
    Sexp::list(items)
}

fn sexp_typed_signature_item(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    si: &crate::types::typedtree::TypedSignatureItem,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, si.sig_loc)]
    } else {
        vec![]
    };
    let desc = sexp_typed_signature_item_desc(arena, ctx, cx, &si.sig_desc);
    let mut items = vec![Sexp::atom("signature_item")];
    items.extend(loc_sexp);
    items.push(desc);
    Sexp::list(items)
}

fn sexp_typed_signature_item_desc(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    desc: &crate::types::typedtree::TypedSignatureItemDesc,
) -> Sexp {
    use crate::types::typedtree::TypedSignatureItemDesc;
    match desc {
        TypedSignatureItemDesc::Tsig_value(vd) => Sexp::list(vec![
            Sexp::atom("Tsig_value"),
            sexp_value_description(arena, ctx, cx, vd),
        ]),
        TypedSignatureItemDesc::Tsig_type(flag, tds) => {
            let mut td_sexps = Vec::new();
            for td in tds.iter() {
                td_sexps.push(sexp_typed_type_declaration(arena, ctx, cx, td));
            }
            Sexp::list(vec![
                Sexp::atom("Tsig_type"),
                sexp_rec_flag(flag),
                Sexp::list(td_sexps),
            ])
        }
        TypedSignatureItemDesc::Tsig_typext(te) => Sexp::list(vec![
            Sexp::atom("Tsig_typext"),
            sexp_type_extension(arena, ctx, cx, te),
        ]),
        TypedSignatureItemDesc::Tsig_exception(ec) => Sexp::list(vec![
            Sexp::atom("Tsig_exception"),
            sexp_extension_constructor(arena, ctx, cx, ec),
        ]),
        TypedSignatureItemDesc::Tsig_module(md) => Sexp::list(vec![
            Sexp::atom("Tsig_module"),
            sexp_typed_module_declaration(arena, ctx, cx, md),
        ]),
        TypedSignatureItemDesc::Tsig_recmodule(mds) => {
            let mut md_sexps = Vec::new();
            for md in mds.iter() {
                md_sexps.push(sexp_typed_module_declaration(arena, ctx, cx, md));
            }
            Sexp::list(vec![Sexp::atom("Tsig_recmodule"), Sexp::list(md_sexps)])
        }
        TypedSignatureItemDesc::Tsig_modtype(mtd) => Sexp::list(vec![
            Sexp::atom("Tsig_modtype"),
            sexp_module_type_declaration(arena, ctx, cx, mtd),
        ]),
        TypedSignatureItemDesc::Tsig_open(od) => Sexp::list(vec![
            Sexp::atom("Tsig_open"),
            sexp_open_description(arena, ctx, cx, od),
        ]),
        TypedSignatureItemDesc::Tsig_include(incl) => Sexp::list(vec![
            Sexp::atom("Tsig_include"),
            sexp_include_description(arena, ctx, cx, incl),
        ]),
        TypedSignatureItemDesc::Tsig_attribute(attr) => Sexp::list(vec![
            Sexp::atom("Tsig_attribute"),
            sexp_attribute(arena, cx, attr),
        ]),
    }
}

fn sexp_typed_module_declaration(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    md: &crate::types::typedtree::TypedModuleDeclaration,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, md.md_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("module_declaration"),
        sexp_ident(&md.md_id),
        string(&md.md_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_module_type(arena, ctx, cx, &md.md_type));
    items.push(sexp_attributes(arena, cx, &md.md_attributes));
    Sexp::list(items)
}

fn sexp_include_description(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    incl: &crate::types::typedtree::IncludeDescription,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, incl.incl_loc)]
    } else {
        vec![]
    };
    let mut items = vec![Sexp::atom("include_description")];
    items.extend(loc_sexp);
    items.push(sexp_module_type(arena, ctx, cx, &incl.incl_mod));
    items.push(sexp_attributes(arena, cx, &incl.incl_attributes));
    Sexp::list(items)
}

fn sexp_module_type_declaration(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    mtd: &crate::types::typedtree::ModuleTypeDeclaration,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, mtd.mtd_loc)]
    } else {
        vec![]
    };
    let mt_sexp = match &mtd.mtd_type {
        None => Sexp::atom("None"),
        Some(mt) => Sexp::list(vec![
            Sexp::atom("Some"),
            sexp_module_type(arena, ctx, cx, mt),
        ]),
    };
    let mut items = vec![
        Sexp::atom("module_type_declaration"),
        sexp_ident(&mtd.mtd_id),
        string(&mtd.mtd_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(mt_sexp);
    items.push(sexp_attributes(arena, cx, &mtd.mtd_attributes));
    Sexp::list(items)
}

fn sexp_value_description(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    vd: &crate::types::typedtree::TypedValueDescription,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, vd.val_loc)]
    } else {
        vec![]
    };
    let mut items = vec![
        Sexp::atom("value_description"),
        sexp_ident(&vd.val_id),
        string(&vd.val_name.txt),
    ];
    items.extend(loc_sexp);
    items.push(sexp_core_type(arena, ctx, cx, &vd.val_desc));
    items.push(Sexp::list(
        std::iter::once(Sexp::atom("prim"))
            .chain(
                vd.val_prim
                    .as_ref()
                    .map(|prim| prim.debug_strings(arena))
                    .unwrap_or_default()
                    .iter()
                    .map(|s| string(s)),
            )
            .collect(),
    ));
    items.push(sexp_attributes(arena, cx, &vd.val_attributes));
    Sexp::list(items)
}

fn sexp_include_declaration(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    incl: &crate::types::typedtree::IncludeDeclaration,
) -> Sexp {
    let loc_sexp = if cx.with_locs {
        vec![location_idx(arena, cx, incl.incl_loc)]
    } else {
        vec![]
    };
    let mut items = vec![Sexp::atom("include_declaration")];
    items.extend(loc_sexp);
    items.push(sexp_module_expr(arena, ctx, cx, &incl.incl_mod));
    items.push(sexp_attributes(arena, cx, &incl.incl_attributes));
    Sexp::list(items)
}

fn sexp_open_description(
    arena: &ParseArena,
    ctx: &TypeContext,
    cx: Cx<'_>,
    od: &OpenDeclaration,
) -> Sexp {
    let mut items = vec![
        Sexp::atom("open_description"),
        sexp_path(&od.open_path),
        sexp_longident_idx(arena, ctx, od.open_txt.txt),
    ];
    items.push(sexp_override_flag(&od.open_override));
    items.push(sexp_attributes(arena, cx, &od.open_attributes));
    Sexp::list(items)
}

// ============================================================================
// Public API
// ============================================================================

/// Print a typed structure as sexp (without locations)
pub fn print_typed_structure<W: Write>(
    arena: &ParseArena,
    ctx: &TypeContext,
    ta: &TypedArena,
    str: &Structure,
    out: &mut W,
) -> std::io::Result<()> {
    let body = sexp_structure(arena, ctx, Cx::new(ta, false), str);
    write_latin1_line(out, &body.to_string())
}

/// Print a typed structure as sexp (with locations)
pub fn print_typed_structure_with_locs<W: Write>(
    arena: &ParseArena,
    ctx: &TypeContext,
    ta: &TypedArena,
    str: &Structure,
    out: &mut W,
) -> std::io::Result<()> {
    let body = sexp_structure(arena, ctx, Cx::new(ta, true), str);
    write_latin1_line(out, &body.to_string())
}

/// Print a typed signature as sexp (without locations)
pub fn print_typed_signature<W: Write>(
    arena: &ParseArena,
    ctx: &TypeContext,
    ta: &TypedArena,
    sig: &crate::types::typedtree::TypedSignature,
    out: &mut W,
) -> std::io::Result<()> {
    let sexp = sexp_typed_signature(arena, ctx, Cx::new(ta, false), sig);
    write_latin1_line(out, &sexp.to_string())
}

/// Print a typed signature as sexp (with locations)
pub fn print_typed_signature_with_locs<W: Write>(
    arena: &ParseArena,
    ctx: &TypeContext,
    ta: &TypedArena,
    sig: &crate::types::typedtree::TypedSignature,
    out: &mut W,
) -> std::io::Result<()> {
    let sexp = sexp_typed_signature(arena, ctx, Cx::new(ta, true), sig);
    write_latin1_line(out, &sexp.to_string())
}

#[cfg(test)]
mod tests {
    use super::Sexp;

    #[test]
    fn sexp_rendering_layout() {
        let a = |s: &str| Sexp::atom(s);
        assert_eq!(Sexp::list(vec![]).to_string(), "()");
        assert_eq!(Sexp::list(vec![a("x")]).to_string(), "(x)");
        let nested = Sexp::list(vec![
            a("f"),
            Sexp::list(vec![Sexp::list(vec![a("p"), a("q")])]),
            Sexp::list(vec![a("g"), Sexp::list(vec![a("h"), a("i")])]),
        ]);
        assert_eq!(
            nested.to_string(),
            "(f\n  ((p\n    q))\n  (g\n    (h\n      i)))"
        );
    }
}
