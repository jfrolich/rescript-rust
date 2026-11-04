//! ML Printer (OCaml-compatible output)
//!
//! This module provides printing functions that output AST in a format
//! compatible with OCaml's Pprintast module. Uses the OCaml-compatible
//! Format module for proper line breaking with box-based formatting.

use std::io::Write;

use super::ast::*;
use super::formatter::{BoxKind, Formatter};
use super::longident::Longident;
use super::parsetree_viewer;
use crate::parse_arena::{CoreTypeIdx, ExprIdx, LidentIdx, Located, ParseArena, PatIdx, StrIdx};

// ============================================================================
// Print context (matching OCaml's pprintast ctxt)
// ============================================================================

/// Context for expression printing, matching OCaml's pprintast `ctxt` type.
/// Determines when extra parentheses are needed for disambiguation.
#[derive(Debug, Clone, Copy, Default)]
struct PrintCtx {
    pipe: bool,
    semi: bool,
    ifthenelse: bool,
}

impl PrintCtx {
    fn reset() -> Self {
        Self {
            pipe: false,
            semi: false,
            ifthenelse: false,
        }
    }
    fn under_pipe(self) -> Self {
        Self { pipe: true, ..self }
    }
    fn under_semi(self) -> Self {
        Self { semi: true, ..self }
    }
    fn under_ifthenelse(self) -> Self {
        Self {
            ifthenelse: true,
            ..self
        }
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Check if pattern is a simple variable with given name (and no attributes)
fn pattern_is_simple_var(arena: &ParseArena, pat: &Pattern, name: &str) -> bool {
    if !pat.ppat_attributes.is_empty() {
        return false;
    }
    match &pat.ppat_desc {
        PatternDesc::Ppat_var(var) => arena.get_string(var.txt) == name,
        _ => false,
    }
}

/// Check if pattern needs parens when used as a function parameter
fn pattern_needs_parens_as_param(pat: &Pattern, arena: &ParseArena) -> bool {
    match &pat.ppat_desc {
        PatternDesc::Ppat_construct(lid, arg) => {
            match arena.get_longident(lid.txt) {
                // () and [] don't need parens, but :: with args does
                Longident::Lident(name_idx) => {
                    let name = arena.get_string(*name_idx);
                    if name == "()" || name == "[]" {
                        false
                    } else if name == "::" {
                        !arg.txt.is_empty()
                    } else {
                        true
                    }
                }
                _ => true,
            }
        }
        PatternDesc::Ppat_variant(inner) => !inner.1.txt.is_empty(),
        PatternDesc::Ppat_alias(_, _) => true,
        PatternDesc::Ppat_or(_, _) => true,
        _ => false,
    }
}

/// Check if a pattern is "simple" according to OCaml's pprintast.
/// Simple patterns can appear as arguments to variants/constructors without parens.
/// Based on pprintast.ml's simple_pattern function.
fn pattern_is_simple(pat: &Pattern, arena: &ParseArena) -> bool {
    // In OCaml, simple_pattern delegates to pattern when attributes are present.
    // pattern adds ((...)attrs) wrapping, so no extra parens needed.
    if !pat.ppat_attributes.is_empty() {
        return true;
    }
    match &pat.ppat_desc {
        // These are all handled directly by simple_pattern:
        PatternDesc::Ppat_any => true,
        PatternDesc::Ppat_var(_) => true,
        PatternDesc::Ppat_array(_) => true,
        PatternDesc::Ppat_unpack(_) => true,
        PatternDesc::Ppat_type(_) => true,
        PatternDesc::Ppat_record(_) => true,
        PatternDesc::Ppat_tuple(_) => true,
        PatternDesc::Ppat_constant(_) => true,
        PatternDesc::Ppat_interval(_) => true,
        PatternDesc::Ppat_variant(inner) => {
            // Only variant without arg is simple
            inner.1.txt.is_empty()
        }
        PatternDesc::Ppat_constraint(_) => true,
        PatternDesc::Ppat_exception(_) => true,
        PatternDesc::Ppat_extension(_) => true,
        PatternDesc::Ppat_construct(lid, _) => {
            // () and [] are simple, others are not
            match arena.get_longident(lid.txt) {
                Longident::Lident(name_idx) => {
                    let name = arena.get_string(*name_idx);
                    name == "()" || name == "[]"
                }
                _ => false,
            }
        }
        // These are NOT simple - need parens:
        PatternDesc::Ppat_alias(_, _) => false,
        PatternDesc::Ppat_or(_, _) => false,
    }
}

/// Check if a payload is empty (empty PStr)
fn payload_is_empty(payload: &Payload) -> bool {
    matches!(payload, Payload::PStr(items) if items.is_empty())
}

/// Check if a constant is negative (starts with -)
fn constant_is_negative(c: &Constant) -> bool {
    match c {
        Constant::Integer(s, _) | Constant::Float(s, _) => s.starts_with('-'),
        _ => false,
    }
}

/// Check if a string represents an infix operator
fn is_infix_operator(name: &str) -> bool {
    const INFIX_SPECIALS: &[&str] = &[
        ":=", "!=", "::", "mod", "land", "lor", "lxor", "lsl", "lsr", "asr", "or",
    ];
    if INFIX_SPECIALS.contains(&name) {
        return true;
    }
    const INFIX_SYMBOLS: &[char] = &[
        '=', '<', '>', '@', '^', '|', '&', '+', '-', '*', '/', '$', '%', '#',
    ];
    if let Some(c) = name.chars().next() {
        if INFIX_SYMBOLS.contains(&c) {
            return true;
        }
    }
    false
}

/// Check if a string represents a prefix operator
fn is_prefix_operator(name: &str) -> bool {
    const PREFIX_SYMBOLS: &[char] = &['!', '?', '~'];
    if let Some(c) = name.chars().next() {
        PREFIX_SYMBOLS.contains(&c)
    } else {
        false
    }
}

/// Check if an identifier needs parens when printed as a value
/// (OCaml wraps operators in parens when used as values)
fn ident_needs_parens(name: &str) -> bool {
    is_infix_operator(name) || is_prefix_operator(name)
}

/// Get operator name if expression is an identifier that is an operator
fn get_operator_name<'a>(expr: &Expression, arena: &'a ParseArena) -> Option<&'a str> {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => match arena.get_longident(lid.txt) {
            Longident::Lident(name_idx) => Some(arena.get_string(*name_idx)),
            _ => None,
        },
        _ => None,
    }
}

/// Check if a Pexp_construct is a "simple construct" (like OCaml's is_simple_construct)
/// This includes: [], (), complete lists [a; b; c], and simple constructors without args
fn is_simple_construct(expr: &Expression, arena: &ParseArena) -> bool {
    if !expr.pexp_attributes.is_empty() {
        return false;
    }
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_construct(_lid, args) if args.txt.is_empty() => {
            // () and [] and simple constructors are simple
            true
        }
        ExpressionDesc::Pexp_construct(lid, _) => {
            // Check if it's a complete list (ends with [])
            if let Longident::Lident(name_idx) = arena.get_longident(lid.txt) {
                let name = arena.get_string(*name_idx);
                if name == "::" {
                    return list_is_complete(expr, arena);
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if expression is "simple" - doesn't need parens (with arena for complete list checking)
fn is_simple_expression_with_arena(expr: &Expression, arena: &ParseArena) -> bool {
    if !expr.pexp_attributes.is_empty() {
        return false;
    }
    // Check for simple constructs first (handles complete lists)
    if is_simple_construct(expr, arena) {
        return true;
    }
    if let ExpressionDesc::Pexp_variant(v) = &expr.pexp_desc {
        if v.1.txt.is_empty() {
            return true;
        }
    }
    matches!(
        &expr.pexp_desc,
        ExpressionDesc::Pexp_ident(_)
            | ExpressionDesc::Pexp_constant(_)
            | ExpressionDesc::Pexp_tuple(_)
            | ExpressionDesc::Pexp_array(_)
            | ExpressionDesc::Pexp_record(_)
            | ExpressionDesc::Pexp_constraint(_)
            | ExpressionDesc::Pexp_coerce(_)
            | ExpressionDesc::Pexp_pack(_)
            // NOTE: Pexp_field and Pexp_object_* are NOT simple in OCaml's pprintast.
            // They are in expression2, which means they need parens when nested.
            // OCaml's simple_expr handles these directly (no paren wrapping)
            | ExpressionDesc::Pexp_for(_)
            | ExpressionDesc::Pexp_for_of(_)
            | ExpressionDesc::Pexp_for_await_of(_)
            | ExpressionDesc::Pexp_while(_, _)
            | ExpressionDesc::Pexp_jsx_element(_) // JSX elements are simple in OCaml
    )
}

/// Check if expression needs parens in "semi" context (array/list elements)
/// OCaml: when ctxt.semi is true and expr is Pexp_fun/match/try/sequence, wrap in parens
fn needs_parens_in_semi_context(expr: &Expression) -> bool {
    matches!(
        &expr.pexp_desc,
        ExpressionDesc::Pexp_fun(_)
            | ExpressionDesc::Pexp_match(_)
            | ExpressionDesc::Pexp_try(_)
            | ExpressionDesc::Pexp_sequence(_, _)
    )
}

/// Check if expression is "expression2" level - includes Pexp_field and the
/// object get/set/literal nodes
/// These don't need parens when used as binary operands or function arguments.
/// OCaml's pprintast.ml: expression2 handles these directly,
/// then falls through to simple_expr for other cases.
fn is_expression2(expr: &Expression, arena: &ParseArena) -> bool {
    if !expr.pexp_attributes.is_empty() {
        // Attributed expressions need to go through full expression printing
        return false;
    }
    // Expression2 includes field and send expressions
    if matches!(
        &expr.pexp_desc,
        ExpressionDesc::Pexp_field(_, _)
            | ExpressionDesc::Pexp_object_get(_)
            | ExpressionDesc::Pexp_object_set(_)
            | ExpressionDesc::Pexp_object_literal(_)
    ) {
        return true;
    }
    // Plus everything that's simple
    is_simple_expression_with_arena(expr, arena)
}

/// Check if an attribute is internal and should not be printed
fn is_internal_attribute(name: &str) -> bool {
    // Note: "res.await" IS printed (it's the AST marker for await modules)
    // "res.array.access" is internal and should not be printed
    matches!(name, "res.array.access")
}

/// Filter attributes to only include ones that should be printed
fn printable_attributes<'a>(
    arena: &ParseArena,
    attrs: &'a [(Located<StrIdx>, Payload)],
) -> Vec<&'a (Located<StrIdx>, Payload)> {
    attrs
        .iter()
        .filter(|(name, _)| !is_internal_attribute(arena.get_string(name.txt)))
        .collect()
}

/// Check if attributes contain a specific attribute name
fn has_attribute(arena: &ParseArena, attrs: &[(Located<StrIdx>, Payload)], name: &str) -> bool {
    attrs.iter().any(|(n, _)| arena.get_string(n.txt) == name)
}

/// Collect list elements from a cons pattern
/// Whether a `::` spine ends in `[]` with no attributes along the way; the
/// completeness flag of [`collect_list_elements`] without collecting.
fn list_is_complete(expr: &Expression, arena: &ParseArena) -> bool {
    let mut current = expr;
    loop {
        if !current.pexp_attributes.is_empty() {
            return false;
        }
        let ExpressionDesc::Pexp_construct(lid, args) = &current.pexp_desc else {
            return false;
        };
        let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
            return false;
        };
        let name = arena.get_string(*name_idx);
        if args.txt.is_empty() {
            return name == "[]";
        }
        match args.txt.as_slice() {
            [_, tail] if name == "::" => current = arena.get_expr(*tail),
            _ => return false,
        }
    }
}

fn collect_list_elements<'a>(
    expr: &'a Expression,
    arena: &'a ParseArena,
) -> (Vec<&'a Expression>, bool) {
    let mut elements = Vec::new();
    let mut current = expr;

    loop {
        if !current.pexp_attributes.is_empty() {
            elements.push(current);
            return (elements, false);
        }

        match &current.pexp_desc {
            ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => {
                if let Longident::Lident(name_idx) = arena.get_longident(lid.txt) {
                    let name = arena.get_string(*name_idx);
                    if name == "[]" {
                        return (elements, true);
                    }
                }
                elements.push(current);
                return (elements, false);
            }
            ExpressionDesc::Pexp_construct(lid, args) => {
                if let Longident::Lident(name_idx) = arena.get_longident(lid.txt) {
                    let name = arena.get_string(*name_idx);
                    if name == "::"
                        && let [e1, e2] = args.txt.as_slice()
                    {
                        elements.push(arena.get_expr(*e1));
                        current = arena.get_expr(*e2);
                        continue;
                    }
                }
                elements.push(current);
                return (elements, false);
            }
            _ => {
                elements.push(current);
                return (elements, false);
            }
        }
    }
}

// ============================================================================
// Public API
// ============================================================================

/// Print structure in ML format (like Pprintast in OCaml)
pub fn print_structure_ml(structure: &Structure, arena: &ParseArena, out: &mut impl Write) {
    let mut f = Formatter::new(out);
    for (i, item) in structure.iter().enumerate() {
        if i > 0 {
            f.newline();
        }
        print_structure_item(&mut f, arena, item);
    }
    f.flush();
}

/// Print signature in ML format
pub fn print_signature_ml(signature: &[SignatureItem], arena: &ParseArena, out: &mut impl Write) {
    let mut f = Formatter::new(out);
    for (i, item) in signature.iter().enumerate() {
        if i > 0 {
            f.newline(); // Top-level items on separate lines
        }
        print_signature_item(&mut f, arena, item);
    }
    f.flush();
}

// ============================================================================
// Structure items
// ============================================================================

fn print_structure_item<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, item: &StructureItem) {
    match &*item.pstr_desc {
        StructureItemDesc::Pstr_eval(inner) => {
            let (ref expr_idx, ref attrs) = **inner;
            // OCaml: pp f "@[<hov2>;;%a@]%a"
            f.open_box(BoxKind::HOV, 2);
            f.string(";;");
            print_expression_no_outer_parens(f, arena, arena.get_expr(*expr_idx));
            f.close_box();
            print_item_attributes(f, arena, attrs);
        }
        StructureItemDesc::Pstr_value(inner) => {
            let (ref rec_flag, ref bindings) = **inner;
            let rec_str = match rec_flag {
                RecFlag::Recursive => "let rec ",
                RecFlag::Nonrecursive => "let ",
            };
            for (i, binding) in bindings.iter().enumerate() {
                if i > 0 {
                    f.newline();
                }
                // OCaml: @[<2>%s %a%a@]%a
                f.open_box(BoxKind::Box, 2);
                if i > 0 {
                    f.string("and ");
                } else {
                    f.string(rec_str);
                }
                print_value_binding(f, arena, binding.pvb_pat, arena.get_expr(binding.pvb_expr));
                f.close_box();
                // Item attributes are OUTSIDE the box in OCaml
                print_item_attributes(f, arena, &binding.pvb_attributes);
            }
        }
        StructureItemDesc::Pstr_primitive(vd) => {
            // OCaml: pp f "@[<hov2>external@ %a@ :@ %a@]%a"
            f.open_box(BoxKind::HOV, 2);
            f.string("external");
            f.space();
            f.string(arena.get_string(vd.pval_name.txt));
            f.space();
            f.string(":");
            f.space();
            // OCaml value_description: pp f "@[<hov2>%a%a@]"
            // where %a%a = core_type followed by optional "@ =@ primitives"
            f.open_box(BoxKind::HOV, 2);
            print_core_type(f, arena, arena.get_core_type(vd.pval_type));
            print_value_description_prim(f, arena, &vd.pval_prim);
            f.close_box();
            f.close_box();
            print_item_attributes(f, arena, &vd.pval_attributes);
        }
        StructureItemDesc::Pstr_type(inner) => {
            let (ref rec_flag, ref decls) = **inner;
            // OCaml: @[<2>type %a%a%s%s%a@]%a for first, @[<2>and %a@]%a for others
            // Each declaration is wrapped in a box with indent 2
            let rec_str = match rec_flag {
                RecFlag::Recursive => "",
                RecFlag::Nonrecursive => " nonrec",
            };
            for (i, decl) in decls.iter().enumerate() {
                if i > 0 {
                    f.newline();
                }
                // OCaml: @[<2> - Open structural box with indent 2 for type declaration
                f.open_box(BoxKind::Box, 2);
                if i == 0 {
                    f.string("type");
                    f.string(rec_str);
                    f.string(" ");
                } else {
                    f.string("and ");
                }
                print_type_declaration(f, arena, decl);
                f.close_box();
                // OCaml: item attributes (%a) are printed OUTSIDE the @[<2>...@] box
                print_item_attributes(f, arena, &decl.ptype_attributes);
            }
        }
        StructureItemDesc::Pstr_typext(ext) => {
            // OCaml: pp f "@[<2>type %a%a += %a@ %a@]%a"
            // Format: "type t +=  \n  | Foo \n  | Bar"
            f.open_box(BoxKind::HV, 2);
            f.string("type ");
            // Print type params if present
            if !ext.ptyext_params.is_empty() {
                if ext.ptyext_params.len() == 1 {
                    // Single param: no parens, like OCaml's "type _ Tid.t +="
                    print_core_type(f, arena, arena.get_core_type(ext.ptyext_params[0].0));
                    f.string(" ");
                } else {
                    f.string("(");
                    for (i, (ty, _variance)) in ext.ptyext_params.iter().enumerate() {
                        if i > 0 {
                            f.string(",");
                        }
                        print_core_type(f, arena, arena.get_core_type(*ty));
                    }
                    f.string(") ");
                }
            }
            print_longident_idx(f, arena, ext.ptyext_path.txt);
            f.string(" += ");
            if matches!(ext.ptyext_private, PrivateFlag::Private) {
                f.string("private ");
            }
            // Extra space before line break to match OCaml's "+=  \n"
            f.string(" ");
            // Each constructor starts with @\n|@; (newline, pipe, break)
            for ctor in ext.ptyext_constructors.iter() {
                f.newline();
                f.string("| ");
                print_extension_constructor(f, arena, ctor);
            }
            f.close_box();
            print_item_attributes(f, arena, &ext.ptyext_attributes);
        }
        StructureItemDesc::Pstr_exception(ext) => {
            // OCaml: pp f "@[<hov2>exception@ %a@]"
            // OCaml: pp f "@[<hov2>exception@ %a@]"
            f.open_box(BoxKind::HOV, 2);
            f.string("exception");
            f.space(); // @ after "exception"
            print_extension_constructor(f, arena, ext);
            f.close_box();
        }
        StructureItemDesc::Pstr_module(mb) => {
            // OCaml: @[<hov2>module %s%a@]%a
            f.open_box(BoxKind::HOV, 2);
            f.string("module ");
            f.string(arena.get_string(mb.pmb_name.txt));
            // OCaml: module_helper unwraps Pmod_functor with no attributes
            // and prints functor parameters inline: `module F(A:X) = body`
            let mut me = arena.get_mod_expr(mb.pmb_expr);
            while let ModuleExprDesc::Pmod_functor(func_inner) = &*me.pmod_desc {
                let (ref name, ref mt, ref body) = **func_inner;
                if me.pmod_attributes.is_empty() {
                    if let Some(mt) = mt {
                        f.string("(");
                        f.string(arena.get_string(name.txt));
                        f.string(":");
                        print_module_type(f, arena, arena.get_mod_type(*mt));
                        f.string(")");
                    } else {
                        f.string("()");
                    }
                    me = arena.get_mod_expr(*body);
                } else {
                    break;
                }
            }
            // OCaml: special case for Pmod_constraint with ident or signature type
            // prints "module X : mt = me'" instead of "module X = (me' : mt)"
            if let ModuleExprDesc::Pmod_constraint(inner_me, mt) = &*me.pmod_desc {
                let mt_ref = arena.get_mod_type(*mt);
                let is_sugar_type = matches!(
                    *mt_ref.pmty_desc,
                    ModuleTypeDesc::Pmty_ident(..) | ModuleTypeDesc::Pmty_signature(..)
                );
                if is_sugar_type && me.pmod_attributes.is_empty() {
                    f.string(" :");
                    f.space();
                    print_module_type(f, arena, mt_ref);
                    f.space();
                    f.string("=");
                    f.space();
                    print_module_expr(f, arena, arena.get_mod_expr(*inner_me));
                    f.space(); // OCaml: trailing @; produces space
                } else {
                    f.string(" =");
                    f.space();
                    print_module_expr(f, arena, me);
                }
            } else {
                f.string(" =");
                f.space();
                print_module_expr(f, arena, me);
            }
            f.close_box();
            print_item_attributes(f, arena, &mb.pmb_attributes);
        }
        StructureItemDesc::Pstr_recmodule(mbs) => {
            // OCaml: @[<hv>@[<hov2>module rec name:mt = me@]%a @ aux_list@]
            // Outer HV box ensures and-bindings break onto separate lines
            f.open_box(BoxKind::HV, 0);
            for (i, mb) in mbs.iter().enumerate() {
                if i == 0 {
                    f.open_box(BoxKind::HOV, 2);
                    f.string("module rec ");
                } else {
                    // Outer @ break: newline in HV box
                    f.space();
                    // OCaml: @[<hov2>@ and@ ...@] — HOV2 box starting with @ before "and"
                    f.open_box(BoxKind::HOV, 2);
                    f.space(); // @ before "and" — gives 1 space in packing mode
                    f.string("and ");
                }
                f.string(arena.get_string(mb.pmb_name.txt));
                // Check for constraint sugar: `A:Mt = Me` instead of `A = (Me : Mt)`
                let mb_expr = arena.get_mod_expr(mb.pmb_expr);
                if let ModuleExprDesc::Pmod_constraint(me, mt) = &*mb_expr.pmod_desc {
                    f.string(":");
                    print_module_type(f, arena, arena.get_mod_type(*mt));
                    f.space(); // @ before =
                    f.string("=");
                    f.space(); // @ after =
                    print_module_expr(f, arena, arena.get_mod_expr(*me));
                } else {
                    f.space(); // @ before =
                    f.string("=");
                    f.space(); // @ after =
                    print_module_expr(f, arena, mb_expr);
                }
                f.close_box();
                // Print module binding attributes
                print_item_attributes(f, arena, &mb.pmb_attributes);
            }
            f.close_box();
        }
        StructureItemDesc::Pstr_modtype(mtd) => {
            // OCaml: pp f "@[<hov2>module@ type@ %s%a@]%a"
            // where inner is: pp_print_space f (); pp f "@ =@ %a" (module_type ctxt) mt
            // This produces two spaces before = when not breaking: "Sig  ="
            f.open_box(BoxKind::HOV, 2);
            f.string("module");
            f.space();
            f.string("type");
            f.space();
            f.string(arena.get_string(mtd.pmtd_name.txt));
            if let Some(mt) = &mtd.pmtd_type {
                // pp_print_space + "@ =" gives two spaces before =
                f.string(" "); // literal space from pp_print_space
                f.space(); // break hint before =
                f.string("=");
                f.space();
                print_module_type(f, arena, arena.get_mod_type(*mt));
            }
            f.close_box();
            print_item_attributes(f, arena, &mtd.pmtd_attributes);
        }
        StructureItemDesc::Pstr_open(od) => {
            f.string("open");
            if matches!(od.popen_override, OverrideFlag::Override) {
                f.string("!");
            }
            f.string(" ");
            print_longident_idx(f, arena, od.popen_lid.txt);
            print_item_attributes(f, arena, &od.popen_attributes);
        }
        StructureItemDesc::Pstr_include(incl) => {
            // OCaml: @[<hov2>include@ %a@]%a
            f.open_box(BoxKind::HOV, 2);
            f.string("include");
            f.space();
            print_module_expr(f, arena, arena.get_mod_expr(incl.pincl_mod));
            f.close_box();
            print_item_attributes(f, arena, &incl.pincl_attributes);
        }
        StructureItemDesc::Pstr_attribute(attr_inner) => {
            let (ref name, ref payload) = **attr_inner;
            // Standalone/floating attributes use [@@@...] (3 @)
            f.string("[@@@");
            f.string(arena.get_string(name.txt));
            if !payload_is_empty(payload) {
                f.string(" ");
                print_payload(f, arena, payload);
            } else {
                f.string(" ");
            }
            f.string("]");
        }
        StructureItemDesc::Pstr_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            let (ref name, ref payload) = *ext;
            f.open_box(BoxKind::H, 2);
            f.string("[%%");
            f.string(arena.get_string(name.txt));
            f.space();
            print_payload(f, arena, payload);
            f.string("]");
            print_item_attributes(f, arena, attrs);
            f.close_box();
        }
    }
}

// ============================================================================
// Value bindings
// ============================================================================

fn print_value_binding<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    pat_idx: crate::parse_arena::PatIdx,
    expr: &Expression,
) {
    let pat = arena.get_pat(pat_idx);
    // pprintast.ml:1119-1123: `pvb_constraint = Some {pvc_newtypes; pvc_type}`.
    if let Some(constraint) = arena.value_constraint(pat_idx) {
        print_simple_pattern(f, arena, pat);
        f.space();
        f.string(": type");
        f.space();
        for (i, name) in constraint.pvc_newtypes.iter().enumerate() {
            if i > 0 {
                f.space();
            }
            f.string(arena.get_string(name.txt));
        }
        f.string(".");
        f.space();
        print_core_type(f, arena, arena.get_core_type(constraint.pvc_type));
        f.space();
        f.string("=");
        f.space();
        print_expression(f, arena, expr);
        return;
    }
    if !expr.pexp_attributes.is_empty() {
        // OCaml: pp f "%a@;=@;%a" (pattern ctxt) p (expression ctxt) x
        print_pattern(f, arena, pat);
        f.space();
        f.string("=");
        f.space();
        print_expression(f, arena, expr);
        return;
    }

    // Check for desugared locally abstract types (GADT sugar):
    // let f : 'a 'b . type_expr = fun (type a) -> fun (type b) -> (body : type_expr')
    // This gets printed as: let f : type a b. type_expr' = body
    // OCaml pprintast.ml is_desugared_gadt function (lines 1054-1081)
    if let PatternDesc::Ppat_constraint(ppat_inner) = &pat.ppat_desc {
        let (ref inner_pat_idx, ref typ_idx) = **ppat_inner;
        let inner_pat = arena.get_pat(*inner_pat_idx);
        let typ = arena.get_core_type(*typ_idx);
        if pat.ppat_attributes.is_empty() {
            if let CoreTypeDesc::Ptyp_poly(poly_inner) = &typ.ptyp_desc {
                let (ref tyvars, _) = **poly_inner;
                if !tyvars.is_empty() && typ.ptyp_attributes.is_empty() {
                    // Try to match the desugared GADT pattern
                    // Collect Pexp_newtype chain from expression
                    let mut e_tyvars = Vec::new();
                    let mut curr_expr = expr;
                    while let ExpressionDesc::Pexp_newtype(newtype_inner) = &curr_expr.pexp_desc {
                        let (ref tyvar, ref inner_idx) = **newtype_inner;
                        if !curr_expr.pexp_attributes.is_empty() {
                            break;
                        }
                        e_tyvars.push(tyvar.txt);
                        curr_expr = arena.get_expr(*inner_idx);
                    }
                    // Check if we end with Pexp_constraint(Box::new((body, ct))) and tyvars match
                    if let ExpressionDesc::Pexp_constraint(constr_inner) = &curr_expr.pexp_desc {
                        let (ref body_idx, ref ct) = **constr_inner;
                        if curr_expr.pexp_attributes.is_empty() && e_tyvars.len() == tyvars.len() {
                            // Check that tyvar names match (pattern has 'a, expr has a -> same base name)
                            let tyvars_match = tyvars
                                .iter()
                                .zip(e_tyvars.iter())
                                .all(|(pt, et)| pt.txt == *et);
                            if tyvars_match {
                                // Print sugared form: name : type t u v. ct = body
                                // OCaml: %a@;: type@;%a.@;%a@;=@;%a
                                print_simple_pattern(f, arena, inner_pat);
                                f.space();
                                f.string(": type");
                                f.space();
                                for (i, tv) in e_tyvars.iter().enumerate() {
                                    if i > 0 {
                                        f.space();
                                    }
                                    f.string(arena.get_string(*tv));
                                }
                                f.string(".");
                                f.space();
                                print_core_type(f, arena, arena.get_core_type(*ct));
                                f.space();
                                f.string("=");
                                f.space();
                                print_expression(f, arena, arena.get_expr(*body_idx));
                                return;
                            }
                        }
                    }
                }
            }
        }
    }

    // Special case: Ppat_constraint - different handling based on type
    // OCaml pprintast.ml lines 1096-1103
    if let PatternDesc::Ppat_constraint(ppat_inner2) = &pat.ppat_desc {
        let (ref inner_pat_idx, ref typ_idx) = **ppat_inner2;
        let inner_pat = arena.get_pat(*inner_pat_idx);
        let typ = arena.get_core_type(*typ_idx);
        if pat.ppat_attributes.is_empty() {
            if matches!(typ.ptyp_desc, CoreTypeDesc::Ptyp_poly(..))
                && typ.ptyp_attributes.is_empty()
            {
                // Ptyp_poly: print without outer parens
                // OCaml: pp f "%a@;:@;%a@;=@;%a"
                print_simple_pattern(f, arena, inner_pat);
                f.space();
                f.string(":");
                f.space();
                print_core_type(f, arena, typ);
                f.space();
                f.string("=");
                f.space();
                print_expression_no_outer_parens(f, arena, expr);
                return;
            } else {
                // Non-poly: print with outer parens using simple_pattern for inner
                // OCaml: pp f "(%a@;:@;%a)@;=@;%a"
                f.string("(");
                print_simple_pattern(f, arena, inner_pat);
                f.space();
                f.string(":");
                f.space();
                print_core_type(f, arena, typ);
                f.string(")");
                f.space();
                f.string("=");
                f.space();
                print_expression_no_outer_parens(f, arena, expr);
                return;
            }
        }
    }

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun {
                arg_label: _,
                default: _,
                lhs: _,
                rhs: _,
                arity: _,
                is_async: _,
            } = **inner;
            // OCaml `binding`: pp f "%a@ %a" (simple_pattern ctxt) p pp_print_pexp_function x
            // (pprintast.ml:1063-1089).
            print_pattern(f, arena, pat);
            f.space();
            print_pexp_function_head(f, arena, inner);
            let body = print_remaining_inline_params(f, arena, arena.get_expr(inner.rhs));

            // OCaml: pp f "=@;%a" (expression ctxt) x
            f.string("=");
            f.space();
            print_expression_no_outer_parens(f, arena, body);
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (ref name, ref inner_idx) = **inner;
            // Handle locally abstract types at the start: let f (type t) ...
            // OCaml: pp f "%a@ %a" where second %a is pp_print_pexp_function
            // pp_print_pexp_function for Pexp_newtype: pp f "(type@ %s)@ %a"
            print_pattern(f, arena, pat);
            f.space(); // @ between pattern and (type ...)
            f.string("(type");
            f.space(); // @ inside (type@ %s)
            f.string(arena.get_string(name.txt));
            f.string(")");
            f.space(); // @ between ) and next
            // Continue collecting newtypes and print arity when we hit a fun
            let body = print_remaining_inline_params(f, arena, arena.get_expr(*inner_idx));
            // OCaml: pp f "=@;%a" (expression ctxt) x
            f.string("=");
            f.space();
            print_expression_no_outer_parens(f, arena, body);
        }
        _ => {
            // OCaml: pp f "%a@;=@;%a" (pattern ctxt) p (expression ctxt) x
            print_pattern(f, arena, pat);
            f.space();
            f.string("=");
            f.space();
            print_expression_no_outer_parens(f, arena, expr);
        }
    }
}

/// Print a function parameter.
/// For Nolabel: no trailing space (caller adds break)
/// For Labelled/Optional: includes trailing break (@;) to match OCaml's label_exp
fn print_inline_param<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    label: &ArgLabel,
    default: &Option<ExprIdx>,
    pat: &Pattern,
) {
    match label {
        ArgLabel::Nolabel => {
            // OCaml: pp f "%a@ " (simple_pattern ctxt) p
            // The "@ " break is emitted by the caller, not by label_exp for Nolabel
            // Wait - actually for Nolabel, pp_print_pexp_function uses (simple_pattern ctxt) directly,
            // not label_exp. So there's no trailing break from the param itself.
            if pattern_needs_parens_as_param(pat, arena) {
                f.string("(");
                print_pattern(f, arena, pat);
                f.string(")");
            } else {
                print_pattern(f, arena, pat);
            }
        }
        ArgLabel::Labelled(name) => {
            // OCaml label_exp: pp f "~%s@;" l  OR  pp f "~%s:%a@;" l (simple_pattern ctxt) p
            // The trailing @; is Break(1,0)
            let name_str = arena.get_string(name.txt);
            if pattern_is_simple_var(arena, pat, name_str) {
                f.string("~");
                f.string(name_str);
                f.space(); // @; from label_exp
            } else {
                f.string("~");
                f.string(name_str);
                f.string(":");
                print_pattern(f, arena, pat);
                f.space(); // @; from label_exp
            }
        }
        ArgLabel::Optional(name) => {
            // OCaml label_exp: pp f "?(%s=@;%a)@;" OR pp f "?%s:(%a=@;%a)@;" etc.
            // All cases have trailing @; = Break(1,0)
            let name_str = arena.get_string(name.txt);
            if let Some(def) = default {
                let def_expr = arena.get_expr(*def);
                if pattern_is_simple_var(arena, pat, name_str) {
                    f.string("?(");
                    f.string(name_str);
                    f.string("=");
                    f.space(); // =@; inside
                    print_expression(f, arena, def_expr);
                    f.string(")");
                    f.space(); // trailing @;
                } else {
                    f.string("?");
                    f.string(name_str);
                    f.string(":(");
                    print_pattern(f, arena, pat);
                    f.string("=");
                    f.space(); // =@; inside
                    print_expression(f, arena, def_expr);
                    f.string(")");
                    f.space(); // trailing @;
                }
            } else if pattern_is_simple_var(arena, pat, name_str) {
                f.string("?");
                f.string(name_str);
                f.space(); // @; trailing
            } else {
                f.string("?");
                f.string(name_str);
                f.string(":");
                print_pattern(f, arena, pat);
                f.space(); // @; trailing
            }
        }
    }
}

/// Print label_exp with trailing break/space, matching OCaml's label_exp.
/// Used in Pexp_fun expression printing where format breaks are used.
fn print_label_exp_with_break<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    label: &ArgLabel,
    default: &Option<ExprIdx>,
    pat: &Pattern,
) {
    match label {
        ArgLabel::Nolabel => {
            // OCaml: %a@ (simple_pattern + break hint with space)
            print_simple_pattern(f, arena, pat);
            f.space();
        }
        ArgLabel::Labelled(name) => {
            let name_str = arena.get_string(name.txt);
            if pattern_is_simple_var(arena, pat, name_str) {
                // Punned: ~foo@;
                f.string("~");
                f.string(name_str);
                f.space();
            } else {
                // Explicit: ~foo:pattern@;
                f.string("~");
                f.string(name_str);
                f.string(":");
                print_simple_pattern(f, arena, pat);
                f.space();
            }
        }
        ArgLabel::Optional(name) => {
            let name_str = arena.get_string(name.txt);
            if pattern_is_simple_var(arena, pat, name_str) {
                match default {
                    Some(def) => {
                        // ?(%s=@;%a)@;
                        f.string("?(");
                        f.string(name_str);
                        f.string("=");
                        f.space();
                        print_expression(f, arena, arena.get_expr(*def));
                        f.string(")");
                        f.space();
                    }
                    None => {
                        // ?%s@ (note: OCaml uses @ not @; for punned optional)
                        f.string("?");
                        f.string(name_str);
                        f.space();
                    }
                }
            } else {
                match default {
                    Some(def) => {
                        // ?%s:(%a=@;%a)@;
                        f.string("?");
                        f.string(name_str);
                        f.string(":(");
                        print_pattern(f, arena, pat);
                        f.string("=");
                        f.space();
                        print_expression(f, arena, arena.get_expr(*def));
                        f.string(")");
                        f.space();
                    }
                    None => {
                        // ?%s:%a@;
                        f.string("?");
                        f.string(name_str);
                        f.string(":");
                        print_simple_pattern(f, arena, pat);
                        f.space();
                    }
                }
            }
        }
    }
}

/// One `Pexp_fun` step of OCaml `pp_print_pexp_function` (pprintast.ml:1069-1086):
/// "%s%a%s%a" async_str pp_newtypes newtypes arity_str pp_params params.
fn print_pexp_function_head<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, inner: &PexpFun) {
    if inner.is_async {
        f.string("async ");
    }
    for (name, nt_attrs) in arena.nary_fun_newtypes(inner) {
        print_attributes(f, arena, nt_attrs);
        f.string("(type");
        f.space();
        f.string(arena.get_string(name.txt));
        f.string(")");
        f.space();
    }
    if let Some(n) = arena.get_arity(inner.arity) {
        f.string(&format!("[arity:{}]", n));
    }
    if let Some(params) = arena.stored_nary_fun_params(inner) {
        for param in params {
            print_inline_param(
                f,
                arena,
                &param.p_lbl,
                &param.p_default,
                arena.get_pat(param.p_pat),
            );
            f.space();
        }
    } else {
        print_inline_param(
            f,
            arena,
            &inner.arg_label,
            &inner.default,
            arena.get_pat(inner.lhs),
        );
        f.space();
    }
}

/// Helper to print the remaining inline params (`fun` heads and newtypes).
fn print_remaining_inline_params<'a, W: Write>(
    f: &mut Formatter<W>,
    arena: &'a ParseArena,
    expr: &'a Expression,
) -> &'a Expression {
    if !expr.pexp_attributes.is_empty() {
        return expr;
    }

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            print_pexp_function_head(f, arena, inner);
            print_remaining_inline_params(f, arena, arena.get_expr(inner.rhs))
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (ref name, ref inner_idx) = **inner;
            // OCaml: pp f "(type@ %s)@ %a" str.txt pp_print_pexp_function e
            f.string("(type");
            f.space(); // @ inside (type@ %s)
            f.string(arena.get_string(name.txt));
            f.string(")");
            f.space(); // @ between ) and next
            print_remaining_inline_params(f, arena, arena.get_expr(*inner_idx))
        }
        _ => expr,
    }
}

// ============================================================================
// Expressions
// ============================================================================

fn print_expression<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, expr: &Expression) {
    let attrs = printable_attributes(arena, &expr.pexp_attributes);
    let has_attrs = !attrs.is_empty();

    if has_attrs {
        // OCaml Format: pp f "((%a)@,%a)" (expression ctxt) {x with pexp_attributes = []} (attributes ctxt) x.pexp_attributes
        // One cut before ALL attributes (not per-attribute), then attributes are concatenated
        f.string("((");
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
        f.string(")");
        f.cut(); // Single cut before all attributes
        print_attributes(f, arena, &expr.pexp_attributes);
        f.string(")");
    } else {
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
    }
}

fn print_expression_no_outer_parens<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    expr: &Expression,
) {
    let attrs = printable_attributes(arena, &expr.pexp_attributes);
    let has_attrs = !attrs.is_empty();

    if has_attrs {
        // OCaml Format: pp f "((%a)@,%a)" - one cut before all attributes
        f.string("((");
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
        f.string(")");
        f.cut(); // Single cut before all attributes
        print_attributes(f, arena, &expr.pexp_attributes);
        f.string(")");
    } else {
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
    }
}

fn print_expression_simple<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, expr: &Expression) {
    print_expression_simple_ctx(f, arena, expr, PrintCtx::reset());
}

/// Context-aware version of print_expression_simple.
/// In OCaml, `simple_expr ctxt` passes the context through, so when it falls through
/// to `expression ctxt`, context-dependent parenthesization (pipe, semi, ifthenelse) is applied.
fn print_expression_simple_ctx<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    expr: &Expression,
    ctx: PrintCtx,
) {
    // OCaml's simple_expr wraps non-simple expressions in parens
    // BUT: attributed expressions already produce ((expr)[@attr]) structure
    // so we don't add extra parens for them
    let has_attrs = !printable_attributes(arena, &expr.pexp_attributes).is_empty();

    if has_attrs {
        // OCaml: simple_expr for attributed exprs -> expression ctxt -> handles attrs
        print_expression_with_ctx(f, arena, expr, ctx);
    } else if is_simple_expression_with_arena(expr, arena) {
        // Simple expressions print directly (no context needed - they don't produce parens)
        print_expression_with_ctx(f, arena, expr, ctx);
    } else {
        // Non-simple: wrap in parens and call expression with context
        // OCaml's paren + expression boxes create a break opportunity
        f.string("(");
        print_expression_with_ctx(f, arena, expr, ctx);
        f.string(")");
    }
}

/// Context-aware version of print_expression_simple_under_semi.
/// OCaml: `simple_expr (under_semi ctxt)` - applies under_semi to the inherited context.
fn print_expression_simple_under_semi_ctx<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    expr: &Expression,
    ctx: PrintCtx,
) {
    let semi_ctx = ctx.under_semi();
    let has_attrs = !printable_attributes(arena, &expr.pexp_attributes).is_empty();

    if has_attrs {
        // OCaml: expression (under_semi ctxt) for attributed non-simple expressions
        print_expression_with_ctx(f, arena, expr, semi_ctx);
    } else if is_simple_expression_with_arena(expr, arena) {
        print_expression_with_ctx(f, arena, expr, semi_ctx);
    } else {
        f.string("(");
        print_expression_with_ctx(f, arena, expr, semi_ctx);
        f.string(")");
    }
}

/// Context-aware version of print_expression2.
/// In OCaml, `expression2 ctxt` passes the context through.
fn print_expression2_ctx<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    expr: &Expression,
    ctx: PrintCtx,
) {
    let has_attrs = !printable_attributes(arena, &expr.pexp_attributes).is_empty();

    if has_attrs {
        // Attributed expressions go through full expression printing with context
        print_expression_with_ctx(f, arena, expr, ctx);
    } else if is_expression2(expr, arena) {
        // Expression2-level expressions don't need parens
        print_expression_with_ctx(f, arena, expr, ctx);
    } else {
        // Everything else needs parens (falls through from simple_expr)
        f.string("(");
        print_expression_with_ctx(f, arena, expr, ctx);
        f.string(")");
    }
}

/// Print expression under OCaml's `under_semi` context.
/// Only wraps specific types in parens (fun/match/try/sequence, let/letmodule/open/letexception).
/// Everything else goes through normal expression printing.
///
/// OCaml's `expression` function checks attributes FIRST, before context checks.
/// When an attributed expression is in semi context, the attribute handling wraps
/// the expression, and then the inner (unattributed) expression gets the semi parens.
/// This produces `(((seq)))[@attr]` instead of `(((seq))[@attr])`.
fn print_expression_under_semi<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    expr: &Expression,
) {
    let attrs = printable_attributes(arena, &expr.pexp_attributes);
    let has_attrs = !attrs.is_empty();

    if has_attrs {
        // OCaml: attributes are checked first, then the inner expression gets the context check.
        // pp f "((%a)@,%a)" (expression ctxt) {x with pexp_attributes=[]} (attributes ctxt) x.pexp_attributes
        // The inner call to `expression ctxt` will then hit the semi context check.
        f.string("((");
        // Print the inner expression with semi context (attrs stripped)
        print_expression_under_semi_inner(f, arena, expr);
        f.string(")");
        f.cut();
        print_attributes(f, arena, &expr.pexp_attributes);
        f.string(")");
    } else {
        let needs_semi_parens = needs_parens_in_semi_context(expr);
        let needs_let_parens = matches!(
            &expr.pexp_desc,
            ExpressionDesc::Pexp_let(_)
                | ExpressionDesc::Pexp_letmodule(_)
                | ExpressionDesc::Pexp_open(_)
                | ExpressionDesc::Pexp_letexception(_)
        );
        if needs_semi_parens || needs_let_parens {
            // OCaml: paren true (expression reset_ctxt) f x
            f.string("(");
            print_expression(f, arena, expr);
            f.string(")");
        } else {
            print_expression(f, arena, expr);
        }
    }
}

/// Helper: print the inner expression (ignoring its attributes) under semi context.
/// This replicates OCaml's behavior where `expression ctxt` is called with attrs stripped,
/// and the semi context check then applies to the unattributed expression.
fn print_expression_under_semi_inner<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    expr: &Expression,
) {
    let needs_semi_parens = needs_parens_in_semi_context(expr);
    let needs_let_parens = matches!(
        &expr.pexp_desc,
        ExpressionDesc::Pexp_let(_)
            | ExpressionDesc::Pexp_letmodule(_)
            | ExpressionDesc::Pexp_open(_)
            | ExpressionDesc::Pexp_letexception(_)
    );
    if needs_semi_parens || needs_let_parens {
        // paren true (expression reset_ctxt) f x
        f.string("(");
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
        f.string(")");
    } else {
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
    }
}

fn print_expression_with_ctx<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    expr: &Expression,
    ctx: PrintCtx,
) {
    let attrs = printable_attributes(arena, &expr.pexp_attributes);
    let has_attrs = !attrs.is_empty();

    if has_attrs {
        f.string("((");
        print_expression_inner(f, arena, expr, false, ctx);
        f.string(")");
        f.cut();
        print_attributes(f, arena, &expr.pexp_attributes);
        f.string(")");
    } else {
        print_expression_inner(f, arena, expr, false, ctx);
    }
}

fn print_expression_inner<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    expr: &Expression,
    use_parens: bool,
    ctx: PrintCtx,
) {
    // Context-dependent parenthesization (matching OCaml's pprintast lines 606-615)
    if (ctx.pipe || ctx.semi)
        && matches!(
            &expr.pexp_desc,
            ExpressionDesc::Pexp_fun(_)
                | ExpressionDesc::Pexp_match(_)
                | ExpressionDesc::Pexp_try(_)
                | ExpressionDesc::Pexp_sequence(_, _)
        )
    {
        if use_parens {
            f.string("(");
        }
        f.string("(");
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
        f.string(")");
        if use_parens {
            f.string(")");
        }
        return;
    }
    if ctx.ifthenelse
        && matches!(
            &expr.pexp_desc,
            ExpressionDesc::Pexp_ifthenelse(_)
                | ExpressionDesc::Pexp_ternary(_)
                | ExpressionDesc::Pexp_sequence(_, _)
        )
    {
        if use_parens {
            f.string("(");
        }
        f.string("(");
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
        f.string(")");
        if use_parens {
            f.string(")");
        }
        return;
    }
    if ctx.semi
        && matches!(
            &expr.pexp_desc,
            ExpressionDesc::Pexp_let(_)
                | ExpressionDesc::Pexp_letmodule(_)
                | ExpressionDesc::Pexp_open(_)
                | ExpressionDesc::Pexp_letexception(_)
        )
    {
        if use_parens {
            f.string("(");
        }
        f.string("(");
        print_expression_inner(f, arena, expr, false, PrintCtx::reset());
        f.string(")");
        if use_parens {
            f.string(")");
        }
        return;
    }

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => {
            // OCaml wraps operators in parens when used as values
            if let Longident::Lident(name_idx) = arena.get_longident(lid.txt) {
                let name = arena.get_string(*name_idx);
                if ident_needs_parens(name) {
                    f.string("(");
                    f.string(name);
                    f.string(")");
                    return;
                }
            }
            print_longident_idx(f, arena, lid.txt);
        }
        ExpressionDesc::Pexp_constant(c) => {
            let is_negative = match &**c {
                Constant::Integer(s, _) | Constant::Float(s, _) => s.starts_with('-'),
                _ => false,
            };
            if is_negative {
                f.string("(");
            }
            print_constant(f, c);
            if is_negative {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_break => {
            f.string("break");
        }
        ExpressionDesc::Pexp_continue => {
            f.string("continue");
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (ref rec_flag, ref bindings, ref body) = **inner;
            // OCaml: @[<2>%a in@;<1 -2>%a@]
            // where %a is (bindings reset_ctxt) (rf, l) and (expression ctxt) e
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::Box, 2);
            // OCaml: @[<2>%a in@;<1 -2>%a@]
            // where %a is (bindings reset_ctxt) (rf, l)
            // bindings wraps each binding in @[<2>kwd binding@]
            let rec_str = match rec_flag {
                RecFlag::Recursive => "let rec ",
                RecFlag::Nonrecursive => "let ",
            };
            for (i, binding) in bindings.iter().enumerate() {
                // OCaml bindings: pp f "@[<2>%s %a%a@]%a"
                f.open_box(BoxKind::Box, 2);
                if i > 0 {
                    f.newline();
                    f.string("and ");
                } else {
                    f.string(rec_str);
                }
                print_value_binding(f, arena, binding.pvb_pat, arena.get_expr(binding.pvb_expr));
                f.close_box();
                // Item attributes are outside the binding box in OCaml
                print_item_attributes(f, arena, &binding.pvb_attributes);
            }
            f.string(" in");
            f.break_(1, -2); // @;<1 -2> - space or newline with -2 indent offset
            print_expression_with_ctx(f, arena, arena.get_expr(*body), ctx);
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun {
                ref arg_label,
                ref default,
                ref lhs,
                ref rhs,
                ref arity,
                ref is_async,
            } = **inner;
            // OCaml: arity is only printed when explicitly set, not computed
            // Look up arity from arena (Arity is now ArityIdx)
            let arity_value = arena.get_arity(*arity).map(|n| n as usize);
            if use_parens {
                f.string("(");
            }
            // OCaml: @[<2>%sfun@;%s%a->@;%a@]
            f.open_box(BoxKind::Box, 2);
            if *is_async {
                f.string("async ");
            }
            f.string("fun");
            f.space();
            // OCaml `pp_newtypes`: "%a(type %s)@;" (pprintast.ml:633-638).
            for (name, nt_attrs) in arena.nary_fun_newtypes(inner) {
                print_attributes(f, arena, nt_attrs);
                f.string("(type ");
                f.string(arena.get_string(name.txt));
                f.string(")");
                f.space();
            }
            if let Some(n) = arity_value {
                f.string(&format!("[arity:{}]", n));
            }
            // OCaml's label_exp prints each param + trailing break/space.
            if let Some(params) = arena.stored_nary_fun_params(inner) {
                for param in params {
                    print_label_exp_with_break(
                        f,
                        arena,
                        &param.p_lbl,
                        &param.p_default,
                        arena.get_pat(param.p_pat),
                    );
                }
            } else {
                print_label_exp_with_break(f, arena, arg_label, default, arena.get_pat(*lhs));
            }
            f.string("->");
            f.space();
            print_expression(f, arena, arena.get_expr(*rhs));
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ref partial,
                ..
            } = **inner;
            // Array access: Array.get(arr, idx) -> arr.(idx)
            // Also handles @res.array.access attribute for backwards compatibility
            // OCaml uses simple_expr for the array expression and expression for the index
            if (parsetree_viewer::is_array_access(arena, expr)
                || has_attribute(arena, &expr.pexp_attributes, "res.array.access"))
                && args.len() == 2
            {
                let (_, arr) = &args[0];
                let (_, idx) = &args[1];
                if use_parens {
                    f.string("(");
                }
                // OCaml: (simple_expr ctxt) a for the array expression
                print_expression_simple_ctx(f, arena, arena.get_expr(*arr), ctx);
                f.string(".(");
                print_expression(f, arena, arena.get_expr(*idx));
                f.string(")");
                if use_parens {
                    f.string(")");
                }
                return;
            }
            // Array set: Array.set(arr, idx, val) -> arr.(idx) <- val
            // OCaml uses simple_expr for both array and value expressions
            if parsetree_viewer::is_array_set(arena, expr) && args.len() == 3 {
                let (_, arr) = &args[0];
                let (_, idx) = &args[1];
                let (_, val) = &args[2];
                if use_parens {
                    f.string("(");
                }
                // OCaml: (simple_expr ctxt) a for the array expression
                print_expression_simple_ctx(f, arena, arena.get_expr(*arr), ctx);
                f.string(".(");
                print_expression(f, arena, arena.get_expr(*idx));
                f.string(") <- ");
                // OCaml: (simple_expr ctxt) v for the value expression
                print_expression_simple_ctx(f, arena, arena.get_expr(*val), ctx);
                if use_parens {
                    f.string(")");
                }
                return;
            }

            // Infix/prefix operators
            let funct_expr = arena.get_expr(*funct);
            if let Some(op_name) = get_operator_name(funct_expr, arena) {
                if is_infix_operator(op_name) && args.len() == 2 {
                    let (_, lhs) = &args[0];
                    let (_, rhs) = &args[1];
                    if use_parens {
                        f.string("(");
                    }
                    f.open_box(BoxKind::Box, 2);
                    // OCaml: arg1 uses (label_x_expression_param reset_ctxt), arg2 uses (label_x_expression_param ctxt)
                    print_expression2_ctx(f, arena, arena.get_expr(*lhs), PrintCtx::reset());
                    f.space();
                    f.string(op_name);
                    f.space();
                    print_expression2_ctx(f, arena, arena.get_expr(*rhs), ctx);
                    if *partial {
                        f.string(" ...");
                    }
                    f.close_box();
                    if use_parens {
                        f.string(")");
                    }
                    return;
                } else if is_prefix_operator(op_name) && args.len() == 1 {
                    let (_, arg_idx) = &args[0];
                    let arg = arena.get_expr(*arg_idx);
                    // OCaml converts ~-, ~+, ~-., ~+., ~~ to shorter forms unless arg is a constant
                    // (to avoid (- 1) being parsed as negative literal)
                    let shortened_op = match op_name {
                        "~-" | "~+" | "~-." | "~+." | "~~" => {
                            if !matches!(&arg.pexp_desc, ExpressionDesc::Pexp_constant(_)) {
                                &op_name[1..] // Remove leading ~
                            } else {
                                op_name
                            }
                        }
                        _ => op_name,
                    };
                    // OCaml: @[<2>%s@;%a@] - no outer parens, uses (simple_expr ctxt)
                    f.open_box(BoxKind::Box, 2);
                    f.string(shortened_op);
                    f.space();
                    print_expression_simple_ctx(f, arena, arg, ctx);
                    if *partial {
                        f.string(" ...");
                    }
                    f.close_box();
                    return;
                }
            }

            // Default: prefix application
            // OCaml: pp f "%a@ %a" (expression2 ctxt) e (list (label_x_expression_param reset_ctxt)) l
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::HOV, 2);
            // OCaml uses (expression2 ctxt) for the function expression
            print_expression2_ctx(f, arena, funct_expr, ctx);
            for (label, arg_idx) in args {
                f.space(); // Break hint between func and args
                // OCaml uses (label_x_expression_param reset_ctxt) for all args in normal apply
                print_arg_with_label_ctx(
                    f,
                    arena,
                    label,
                    arena.get_expr(*arg_idx),
                    PrintCtx::reset(),
                );
            }
            if *partial {
                f.string(" ...");
            }
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_match(inner) => {
            let (ref scrutinee, ref cases) = **inner;
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::HV, 0);
            f.open_box(BoxKind::HV, 0);
            f.open_box(BoxKind::Box, 2);
            f.string("match ");
            print_expression(f, arena, arena.get_expr(*scrutinee));
            f.close_box();
            f.space();
            f.string("with");
            f.close_box();
            for case in cases {
                f.space();
                f.string("| ");
                // OCaml: @[<2>%a%a@;->@;%a@]
                f.open_box(BoxKind::Box, 2);
                print_pattern(f, arena, arena.get_pat(case.pc_lhs));
                if let Some(guard) = &case.pc_guard {
                    // OCaml: (option (expression ctxt) ~first:"@;when@;")
                    f.space(); // @; before "when"
                    f.string("when");
                    f.space(); // @; after "when"
                    print_expression(f, arena, arena.get_expr(*guard));
                }
                f.space();
                f.string("->");
                f.space();
                // OCaml uses (expression (under_pipe ctxt)) for case RHS,
                // which wraps Pexp_fun/match/try/sequence in parens
                print_expression_with_ctx(f, arena, arena.get_expr(case.pc_rhs), ctx.under_pipe());
                f.close_box();
            }
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_try(inner) => {
            let (ref body, ref cases) = **inner;
            if use_parens {
                f.string("(");
            }
            // OCaml: @[<0>@[<hv2>try@ %a@]@ @[<0>with%a@]@]
            f.open_box(BoxKind::Box, 0);
            f.open_box(BoxKind::HV, 2);
            f.string("try");
            f.space(); // @ break between try and body
            print_expression(f, arena, arena.get_expr(*body));
            f.close_box();
            f.space(); // @ break between try-box and with-box
            f.open_box(BoxKind::Box, 0);
            f.string("with");
            for case in cases {
                f.space();
                f.string("| ");
                f.open_box(BoxKind::Box, 2);
                print_pattern(f, arena, arena.get_pat(case.pc_lhs));
                if let Some(guard) = &case.pc_guard {
                    f.space(); // @; before "when"
                    f.string("when");
                    f.space(); // @; after "when"
                    print_expression(f, arena, arena.get_expr(*guard));
                }
                f.string(" -> ");
                // OCaml uses (expression (under_pipe ctxt)) for case RHS
                print_expression_with_ctx(f, arena, arena.get_expr(case.pc_rhs), ctx.under_pipe());
                f.close_box();
            }
            f.close_box();
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_tuple(exprs) => {
            print_expr_tuple(f, arena, exprs, ctx);
        }
        ExpressionDesc::Pexp_construct(lid, arg) => {
            // Special handling for list syntax
            if let Longident::Lident(name_idx) = arena.get_longident(lid.txt) {
                let name = arena.get_string(*name_idx);
                if name == "::" {
                    let (elements, is_complete) = collect_list_elements(expr, arena);
                    if is_complete && !elements.is_empty() {
                        // OCaml: @[<hv0>[%a]@] with expression (under_semi ctxt) and sep ";@;"
                        f.open_box(BoxKind::HV, 0);
                        f.string("[");
                        for (i, elem) in elements.iter().enumerate() {
                            if i > 0 {
                                f.string(";");
                                f.space();
                            }
                            // OCaml uses expression (under_semi), NOT simple_expr
                            print_expression_under_semi(f, arena, elem);
                        }
                        f.string("]");
                        f.close_box();
                        return;
                    }
                    // Non-complete list: a :: b :: expr
                    // OCaml: list (simple_expr ctxt) ~sep:"@;::@;"
                    for (i, elem) in elements.iter().enumerate() {
                        if i > 0 {
                            f.space();
                            f.string("::");
                            f.space();
                        }
                        print_expression_simple_ctx(f, arena, elem, ctx);
                    }
                    return;
                } else if name == "[]" {
                    f.string("[]");
                    return;
                } else if name == "()" {
                    f.string("()");
                    return;
                }
            }
            match arg.txt.as_slice() {
                [] => print_longident_idx(f, arena, lid.txt),
                args => {
                    // OCaml: @[<2>%a@;%a@] with (simple_expr ctxt) for arg
                    f.open_box(BoxKind::Box, 2);
                    print_longident_idx(f, arena, lid.txt);
                    f.space();
                    match args {
                        [a] => print_expression_simple_ctx(f, arena, arena.get_expr(*a), ctx),
                        args => print_expr_tuple(f, arena, args, ctx),
                    }
                    f.close_box();
                }
            }
        }
        ExpressionDesc::Pexp_variant(inner) => {
            let (ref label, ref arg) = **inner;
            if !arg.txt.is_empty() {
                // OCaml: @[<2>`%s@;%a@] with (simple_expr ctxt) for arg
                f.open_box(BoxKind::Box, 2);
                f.string("`");
                f.string(label);
                f.space();
                match arg.txt.as_slice() {
                    [a] => print_expression_simple_ctx(f, arena, arena.get_expr(*a), ctx),
                    args => print_expr_tuple(f, arena, args, ctx),
                }
                f.close_box();
            } else {
                f.string("`");
                f.string(label);
            }
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (ref fields, ref base) = **inner;
            // OCaml: pp f "@[<hv0>@[<hv2>{@;%a%a@]@;}@]"
            f.open_box(BoxKind::HV, 0);
            f.open_box(BoxKind::HV, 2);
            f.string("{");
            f.space(); // @; after {
            if let Some(b) = base {
                print_expression_simple_ctx(f, arena, arena.get_expr(*b), ctx);
                f.string(" with");
                f.space(); // @; after "with"
            }
            for (i, field) in fields.iter().enumerate() {
                if i > 0 {
                    f.string(";");
                    f.space(); // ;@; separator
                }
                // Check for punning: { a } is shorthand for { a = a }
                // OCaml only uses punning when field is Lident (not qualified)
                let lid = arena.get_longident(field.lid.txt);
                let is_punned = if let Longident::Lident(name_idx) = lid {
                    let fname = arena.get_string(*name_idx);
                    // Check if expression is Pexp_ident(Lident(fname))
                    let field_expr = arena.get_expr(field.expr);
                    if let ExpressionDesc::Pexp_ident(expr_lid) = &field_expr.pexp_desc {
                        match arena.get_longident(expr_lid.txt) {
                            Longident::Lident(var_idx) => arena.get_string(*var_idx) == fname,
                            _ => false,
                        }
                    } else {
                        false
                    }
                } else {
                    false
                };

                if is_punned {
                    // OCaml: pp f "@[<hov2>%a%s@]"
                    f.open_box(BoxKind::HOV, 2);
                    print_longident_idx(f, arena, field.lid.txt);
                    if field.opt {
                        f.string("?"); // Optional punned field: name?
                    }
                    f.close_box();
                } else {
                    // OCaml: pp f "@[<hov2>%a@;=@;%s%a@]"
                    f.open_box(BoxKind::HOV, 2);
                    print_longident_idx(f, arena, field.lid.txt);
                    f.space(); // @; before =
                    f.string("=");
                    f.space(); // @; after =
                    if field.opt {
                        f.string("?"); // Optional field: name = ?value
                    }
                    // OCaml uses (simple_expr ctxt) for record field values
                    print_expression_simple_ctx(f, arena, arena.get_expr(field.expr), ctx);
                    f.close_box();
                }
            }
            f.close_box();
            f.space(); // @; before }
            f.string("}");
            f.close_box();
        }
        ExpressionDesc::Pexp_field(obj, field) => {
            // OCaml expression2: pp f "@[<hov2>%a.%a@]" (simple_expr ctxt) e longident_loc li
            f.open_box(BoxKind::HOV, 2);
            print_expression_simple_ctx(f, arena, arena.get_expr(*obj), ctx);
            f.string(".");
            print_longident_idx(f, arena, field.txt);
            f.close_box();
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (ref obj, ref field, ref value) = **inner;
            // OCaml: pp f "@[<2>%a.%a@ <-@ %a@]" (simple_expr ctxt) e1 longident_loc li (simple_expr ctxt) e2
            // Note: uses simple_expr ctxt for both object and value
            print_expression_simple_ctx(f, arena, arena.get_expr(*obj), ctx);
            f.string(".");
            print_longident_idx(f, arena, field.txt);
            f.string(" <- ");
            print_expression_simple_ctx(f, arena, arena.get_expr(*value), ctx);
        }
        ExpressionDesc::Pexp_array(elems) => {
            // OCaml: @[<0>@[<2>[|%a|]@]@] with (list (simple_expr (under_semi ctxt)) ~sep:";")
            f.open_box(BoxKind::Box, 0);
            f.open_box(BoxKind::Box, 2);
            f.string("[|");
            for (i, e) in elems.iter().enumerate() {
                if i > 0 {
                    f.string(";");
                }
                print_expression_simple_under_semi_ctx(f, arena, arena.get_expr(*e), ctx);
            }
            f.string("|]");
            f.close_box();
            f.close_box();
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (ref cond, ref then_expr, ref else_expr) = **inner;
            if use_parens {
                f.string("(");
            }
            // OCaml: @[<hv0>@[<2>if@ %a@]@;@[<2>then@ %a@]%a@]
            // Both condition and then body use expression (under_ifthenelse ctxt)
            f.open_box(BoxKind::HV, 0);
            f.open_box(BoxKind::Box, 2);
            f.string("if");
            f.space(); // @ break between if and condition
            print_expression_with_ctx(f, arena, arena.get_expr(*cond), ctx.under_ifthenelse());
            f.close_box();
            f.space(); // @; break between if-box and then-box
            f.open_box(BoxKind::Box, 2);
            f.string("then");
            f.space(); // @ break between then and body
            print_expression_with_ctx(f, arena, arena.get_expr(*then_expr), ctx.under_ifthenelse());
            f.close_box();
            if let Some(e) = else_expr {
                f.space(); // @; break before else
                f.open_box(BoxKind::Box, 2);
                f.string("else");
                f.space(); // @; break between else and body
                // OCaml: expression (under_semi ctxt) for else body
                print_expression_with_ctx(f, arena, arena.get_expr(*e), ctx.under_semi());
                f.close_box();
            }
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_ternary(inner) => {
            let (cond, consequent, alternate) = **inner;
            if use_parens {
                f.string("(");
            }
            // OCaml: @[<2>%a@ ?@ %a@ :@ %a@]
            f.open_box(BoxKind::Box, 2);
            print_expression_simple_ctx(f, arena, arena.get_expr(cond), ctx);
            f.space();
            f.string("?");
            f.space();
            print_expression_with_ctx(f, arena, arena.get_expr(consequent), PrintCtx::reset());
            f.space();
            f.string(":");
            f.space();
            print_expression_with_ctx(f, arena, arena.get_expr(alternate), PrintCtx::reset());
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_regexp(regexp) => {
            if use_parens {
                f.string("(");
            }
            f.string("/");
            f.string(&regexp.pattern);
            f.string("/");
            f.string(&regexp.flags);
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_braces(braces) => {
            if use_parens {
                f.string("(");
            }
            // OCaml: {%a} with the enclosing context.
            f.string("{");
            print_expression_with_ctx(f, arena, arena.get_expr(braces.expr), ctx);
            f.string("}");
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_sequence(e1, e2) => {
            if use_parens {
                f.string("(");
            }
            // OCaml: flatten sequence chain and print with @[<hv>%a@] and ";@;" separator
            // Uses expression (under_semi ctxt) for each element
            let mut elements: Vec<&Expression> = Vec::new();
            // Collect flattened sequence elements (only unfold non-attributed sequences)
            elements.push(arena.get_expr(*e1));
            let mut rest = arena.get_expr(*e2);
            loop {
                match &rest.pexp_desc {
                    ExpressionDesc::Pexp_sequence(next_e1, next_e2)
                        if rest.pexp_attributes.is_empty() =>
                    {
                        elements.push(arena.get_expr(*next_e1));
                        rest = arena.get_expr(*next_e2);
                    }
                    _ => {
                        elements.push(rest);
                        break;
                    }
                }
            }
            // Print in HV box: horizontal if fits, vertical otherwise
            f.open_box(BoxKind::HV, 0);
            for (i, elem) in elements.iter().enumerate() {
                // OCaml: each element uses expression (under_semi ctxt)
                // under_semi only wraps specific types in parens, NOT all non-simple exprs
                print_expression_with_ctx(f, arena, elem, ctx.under_semi());
                if i < elements.len() - 1 {
                    f.string(";");
                    f.space(); // ";@;" separator
                }
            }
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_while(cond, body) => {
            // OCaml: @[<2>while@;%a@;do@;%a@;done@]
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::Box, 2);
            f.string("while");
            f.space();
            print_expression(f, arena, arena.get_expr(*cond));
            f.space();
            f.string("do");
            f.space();
            print_expression(f, arena, arena.get_expr(*body));
            f.space();
            f.string("done");
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (ref pat, ref start, ref end, ref dir, ref body) = **inner;
            // OCaml: @[<hv0>@[<hv2>@[<2>for %a =@;%a@;%a%a@;do@]@;%a@]@;done@]
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::HV, 0);
            f.open_box(BoxKind::HV, 2);
            f.open_box(BoxKind::Box, 2);
            f.string("for ");
            print_pattern(f, arena, arena.get_pat(*pat));
            f.string(" =");
            f.space();
            print_expression(f, arena, arena.get_expr(*start));
            f.space();
            let dir_str = match dir {
                DirectionFlag::Upto => "to",
                DirectionFlag::Downto => "downto",
            };
            f.string(dir_str);
            f.space();
            print_expression(f, arena, arena.get_expr(*end));
            f.space();
            f.string("do");
            f.close_box();
            f.space();
            print_expression(f, arena, arena.get_expr(*body));
            f.close_box();
            f.space();
            f.string("done");
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            let (ref pat, ref iterable, ref body) = **inner;
            let is_await = matches!(&expr.pexp_desc, ExpressionDesc::Pexp_for_await_of(_));
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::HV, 0);
            f.open_box(BoxKind::HV, 2);
            f.open_box(BoxKind::Box, 2);
            if is_await {
                f.string("for await ");
            } else {
                f.string("for ");
            }
            print_pattern(f, arena, arena.get_pat(*pat));
            f.string(" of");
            f.space();
            print_expression(f, arena, arena.get_expr(*iterable));
            f.space();
            f.string("do");
            f.close_box();
            f.space();
            print_expression(f, arena, arena.get_expr(*body));
            f.close_box();
            f.space();
            f.string("done");
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref e, ref t) = **inner;
            // OCaml: (%a :@ %a)
            f.string("(");
            print_expression(f, arena, arena.get_expr(*e));
            f.string(" :");
            f.space();
            print_core_type(f, arena, arena.get_core_type(*t));
            f.string(")");
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (ref e, ref t1, ref t2) = **inner;
            f.string("(");
            print_expression(f, arena, arena.get_expr(*e));
            if let Some(t) = t1 {
                f.string(" : ");
                print_core_type(f, arena, arena.get_core_type(*t));
            }
            f.string(" :> ");
            print_core_type(f, arena, arena.get_core_type(*t2));
            f.string(")");
        }
        ExpressionDesc::Pexp_object_get(inner) => {
            let (ref e, ref name) = **inner;
            // OCaml: pp f "@[<hov2>%a[\"%s\"]@]" (simple_expr ctxt) e s.txt
            f.open_box(BoxKind::HOV, 2);
            print_expression_simple_ctx(f, arena, arena.get_expr(*e), ctx);
            f.string("[\"");
            f.string(&name.txt);
            f.string("\"]");
            f.close_box();
        }
        ExpressionDesc::Pexp_object_set(inner) => {
            let (ref e, ref name, ref v) = **inner;
            // OCaml: pp f "@[<hov2>%a[\"%s\"] =@ %a@]" (simple_expr ctxt) e s.txt
            //   (expression ctxt) v
            f.open_box(BoxKind::HOV, 2);
            print_expression_simple_ctx(f, arena, arena.get_expr(*e), ctx);
            f.string("[\"");
            f.string(&name.txt);
            f.string("\"] =");
            f.space();
            print_expression_with_ctx(f, arena, arena.get_expr(*v), ctx);
            f.close_box();
        }
        ExpressionDesc::Pexp_object_literal(fields) => {
            // OCaml: pp f "@[<hov2>{%a}@]" (list ~sep:",@ " (fun f (s, e) ->
            //   pp f "@[<hov2>\"%s\":@ %a@]" s.txt (expression ctxt) e)) fields
            f.open_box(BoxKind::HOV, 2);
            f.string("{");
            for (i, (name, e)) in fields.iter().enumerate() {
                if i > 0 {
                    f.string(",");
                    f.space();
                }
                f.open_box(BoxKind::HOV, 2);
                f.string("\"");
                f.string(&name.txt);
                f.string("\":");
                f.space();
                print_expression_with_ctx(f, arena, arena.get_expr(*e), ctx);
                f.close_box();
            }
            f.string("}");
            f.close_box();
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (ref name, ref mexpr, ref body) = **inner;
            // OCaml: pp f "@[<hov2>let@ module@ %s@ =@ %a@ in@ %a@]"
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::HOV, 2);
            f.string("let");
            f.space();
            f.string("module");
            f.space();
            f.string(arena.get_string(name.txt));
            f.space();
            f.string("=");
            f.space();
            print_module_expr(f, arena, arena.get_mod_expr(*mexpr));
            f.space();
            f.string("in");
            f.space();
            print_expression_with_ctx(f, arena, arena.get_expr(*body), ctx);
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (ref ext, ref body) = **inner;
            // OCaml: pp f "@[<hov2>let@ exception@ %a@ in@ %a@]"
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::HOV, 2);
            f.string("let");
            f.space();
            f.string("exception");
            f.space();
            print_extension_constructor(f, arena, ext);
            f.space();
            f.string("in");
            f.space();
            print_expression_with_ctx(f, arena, arena.get_expr(*body), ctx);
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_assert(e) => {
            // OCaml: @[<hov2>assert@ %a@] - no parens
            // Parens come from (simple_expr ctxt) when needed
            f.open_box(BoxKind::HOV, 2);
            f.string("assert ");
            print_expression_simple_ctx(f, arena, arena.get_expr(*e), ctx);
            f.close_box();
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (ref name, ref body) = **inner;
            // OCaml: pp f "fun@;(type@;%s)@;->@;%a"
            f.string("fun");
            f.space(); // @; after "fun"
            f.string("(type");
            f.space(); // @; after "(type"
            f.string(arena.get_string(name.txt));
            f.string(")");
            f.space(); // @; after ")"
            f.string("->");
            f.space(); // @; after "->"
            print_expression(f, arena, arena.get_expr(*body));
        }
        ExpressionDesc::Pexp_pack(mexpr) => {
            // OCaml: pp f "(module@;%a)" (module_expr ctxt) me
            f.string("(module");
            f.space(); // @; after "(module"
            print_module_expr(f, arena, arena.get_mod_expr(*mexpr));
            f.string(")");
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (ref override_flag, ref lid, ref body) = **inner;
            // OCaml: pp f "@[<2>let open%s %a in@;%a@]"
            if use_parens {
                f.string("(");
            }
            f.open_box(BoxKind::Box, 2);
            f.string("let open");
            if matches!(override_flag, OverrideFlag::Override) {
                f.string("!");
            }
            f.string(" ");
            print_longident_idx(f, arena, lid.txt);
            f.string(" in");
            f.space(); // @;
            print_expression_with_ctx(f, arena, arena.get_expr(*body), ctx);
            f.close_box();
            if use_parens {
                f.string(")");
            }
        }
        ExpressionDesc::Pexp_extension(ext_inner) => {
            let (ref name, ref payload) = **ext_inner;
            // OCaml: @[<2>[%%%s@ %a]@] — structural box with indent 2
            f.open_box(BoxKind::Box, 2);
            f.string("[%");
            f.string(arena.get_string(name.txt));
            f.space();
            print_payload(f, arena, payload);
            f.string("]");
            f.close_box();
        }
        ExpressionDesc::Pexp_template(template) => {
            // OCaml pprintast: pp f "`%a`" parts, each part "%s${%a}%a".
            f.string("`");
            print_template_parts(f, arena, &template.source_segments, &template.values, ctx);
            f.string("`");
        }
        ExpressionDesc::Pexp_tagged_template(template) => {
            print_expression_simple_ctx(f, arena, arena.get_expr(template.tag), ctx);
            f.string("`");
            print_template_parts(f, arena, &template.raw_sources, &template.values, ctx);
            f.string("`");
        }
        ExpressionDesc::Pexp_await(e) => {
            // OCaml: @[<hov2>await@ %a@]
            f.open_box(BoxKind::HOV, 2);
            f.string("await");
            f.space(); // @ break between await and expression
            // Check if expression is "simple" enough to not need parens
            // Note: attributed expressions will get their own parens from print_expression
            let e_expr = arena.get_expr(*e);
            let has_attrs = !printable_attributes(arena, &e_expr.pexp_attributes).is_empty();
            let is_simple = matches!(
                &e_expr.pexp_desc,
                ExpressionDesc::Pexp_ident(_)
                    | ExpressionDesc::Pexp_constant(_)
                    | ExpressionDesc::Pexp_tuple(_)
                    | ExpressionDesc::Pexp_array(_)
                    | ExpressionDesc::Pexp_record(_)
            ) || matches!(&e_expr.pexp_desc, ExpressionDesc::Pexp_construct(_, args) if args.txt.is_empty());
            // If has attributes, print_expression already produces ((expr)[@attr ])
            // so we don't need to add extra parens
            let needs_parens = !is_simple && !has_attrs;
            if needs_parens {
                f.string("(");
            }
            print_expression(f, arena, e_expr);
            if needs_parens {
                f.string(")");
            }
            f.close_box();
        }
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            print_jsx_element(f, arena, jsx);
        }
    }
}

// ============================================================================
// JSX Printing
// ============================================================================

fn jsx_tag_name_to_string(tag_name: &JsxTagName, arena: &ParseArena) -> String {
    match tag_name {
        JsxTagName::Lower(name) => name.clone(),
        JsxTagName::QualifiedLower { path, name } => {
            let path_str = arena.longident_to_string(arena.get_longident(*path));
            format!("{}.{}", path_str, name)
        }
        JsxTagName::Upper(lident) => arena.longident_to_string(arena.get_longident(*lident)),
        JsxTagName::Invalid(name) => name.clone(),
    }
}

fn print_jsx_element<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, jsx: &JsxElement) {
    match jsx {
        JsxElement::Fragment(frag) => {
            f.string("<>");
            for (i, child) in frag.children.iter().enumerate() {
                if i > 0 {
                    f.space(); // OCaml uses "@ " (space with optional break) between children
                }
                print_expression_simple(f, arena, arena.get_expr(*child));
            }
            f.string("</>");
        }
        JsxElement::Unary(elem) => {
            let name = jsx_tag_name_to_string(&elem.tag_name.txt, arena);
            if elem.props.is_empty() {
                f.string(&format!("<{} />", name));
            } else {
                f.string(&format!("<{} ", name));
                print_jsx_props(f, arena, &elem.props);
                f.string(" />");
            }
        }
        JsxElement::Container(elem) => {
            let name = jsx_tag_name_to_string(&elem.tag_name_start.txt, arena);
            let closing_name = match &elem.closing_tag {
                None => String::new(),
                Some(closing) => {
                    let close_name = jsx_tag_name_to_string(&closing.name.txt, arena);
                    format!("</{}>", close_name)
                }
            };
            if elem.props.is_empty() {
                f.string(&format!("<{}>", name));
                for (i, child) in elem.children.iter().enumerate() {
                    if i > 0 {
                        f.space(); // OCaml uses "@ " between children
                    }
                    print_expression_simple(f, arena, arena.get_expr(*child));
                }
                f.string(&closing_name);
            } else {
                f.string(&format!("<{} ", name));
                print_jsx_props(f, arena, &elem.props);
                f.string(">");
                for (i, child) in elem.children.iter().enumerate() {
                    if i > 0 {
                        f.space(); // OCaml uses "@ " between children
                    }
                    print_expression_simple(f, arena, arena.get_expr(*child));
                }
                f.string(&closing_name);
            }
        }
    }
}

fn print_jsx_props<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, props: &[JsxProp]) {
    for (i, prop) in props.iter().enumerate() {
        if i > 0 {
            f.string(" ");
        }
        print_jsx_prop(f, arena, prop);
    }
}

fn print_jsx_prop<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, prop: &JsxProp) {
    match prop {
        JsxProp::Punning { optional, name } => {
            if *optional {
                f.string("?");
            }
            f.string(arena.get_string(name.txt));
        }
        JsxProp::Value {
            name,
            optional,
            value,
        } => {
            f.string(arena.get_string(name.txt));
            f.string("=");
            if *optional {
                f.string("?");
            }
            print_expression_simple(f, arena, arena.get_expr(*value));
        }
        JsxProp::Spreading { expr, .. } => {
            f.string("{...");
            print_expression_simple(f, arena, arena.get_expr(*expr));
            f.string("}");
        }
    }
}

// ============================================================================
// Patterns
// ============================================================================

fn print_pattern<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, pat: &Pattern) {
    let has_attrs = !pat.ppat_attributes.is_empty();
    if has_attrs {
        f.string("((");
    }
    print_pattern_inner(f, arena, pat);
    if has_attrs {
        f.string(")");
        // OCaml: pp f "((%a)%a)" — NO cut/break between ) and attributes for patterns
        // (Unlike expressions which use @, = Cut between ) and attributes)
        print_attributes(f, arena, &pat.ppat_attributes);
        f.string(")");
    }
}

/// Print a pattern in "simple" context - non-simple patterns get wrapped in parens.
/// This matches OCaml's simple_pattern which wraps non-simple patterns via:
/// `| _ -> paren true (pattern ctxt) f x`
fn print_simple_pattern<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, pat: &Pattern) {
    if pattern_is_simple(pat, arena) {
        print_pattern(f, arena, pat);
    } else {
        f.string("(");
        print_pattern(f, arena, pat);
        f.string(")");
    }
}

fn print_pattern_inner<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, pat: &Pattern) {
    match &pat.ppat_desc {
        PatternDesc::Ppat_any => {
            f.string("_");
        }
        PatternDesc::Ppat_var(name) => {
            f.string(arena.get_string(name.txt));
        }
        PatternDesc::Ppat_alias(p, name) => {
            // OCaml: @[<2>%a@;as@;%a@]
            f.open_box(BoxKind::Box, 2);
            print_pattern(f, arena, arena.get_pat(*p));
            f.space(); // @; before as
            f.string("as");
            f.space(); // @; after as
            f.string(arena.get_string(name.txt));
            f.close_box();
        }
        PatternDesc::Ppat_constant(c) => {
            // Negative numbers need parentheses in patterns
            if constant_is_negative(c) {
                f.string("(");
                print_constant(f, c);
                f.string(")");
            } else {
                print_constant(f, c);
            }
        }
        PatternDesc::Ppat_interval(inner) => {
            let (ref c1, ref c2) = **inner;
            // Negative numbers in intervals need parentheses
            let c1_needs_parens = constant_is_negative(c1);
            let c2_needs_parens = constant_is_negative(c2);
            if c1_needs_parens {
                f.string("(");
            }
            print_constant(f, c1);
            if c1_needs_parens {
                f.string(")");
            }
            f.string("..");
            if c2_needs_parens {
                f.string("(");
            }
            print_constant(f, c2);
            if c2_needs_parens {
                f.string(")");
            }
        }
        PatternDesc::Ppat_tuple(pats) => {
            print_pat_tuple(f, arena, pats);
        }
        PatternDesc::Ppat_construct(lid, arg) => {
            // Special case for cons pattern - no outer parens by default
            if let Longident::Lident(name_idx) = arena.get_longident(lid.txt) {
                let name = arena.get_string(*name_idx);
                if name == "::" {
                    {
                        {
                            let elements = &arg.txt;
                            if elements.len() == 2 {
                                let left = arena.get_pat(elements[0]);
                                let right = arena.get_pat(elements[1]);
                                // Left element needs parens if it's an alias or constraint
                                let left_needs_parens = pattern_needs_parens_as_param(left, arena);
                                if left_needs_parens {
                                    f.string("(");
                                }
                                print_pattern(f, arena, left);
                                if left_needs_parens {
                                    f.string(")");
                                }
                                f.string("::");
                                // Right element needs parens if it's an alias (so it doesn't
                                // look like `(x::xs) as tail`)
                                let right_needs_parens =
                                    matches!(&right.ppat_desc, PatternDesc::Ppat_alias(..));
                                if right_needs_parens {
                                    f.string("(");
                                }
                                print_pattern(f, arena, right);
                                if right_needs_parens {
                                    f.string(")");
                                }
                                return;
                            }
                        }
                    }
                }
            }
            match arg.txt.as_slice() {
                [] => print_longident_idx(f, arena, lid.txt),
                args => {
                    // OCaml: @[<2>%a@;%a@] with simple_pattern for arg
                    f.open_box(BoxKind::Box, 2);
                    print_longident_idx(f, arena, lid.txt);
                    f.space();
                    match args {
                        [a] => print_simple_pattern(f, arena, arena.get_pat(*a)),
                        args => print_pat_tuple(f, arena, args),
                    }
                    f.close_box();
                }
            }
        }
        PatternDesc::Ppat_variant(inner) => {
            let (ref label, ref arg) = **inner;
            if !arg.txt.is_empty() {
                // OCaml: @[<2>`%s@;%a@] with simple_pattern
                f.open_box(BoxKind::Box, 2);
                f.string("`");
                f.string(label);
                f.space();
                match arg.txt.as_slice() {
                    [a] => print_simple_pattern(f, arena, arena.get_pat(*a)),
                    args => print_pat_tuple(f, arena, args),
                }
                f.close_box();
            } else {
                f.string("`");
                f.string(label);
            }
        }
        PatternDesc::Ppat_record(inner) => {
            let (ref fields, ref closed, ref record_rest) = **inner;
            // OCaml closed: @[<2>{@;%a@;}@]  with sep ";@;"
            // OCaml open:   @[<2>{@;%a;_}@]  with sep ";@;"
            f.open_box(BoxKind::Box, 2);
            f.string("{");
            f.space(); // @; after {
            for (i, field) in fields.iter().enumerate() {
                if i > 0 {
                    f.string(";");
                    f.space(); // ;@; separator
                }
                // OCaml only punns for simple Lident fields, not qualified Ldot fields
                let is_punned = match arena.get_longident(field.lid.txt) {
                    Longident::Lident(name_idx) => {
                        let fname = arena.get_string(*name_idx);
                        let field_pat = arena.get_pat(field.pat);
                        field_pat.ppat_attributes.is_empty()
                            && matches!(&field_pat.ppat_desc, PatternDesc::Ppat_var(var) if arena.get_string(var.txt) == fname)
                    }
                    _ => false,
                };

                if is_punned {
                    // OCaml: @[<2>%a%s@]
                    f.open_box(BoxKind::Box, 2);
                    print_longident_idx(f, arena, field.lid.txt);
                    if field.opt {
                        f.string("?");
                    }
                    f.close_box();
                } else {
                    // OCaml: @[<2>%a%s@;=@;%a@]
                    f.open_box(BoxKind::Box, 2);
                    print_longident_idx(f, arena, field.lid.txt);
                    if field.opt {
                        f.string("?");
                    }
                    f.space(); // @; before =
                    f.string("=");
                    f.space(); // @; after =
                    // Print with parens for alias patterns (pattern1 context)
                    let field_pat = arena.get_pat(field.pat);
                    let needs_parens = matches!(
                        &field_pat.ppat_desc,
                        PatternDesc::Ppat_alias(..) | PatternDesc::Ppat_or(..)
                    );
                    if needs_parens {
                        f.string("(");
                    }
                    print_pattern(f, arena, field_pat);
                    if needs_parens {
                        f.string(")");
                    }
                    f.close_box();
                }
            }
            if let Some(rest) = record_rest.as_ref() {
                if !fields.is_empty() {
                    f.string(";");
                    f.space();
                }
                f.string("...");
                if let Some(rest_type) = rest.rest_type {
                    print_core_type(f, arena, arena.get_core_type(rest_type));
                    f.string(" as ");
                }
                f.string(arena.get_string(rest.rest_name.txt));
                f.space();
                f.string("}");
            } else if matches!(closed, ClosedFlag::Open) {
                f.string(";_}");
            } else {
                f.space(); // @; before }
                f.string("}");
            }
            f.close_box();
        }
        PatternDesc::Ppat_array(pats) => {
            // OCaml: pp f "@[<2>[|%a|]@]" with sep ";"
            f.open_box(BoxKind::Box, 2);
            f.string("[|");
            for (i, p) in pats.iter().enumerate() {
                if i > 0 {
                    f.string(";");
                }
                print_pattern(f, arena, arena.get_pat(*p));
            }
            f.string("|]");
            f.close_box();
        }
        PatternDesc::Ppat_or(p1, p2) => {
            print_pattern(f, arena, arena.get_pat(*p1));
            f.string("|");
            print_pattern(f, arena, arena.get_pat(*p2));
        }
        PatternDesc::Ppat_constraint(inner) => {
            let (ref p_idx, ref t_idx) = **inner;
            let p = arena.get_pat(*p_idx);
            let t = arena.get_core_type(*t_idx);
            // OCaml: pp f "@[<2>(%a@;:@;%a)@]" (pattern1 ctxt) p (core_type ctxt) ct
            f.open_box(BoxKind::Box, 2);
            f.string("(");
            // Only alias and or patterns need extra parens (cons is handled by pattern1 without parens)
            let needs_inner_parens = matches!(
                p.ppat_desc,
                PatternDesc::Ppat_alias(..) | PatternDesc::Ppat_or(..)
            );
            if needs_inner_parens {
                f.string("(");
            }
            print_pattern(f, arena, p);
            if needs_inner_parens {
                f.string(")");
            }
            f.space(); // @; before :
            f.string(":");
            f.space(); // @; after :
            print_core_type(f, arena, t);
            f.string(")");
            f.close_box();
        }
        PatternDesc::Ppat_type(lid) => {
            f.string("#");
            print_longident_idx(f, arena, lid.txt);
        }
        PatternDesc::Ppat_unpack(name) => {
            // OCaml: pp f "(module@ %s)@ " s.txt
            f.string("(module");
            f.space(); // @ after "(module"
            f.string(arena.get_string(name.txt));
            f.string(")");
            f.space(); // @ trailing break
        }
        PatternDesc::Ppat_exception(p_idx) => {
            let p = arena.get_pat(*p_idx);
            f.string("exception ");
            // Or-patterns and alias patterns inside exception need parentheses
            let needs_parens = matches!(
                p.ppat_desc,
                PatternDesc::Ppat_or(..) | PatternDesc::Ppat_alias(..)
            );
            if needs_parens {
                f.string("(");
            }
            print_pattern(f, arena, p);
            if needs_parens {
                f.string(")");
            }
        }
        PatternDesc::Ppat_extension(ext_inner) => {
            let (ref name, ref payload) = **ext_inner;
            f.open_box(BoxKind::H, 2);
            f.string("[%");
            f.string(arena.get_string(name.txt));
            f.space();
            print_payload(f, arena, payload);
            f.string("]");
            f.close_box();
        }
    }
}

// ============================================================================
// Types
// ============================================================================

/// `core_type1` (pprintast.ml:328-400): no box of its own; types with
/// attributes go through `core_type`, and arrow, alias and poly types fall
/// through to `paren true (core_type ctxt)`.
fn print_core_type1<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, typ: &CoreType) {
    if !typ.ptyp_attributes.is_empty() {
        print_core_type(f, arena, typ);
        return;
    }
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(_) | CoreTypeDesc::Ptyp_alias(..) | CoreTypeDesc::Ptyp_poly(_) => {
            f.string("(");
            print_core_type(f, arena, typ);
            f.string(")");
        }
        _ => print_core_type_inner(f, arena, typ),
    }
}

fn print_core_type<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, typ: &CoreType) {
    // Types with attributes are wrapped: ((type)[@attr ])
    let has_attrs = !printable_attributes(arena, &typ.ptyp_attributes).is_empty();
    if has_attrs {
        f.string("((");
    }
    // OCaml's core_type wraps fallthrough types (those handled by core_type1) in @[<2>...@]
    // Types that already handle their own Box(2): Ptyp_arrow, Ptyp_alias, Ptyp_poly (non-empty vars)
    // Ptyp_poly with empty vars just recurses into core_type, so no extra box needed
    let needs_box = match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(_) => false,
        CoreTypeDesc::Ptyp_alias(..) => false,
        CoreTypeDesc::Ptyp_poly(inner) if !inner.0.is_empty() => false,
        CoreTypeDesc::Ptyp_poly(_) => false, // empty vars recurses into core_type
        _ => true,
    };
    if needs_box {
        f.open_box(BoxKind::Box, 2);
    }
    print_core_type_inner(f, arena, typ);
    if needs_box {
        f.close_box();
    }
    if has_attrs {
        f.string(")");
        print_attributes(f, arena, &typ.ptyp_attributes);
        f.string(")");
    }
}

fn print_core_type_inner<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, typ: &CoreType) {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_any => {
            f.string("_");
        }
        CoreTypeDesc::Ptyp_var(name) => {
            f.string("'");
            f.string(name);
        }
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (ref arg, ref ret, ref arity) = **inner;
            // OCaml: pp f "@[<2>%a@;->@;%a%s@]"
            // Structural box with indent 2, break hints around ->
            f.open_box(BoxKind::Box, 2);
            let args = arena.nary_arrow_args(arg, *arity);
            for arg in args.iter() {
                // `type_with_label` (pprintast.ml:287-295) prints the
                // argument with `core_type1`.
                print_arg_label(f, arena, &arg.lbl);
                print_core_type1(f, arena, arena.get_core_type(arg.typ));
                // Print attributes on the argument (after the type)
                print_attributes(f, arena, &arg.attrs);
                f.space(); // Break hint before ->
                f.string("->");
                f.space(); // Break hint after ->
            }
            print_core_type(f, arena, arena.get_core_type(*ret));
            if let Some(n) = arena.get_arity(*arity) {
                f.string(&format!(" (a:{})", n));
            }
            f.close_box();
        }
        CoreTypeDesc::Ptyp_tuple(types) => {
            print_type_tuple(f, arena, types);
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            // OCaml: | [x] -> pp f "%a@;" (core_type1 ctxt) x
            //        | _ -> list ~first:"(" ~last:")@;" (core_type ctxt) ~sep:",@;" f l
            if !args.is_empty() {
                if args.len() == 1 {
                    // Single arg uses core_type1 (no extra Box wrapping)
                    print_core_type_inner(f, arena, arena.get_core_type(args[0]));
                    f.space(); // @;
                } else {
                    f.string("(");
                    for (i, t) in args.iter().enumerate() {
                        if i > 0 {
                            f.string(",");
                            f.space(); // ,@;
                        }
                        print_core_type(f, arena, arena.get_core_type(*t));
                    }
                    f.string(")");
                    f.space(); // )@;
                }
            }
            print_longident_idx(f, arena, lid.txt);
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            let (ref fields, ref closed) = **inner;
            // OCaml: pp f "@[<hov2><@ %a%a@ > @]"
            f.open_box(BoxKind::HOV, 2);
            f.string("<");
            f.space(); // @ after <
            for (i, field) in fields.iter().enumerate() {
                if i > 0 {
                    f.string(";");
                }
                match field {
                    ObjectField::Otag(name, attrs, typ_idx) if attrs.is_empty() => {
                        // OCaml: pp f "@[<hov2>%s: %a@;<2 0>@]"
                        f.open_box(BoxKind::HOV, 2);
                        f.string(arena.get_string(name.txt));
                        f.string(": ");
                        print_core_type(f, arena, arena.get_core_type(*typ_idx));
                        f.break_(2, 0);
                        f.close_box();
                    }
                    ObjectField::Otag(name, attrs, typ_idx) => {
                        // OCaml: pp f "@[<hov2>%s: %a@ %a@ @]"
                        f.open_box(BoxKind::HOV, 2);
                        f.string(arena.get_string(name.txt));
                        f.string(": ");
                        print_core_type(f, arena, arena.get_core_type(*typ_idx));
                        f.space(); // @ after type
                        let printable = printable_attributes(arena, attrs);
                        if !printable.is_empty() {
                            print_attributes(f, arena, attrs);
                        }
                        f.space(); // @ before close
                        f.close_box();
                    }
                    ObjectField::Oinherit(typ_idx) => {
                        // OCaml: pp f "@[<hov2>%a@ @]"
                        f.open_box(BoxKind::HOV, 2);
                        print_core_type(f, arena, arena.get_core_type(*typ_idx));
                        f.space(); // @ after type
                        f.close_box();
                    }
                }
            }
            // Open object suffix
            // OCaml field_var: if fields empty then ".." else " ;.."
            if matches!(closed, ClosedFlag::Open) {
                if fields.is_empty() {
                    f.string("..");
                } else {
                    f.string(" ;..");
                }
            }
            f.space(); // @ before >
            f.string(">");
            f.space(); // @ after >
            f.close_box();
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (ref t_idx, ref name) = **inner;
            let t = arena.get_core_type(*t_idx);
            // OCaml: pp f "@[<2>%a@;as@;'%s@]" (core_type1 ctxt) ct s
            f.open_box(BoxKind::Box, 2);
            // Arrow types inside alias need parens for precedence
            let needs_parens = matches!(t.ptyp_desc, CoreTypeDesc::Ptyp_arrow(_));
            if needs_parens {
                f.string("(");
            }
            print_core_type(f, arena, t);
            if needs_parens {
                f.string(")");
            }
            f.space();
            f.string("as");
            f.space();
            f.string("'");
            f.string(name);
            f.close_box();
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (ref rows, ref closed, ref labels) = **inner;
            // OCaml: pp f "@[<2>[%a%a]@]" ...
            f.open_box(BoxKind::Box, 2);
            f.string("[");

            // Empty variant cases
            if rows.is_empty() {
                match closed {
                    ClosedFlag::Open => f.string(">"),
                    ClosedFlag::Closed => {}
                }
            } else {
                // Non-empty: prefix + break, then list
                // OCaml: pp f "%s@;%a" prefix (list type_variant_helper ~sep:"@;<1 -2>| ") rows
                match (closed, &labels) {
                    (ClosedFlag::Closed, None) => {
                        // Just break hint (no prefix character)
                        f.space();
                    }
                    (ClosedFlag::Closed, Some(_)) => {
                        f.string("<");
                        f.space();
                    }
                    (ClosedFlag::Open, _) => {
                        f.string(">");
                        f.space();
                    }
                }

                for (i, row) in rows.iter().enumerate() {
                    if i > 0 {
                        // Separator: @;<1 -2>| = break with offset -2, then "| "
                        // The -2 offset causes the "|" to align with the "["
                        f.break_(1, -2);
                        f.string("| ");
                    }
                    match row {
                        RowField::Rtag(label, attrs, empty, types) => {
                            // OCaml: @[<2>%a%a@;%a@]
                            f.open_box(BoxKind::Box, 2);
                            f.string("`");
                            f.string(&label.txt);
                            if !*empty || !types.is_empty() {
                                // of@; = " of " with break hint
                                f.space();
                                f.string("of");
                                f.space();
                                for (j, group) in types.iter().enumerate() {
                                    if j > 0 {
                                        f.string("&");
                                    }
                                    // pprintast.ml: `Ast_helper.Typ.tuple ~loc args`
                                    // for a multi-type group.
                                    match group.txt.as_slice() {
                                        [t] => print_core_type(f, arena, arena.get_core_type(*t)),
                                        types => {
                                            let tuple = arena.push_shared_core_type(CoreType {
                                                ptyp_desc: CoreTypeDesc::Ptyp_tuple(Box::new(
                                                    types.to_vec(),
                                                )),
                                                ptyp_loc: group.loc,
                                                ptyp_attributes: Attributes::new(),
                                            });
                                            print_core_type(f, arena, arena.get_core_type(tuple))
                                        }
                                    }
                                }
                            }
                            // Trailing break (@;) then attrs
                            f.space();
                            print_attributes(f, arena, attrs);
                            f.close_box();
                        }
                        RowField::Rinherit(typ_idx) => {
                            print_core_type(f, arena, arena.get_core_type(*typ_idx));
                        }
                    }
                }
            }

            // Low labels (present for some polymorphic variants)
            // OCaml: Some [] | None -> () (do nothing)
            //        Some xs -> print "> " then labels
            if let Some(lbls) = labels {
                if !lbls.is_empty() {
                    f.string("> ");
                    for (i, lbl) in lbls.iter().enumerate() {
                        if i > 0 {
                            f.string(" ");
                        }
                        f.string("`");
                        f.string(lbl);
                    }
                }
            }
            f.string("]");
            f.close_box();
        }
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (ref vars, ref t_idx) = **inner;
            let t = arena.get_core_type(*t_idx);
            if vars.is_empty() {
                // OCaml: Ptyp_poly ([], ct) -> core_type ctxt f ct
                print_core_type(f, arena, t);
            } else {
                // OCaml: @[<2>%a@;.@;%a@] with tyvars separated by @;
                f.open_box(BoxKind::Box, 2);
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        f.space(); // @; between tyvars
                    }
                    f.string("'");
                    f.string(arena.get_string(var.txt));
                }
                f.space(); // @; before .
                f.string(".");
                f.space(); // @; after .
                print_core_type(f, arena, t);
                f.close_box();
            }
        }
        CoreTypeDesc::Ptyp_package(pkg_inner) => {
            let (ref lid, ref constraints) = **pkg_inner;
            // OCaml: @[<hov2>(module@ %a@ with@ %a)@]
            f.open_box(BoxKind::HOV, 2);
            f.string("(module");
            f.space(); // @ after "(module"
            print_longident_idx(f, arena, lid.txt);
            for (i, (path, typ_idx)) in constraints.iter().enumerate() {
                if i == 0 {
                    f.space(); // @ before "with"
                    f.string("with");
                    f.space(); // @ after "with"
                } else {
                    f.space(); // @ before "and"
                    f.string("and");
                    f.space(); // @ after "and"
                }
                // OCaml: "type %a@ =@ %a"
                f.string("type");
                f.space();
                print_longident_idx(f, arena, path.txt);
                f.space(); // @ before "="
                f.string("=");
                f.space(); // @ after "="
                print_core_type(f, arena, arena.get_core_type(*typ_idx));
            }
            f.string(")");
            f.close_box();
        }
        CoreTypeDesc::Ptyp_extension(ext_inner) => {
            let (ref name, ref payload) = **ext_inner;
            f.open_box(BoxKind::H, 2);
            f.string("[%");
            f.string(arena.get_string(name.txt));
            f.space();
            print_payload(f, arena, payload);
            f.string("]");
            f.close_box();
        }
    }
    // Note: attributes handled in print_core_type wrapper
}

// ============================================================================
// Labels and arguments
// ============================================================================

fn print_arg_label<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, label: &ArgLabel) {
    // In OCaml types, labeled arguments are printed as "label:type" without ~
    match label {
        ArgLabel::Nolabel => {}
        ArgLabel::Labelled(s) => {
            f.string(arena.get_string(s.txt));
            f.string(":");
        }
        ArgLabel::Optional(s) => {
            f.string("?");
            f.string(arena.get_string(s.txt));
            f.string(":");
        }
    }
}

/// Context-aware version of print_arg_with_label.
/// OCaml's `label_x_expression_param ctxt` passes context through to simple_expr and expression2.
fn print_arg_with_label_ctx<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    label: &ArgLabel,
    arg: &Expression,
    ctx: PrintCtx,
) {
    match label {
        ArgLabel::Labelled(name) => {
            let name_str = arena.get_string(name.txt);
            if let ExpressionDesc::Pexp_ident(lid) = &arg.pexp_desc {
                if let Longident::Lident(arg_name_idx) = arena.get_longident(lid.txt) {
                    let arg_name = arena.get_string(*arg_name_idx);
                    if arg_name == name_str && arg.pexp_attributes.is_empty() {
                        f.string("~");
                        f.string(name_str);
                        return;
                    }
                }
            }
            f.string("~");
            f.string(name_str);
            f.string(":");
            // OCaml uses simple_expr ctxt for labeled args
            print_expression_simple_ctx(f, arena, arg, ctx);
        }
        ArgLabel::Optional(name) => {
            let name_str = arena.get_string(name.txt);
            if let ExpressionDesc::Pexp_ident(lid) = &arg.pexp_desc {
                if let Longident::Lident(arg_name_idx) = arena.get_longident(lid.txt) {
                    let arg_name = arena.get_string(*arg_name_idx);
                    if arg_name == name_str && arg.pexp_attributes.is_empty() {
                        f.string("?");
                        f.string(name_str);
                        return;
                    }
                }
            }
            f.string("?");
            f.string(name_str);
            f.string(":");
            // OCaml uses simple_expr ctxt for optional args
            print_expression_simple_ctx(f, arena, arg, ctx);
        }
        ArgLabel::Nolabel => {
            // OCaml uses expression2 ctxt for unlabeled args (label_x_expression_param -> Nolabel -> expression2)
            print_expression2_ctx(f, arena, arg, ctx);
        }
    }
}

// ============================================================================
// Constants
// ============================================================================

/// The `parts` printer of OCaml pprintast's template cases.
fn print_template_parts<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    sources: &[StringLoc],
    values: &[ExprIdx],
    ctx: PrintCtx,
) {
    assert_eq!(sources.len(), values.len() + 1);
    for (index, source) in sources.iter().enumerate() {
        f.string(arena.get_string(source.txt));
        if let Some(value) = values.get(index) {
            f.string("${");
            print_expression_with_ctx(f, arena, arena.get_expr(*value), ctx);
            f.string("}");
        }
    }
}

fn print_constant<W: Write>(f: &mut Formatter<W>, c: &Constant) {
    match c {
        Constant::Integer(s, suffix) => {
            f.string(s);
            if let Some(c) = suffix {
                f.string(&c.to_string());
            }
        }
        Constant::Char { source, .. } => {
            f.string("'");
            f.string(source);
            f.string("'");
        }
        Constant::String(payload) => {
            f.string("{js|");
            f.string(payload.source());
            f.string("|js}");
        }
        Constant::Json(source) => {
            f.string("{json|");
            f.string(source);
            f.string("|json}");
        }
        Constant::RawSource(source) => {
            f.string("{js|");
            f.string(source);
            f.string("|js}");
        }
        Constant::Float(s, suffix) => {
            f.string(s);
            if let Some(c) = suffix {
                f.string(&c.to_string());
            }
        }
    }
}

// ============================================================================
// Longident
// ============================================================================

fn print_longident<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, lid: &Longident) {
    match lid {
        Longident::Lident(name_idx) => {
            let name = arena.get_string(*name_idx);
            f.string(name);
        }
        Longident::Ldot(prefix, name_idx) => {
            print_longident(f, arena, prefix);
            f.string(".");
            let name = arena.get_string(*name_idx);
            f.string(name);
        }
        Longident::Lapply(m1, m2) => {
            print_longident(f, arena, m1);
            f.string("(");
            print_longident(f, arena, m2);
            f.string(")");
        }
    }
}

/// Print longident from index using arena
fn print_longident_idx<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, lid_idx: LidentIdx) {
    print_longident(f, arena, arena.get_longident(lid_idx));
}

// ============================================================================
// Payload
// ============================================================================

fn print_payload<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, payload: &Payload) {
    match payload {
        Payload::PStr(items) => {
            // Special case: single Pstr_eval prints just the expression
            // OCaml: pp f "@[<2>%a@]%a" (expression ctxt) e (item_attributes ctxt) attrs
            if items.len() == 1 {
                if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                    let (ref expr_idx, ref attrs) = **eval_inner;
                    f.open_box(BoxKind::Box, 2);
                    print_expression(f, arena, arena.get_expr(*expr_idx));
                    f.close_box();
                    print_item_attributes(f, arena, attrs);
                    return;
                }
            }
            for (i, item) in items.iter().enumerate() {
                print_structure_item(f, arena, item);
                if i < items.len() - 1 {
                    f.string("\n  ");
                }
            }
        }
        Payload::PSig(sig_items) => {
            // Print signature items with : prefix and newlines between items
            f.string(":");
            for (i, item) in sig_items.iter().enumerate() {
                print_signature_item(f, arena, item);
                if i < sig_items.len() - 1 {
                    f.string("\n    ");
                }
            }
        }
        Payload::PTyp(typ_idx) => {
            f.string(":");
            print_core_type(f, arena, arena.get_core_type(*typ_idx));
        }
        Payload::PPat(inner) => {
            let (ref pat_idx, ref guard) = **inner;
            f.string("?");
            print_pattern(f, arena, arena.get_pat(*pat_idx));
            if let Some(g) = guard {
                f.string(" when ");
                print_expression(f, arena, arena.get_expr(*g));
            }
        }
    }
}

// ============================================================================
// Type declarations
// ============================================================================

/// Print record declaration: {field1: type; field2: type}
/// Matches OCaml's record_declaration: pp f "{@\n%a}" (list type_record_field ~sep:";@\n") lbls
/// Each field: @[<2>mutable? name?: type @; attrs@]
fn print_record_declaration<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    fields: &[LabelDeclaration],
) {
    // OCaml: pp f "{@\n%a}" (list type_record_field ~sep:";@\n") lbls
    f.string("{");
    f.newline();
    if fields.is_empty() {
        f.string("}");
        return;
    }
    for (i, field) in fields.iter().enumerate() {
        // OCaml: @[<2>%a%s%a:@;%a@;%a@]
        // mutable_flag, name, optional_flag, core_type, attributes
        f.open_box(BoxKind::Box, 2);
        if matches!(field.pld_mutable, MutableFlag::Mutable) {
            f.string("mutable ");
        }
        f.string(arena.get_string(field.pld_name.txt));
        if field.pld_optional {
            f.string("?");
        }
        f.string(":");
        f.space();
        print_core_type(f, arena, arena.get_core_type(field.pld_type));
        f.space();
        print_attributes(
            f,
            arena,
            &crate::ast_helper_type::field_attributes(arena, field),
        );
        f.close_box();
        if i < fields.len() - 1 {
            f.string(";");
            f.newline();
        } else {
            f.string("}");
        }
    }
}

fn print_type_declaration<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    decl: &TypeDeclaration,
) {
    if !decl.ptype_params.is_empty() {
        if decl.ptype_params.len() == 1 {
            // Print variance prefix
            match decl.ptype_params[0].1 {
                Variance::Covariant => f.string("+"),
                Variance::Contravariant => f.string("-"),
                Variance::Invariant => {}
            }
            print_core_type(f, arena, arena.get_core_type(decl.ptype_params[0].0));
            f.string(" ");
        } else {
            f.string("(");
            for (i, (t, variance)) in decl.ptype_params.iter().enumerate() {
                if i > 0 {
                    f.string(", ");
                }
                // Print variance prefix
                match variance {
                    Variance::Covariant => f.string("+"),
                    Variance::Contravariant => f.string("-"),
                    Variance::Invariant => {}
                }
                print_core_type(f, arena, arena.get_core_type(*t));
            }
            f.string(") ");
        }
    }
    f.string(arena.get_string(decl.ptype_name.txt));

    if let Some(manifest) = &decl.ptype_manifest {
        // OCaml: type_def_list prints " =" then type_declaration prints "@;private @;type"
        // The break hint allows long types to wrap to the next line
        f.string(" =");
        if matches!(decl.ptype_private, PrivateFlag::Private) {
            f.space(); // Break hint before private
            f.string("private");
        }
        f.space(); // Break hint before type body (OCaml's @;)
        print_core_type(f, arena, arena.get_core_type(*manifest));
    }

    match &decl.ptype_kind {
        TypeKind::Ptype_abstract => {}
        TypeKind::Ptype_variant(ctors) => {
            f.string(" =");
            if matches!(decl.ptype_private, PrivateFlag::Private) {
                f.string(" private");
            }
            // OCaml uses: pp f "%t%t@\n%a" intro priv (list ~sep:"@\n" constructor_declaration) xs
            // Where constructor_declaration is: pp f "|@;"; ...
            // This means each constructor gets @\n (force newline with indent) + |@; (break hint)
            for ctor in ctors.iter() {
                // OCaml: pp f "|@;"; constructor_declaration ...
                // Each constructor gets @\n (force newline) + |@; (| then break hint)
                f.newline();
                f.string("|");
                f.space(); // @; after |
                f.string(arena.get_string(ctor.pcd_name.txt));
                // OCaml constructor_declaration: "%s%a@;%a" name args attrs
                match &ctor.pcd_res {
                    None => {
                        // Non-GADT: pp f "@;of@;%a" (list (core_type1 ctxt) ~sep:"@;*@;") l
                        match &ctor.pcd_args {
                            ConstructorArguments::Pcstr_tuple(args) if !args.is_empty() => {
                                f.space(); // @; before "of"
                                f.string("of");
                                f.space(); // @; after "of"
                                for (j, arg) in args.iter().enumerate() {
                                    if j > 0 {
                                        f.space(); // @; before *
                                        f.string("*");
                                        f.space(); // @; after *
                                    }
                                    print_core_type1(f, arena, arena.get_core_type(*arg));
                                }
                            }
                            ConstructorArguments::Pcstr_record(fields) => {
                                f.space(); // @; before "of"
                                f.string("of");
                                f.space(); // @; after "of"
                                print_record_declaration(f, arena, fields);
                            }
                            _ => {}
                        }
                    }
                    Some(res_idx) => {
                        // GADT: "%s:@;%a@;%a" name args attrs
                        let res = arena.get_core_type(*res_idx);
                        f.string(":");
                        f.space(); // @; after :
                        match &ctor.pcd_args {
                            ConstructorArguments::Pcstr_tuple(args) if !args.is_empty() => {
                                // "%a@;->@;%a" (list core_type1 ~sep:"@;*@;") l core_type1 r
                                for (j, arg) in args.iter().enumerate() {
                                    if j > 0 {
                                        f.space(); // @; before *
                                        f.string("*");
                                        f.space(); // @; after *
                                    }
                                    print_core_type1(f, arena, arena.get_core_type(*arg));
                                }
                                f.space(); // @; before ->
                                f.string("->");
                                f.space(); // @; after ->
                                print_core_type1(f, arena, res);
                            }
                            ConstructorArguments::Pcstr_record(fields) => {
                                print_record_declaration(f, arena, fields);
                                f.space(); // @; before ->
                                f.string("->");
                                f.space(); // @; after ->
                                print_core_type1(f, arena, res);
                            }
                            _ => {
                                print_core_type1(f, arena, res);
                            }
                        }
                    }
                }
                // OCaml: @;%a for attrs (break hint before attrs)
                f.space();
                print_attributes(
                    f,
                    arena,
                    &crate::ast_helper_type::constructor_attributes(arena, ctor),
                );
            }
        }
        TypeKind::Ptype_record(fields) => {
            // OCaml: pp f "%t%t@;%a" intro priv (record_declaration ctxt) l
            // record_declaration: pp f "{@\n%a}" outputs { then forced newline then fields then }
            f.string(" =");
            if matches!(decl.ptype_private, PrivateFlag::Private) {
                f.string(" private");
            }
            f.space(); // @; break hint
            print_record_declaration(f, arena, fields);
        }
        TypeKind::Ptype_open => {
            f.string(" =");
            if matches!(decl.ptype_private, PrivateFlag::Private) {
                f.string(" private");
            }
            f.string(" ..");
        }
    }

    // Type constraints
    for (ct1, ct2, _) in &decl.ptype_cstrs {
        f.string(" constraint ");
        print_core_type(f, arena, arena.get_core_type(*ct1));
        f.string(" = ");
        print_core_type(f, arena, arena.get_core_type(*ct2));
    }

    // NOTE: Type attributes (ptype_attributes) are NOT printed here.
    // In OCaml, item attributes are printed OUTSIDE the @[<2>...@] box
    // by the caller (Pstr_type/Psig_type).
}

fn print_extension_constructor<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    ext: &ExtensionConstructor,
) {
    f.string(arena.get_string(ext.pext_name.txt));
    match &ext.pext_kind {
        ExtensionConstructorKind::Pext_decl(args, res) => {
            // OCaml: extension_constructor delegates to constructor_declaration
            // Same format strings as constructor_declaration
            match res {
                None => {
                    // Non-GADT: "%s%a@;%a" name args attrs
                    match args {
                        ConstructorArguments::Pcstr_tuple(args) if !args.is_empty() => {
                            f.space(); // @; before "of"
                            f.string("of");
                            f.space(); // @; after "of"
                            for (i, arg) in args.iter().enumerate() {
                                if i > 0 {
                                    f.space(); // @; before *
                                    f.string("*");
                                    f.space(); // @; after *
                                }
                                print_core_type1(f, arena, arena.get_core_type(*arg));
                            }
                        }
                        ConstructorArguments::Pcstr_record(fields) => {
                            f.space(); // @; before "of"
                            f.string("of");
                            f.space(); // @; after "of"
                            print_record_declaration(f, arena, fields);
                        }
                        _ => {}
                    }
                    f.space(); // @; before attrs
                }
                Some(r_idx) => {
                    let r = arena.get_core_type(*r_idx);
                    // GADT: "%s:@;%a@;%a" name args attrs
                    f.string(":");
                    f.space(); // @; after :
                    match args {
                        ConstructorArguments::Pcstr_tuple(args) if !args.is_empty() => {
                            for (i, arg) in args.iter().enumerate() {
                                if i > 0 {
                                    f.space(); // @; before *
                                    f.string("*");
                                    f.space(); // @; after *
                                }
                                print_core_type1(f, arena, arena.get_core_type(*arg));
                            }
                            f.space(); // @; before ->
                            f.string("->");
                            f.space(); // @; after ->
                            print_core_type1(f, arena, r);
                        }
                        ConstructorArguments::Pcstr_record(fields) => {
                            print_record_declaration(f, arena, fields);
                            f.space(); // @; before ->
                            f.string("->");
                            f.space(); // @; after ->
                            print_core_type1(f, arena, r);
                        }
                        _ => {
                            print_core_type1(f, arena, r);
                        }
                    }
                    f.space(); // @; before attrs
                }
            }
        }
        ExtensionConstructorKind::Pext_rebind(lid) => {
            // Print attributes before rebind
            print_attributes(f, arena, &ext.pext_attributes);
            f.string(" = ");
            print_longident_idx(f, arena, lid.txt);
            return; // Don't print attributes twice
        }
    }
    // Print attributes
    print_attributes(f, arena, &ext.pext_attributes);
}

// ============================================================================
// Modules
// ============================================================================

fn print_module_expr<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, mexpr: &ModuleExpr) {
    // Print attributes on module expressions: ((mexpr)[@attr ])
    let has_attrs = !printable_attributes(arena, &mexpr.pmod_attributes).is_empty();
    if has_attrs {
        f.string("((");
    }
    print_module_expr_inner(f, arena, mexpr);
    if has_attrs {
        f.string(")");
        print_attributes(f, arena, &mexpr.pmod_attributes);
        f.string(")");
    }
}

fn print_module_expr_inner<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, mexpr: &ModuleExpr) {
    match &*mexpr.pmod_desc {
        ModuleExprDesc::Pmod_ident(lid) => {
            print_longident_idx(f, arena, lid.txt);
        }
        ModuleExprDesc::Pmod_structure(items) => {
            // OCaml: pp f "@[<hv2>struct@;@[<0>%a@]@;<1 -2>end@]" with items separated by @\n
            f.open_box(BoxKind::HV, 2);
            f.string("struct");
            f.space(); // @;
            f.open_box(BoxKind::Box, 0);
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    f.newline(); // @\n forced newline between structure items
                }
                print_structure_item(f, arena, item);
            }
            f.close_box();
            f.break_(1, -2);
            f.string("end");
            f.close_box();
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (ref name, ref mtype, ref body) = **inner;
            if let Some(mt) = mtype {
                // OCaml: pp f "functor@ (%s@ :@ %a)@;->@;%a"
                f.string("functor");
                f.space(); // @ after "functor"
                f.string("(");
                f.string(arena.get_string(name.txt));
                f.space(); // @ after name
                f.string(":");
                f.space(); // @ after ":"
                print_module_type(f, arena, arena.get_mod_type(*mt));
                f.string(")");
                f.space(); // @; after ")"
                f.string("->");
                f.space(); // @; after "->"
            } else {
                // OCaml: pp f "functor ()@;->@;%a"
                f.string("functor ()");
                f.space(); // @; after "()"
                f.string("->");
                f.space(); // @; after "->"
            }
            print_module_expr(f, arena, arena.get_mod_expr(*body));
        }
        ModuleExprDesc::Pmod_apply(m1, m2) => {
            // OCaml: pp f "(%a)(%a)" - both functor and argument get parens
            f.string("(");
            print_module_expr(f, arena, arena.get_mod_expr(*m1));
            f.string(")(");
            print_module_expr(f, arena, arena.get_mod_expr(*m2));
            f.string(")");
        }
        ModuleExprDesc::Pmod_constraint(m, mt) => {
            // OCaml: pp f "@[<hov2>(%a@ :@ %a)@]"
            f.open_box(BoxKind::HOV, 2);
            f.string("(");
            print_module_expr(f, arena, arena.get_mod_expr(*m));
            f.space(); // @ before ":"
            f.string(":");
            f.space(); // @ after ":"
            print_module_type(f, arena, arena.get_mod_type(*mt));
            f.string(")");
            f.close_box();
        }
        ModuleExprDesc::Pmod_unpack(e) => {
            // OCaml: (val@ %a) — break hint between val and expression
            f.string("(val");
            f.space();
            print_expression(f, arena, arena.get_expr(*e));
            f.string(")");
        }
        ModuleExprDesc::Pmod_extension(ext_inner) => {
            let (ref name, ref payload) = **ext_inner;
            // OCaml: @[<2>[%%%s@ %a]@]
            f.open_box(BoxKind::Box, 2);
            f.string("[%");
            f.string(arena.get_string(name.txt));
            f.space();
            print_payload(f, arena, payload);
            f.string("]");
            f.close_box();
        }
    }
}

fn print_module_type<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, mtype: &ModuleType) {
    // Print attributes on module types: ((mtype)[@attr ])
    let has_attrs = !printable_attributes(arena, &mtype.pmty_attributes).is_empty();
    if has_attrs {
        f.string("((");
    }
    print_module_type_inner(f, arena, mtype);
    if has_attrs {
        f.string(")");
        print_attributes(f, arena, &mtype.pmty_attributes);
        f.string(")");
    }
}

fn print_module_type_inner<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, mtype: &ModuleType) {
    match &*mtype.pmty_desc {
        ModuleTypeDesc::Pmty_ident(lid) => {
            print_longident_idx(f, arena, lid.txt);
        }
        ModuleTypeDesc::Pmty_signature(items) => {
            // OCaml: pp f "@[<hv0>@[<hv2>sig@ %a@]@ end@]"
            // Items separated by default "@ " = Break(1,0) (list without ~sep)
            f.open_box(BoxKind::HV, 0);
            f.open_box(BoxKind::HV, 2);
            f.string("sig");
            f.space(); // @ break hint after sig
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    f.space(); // @ break hint between items
                }
                print_signature_item(f, arena, item);
            }
            f.close_box();
            f.space(); // @ break hint before end
            f.string("end");
            f.close_box();
        }
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (ref name, ref arg_type, ref ret_type) = **inner;
            if arg_type.is_none() {
                // OCaml: pp f "@[<hov2>functor () ->@ %a@]"
                f.open_box(BoxKind::HOV, 2);
                f.string("functor ()");
                f.space();
                f.string("->");
                f.space();
                print_module_type(f, arena, arena.get_mod_type(*ret_type));
                f.close_box();
            } else if arena.get_string(name.txt) == "_" {
                // OCaml: pp f "@[<hov2>%a@ ->@ %a@]"
                f.open_box(BoxKind::HOV, 2);
                if let Some(mt) = arg_type {
                    print_module_type(f, arena, arena.get_mod_type(*mt));
                }
                f.space();
                f.string("->");
                f.space();
                print_module_type(f, arena, arena.get_mod_type(*ret_type));
                f.close_box();
            } else {
                // OCaml: pp f "@[<hov2>functor@ (%s@ :@ %a)@ ->@ %a@]"
                f.open_box(BoxKind::HOV, 2);
                f.string("functor");
                f.space();
                f.string("(");
                f.string(arena.get_string(name.txt));
                if let Some(mt) = arg_type {
                    f.space();
                    f.string(":");
                    f.space();
                    print_module_type(f, arena, arena.get_mod_type(*mt));
                }
                f.string(")");
                f.space();
                f.string("->");
                f.space();
                print_module_type(f, arena, arena.get_mod_type(*ret_type));
                f.close_box();
            }
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (ref mt_idx, ref constraints) = **inner;
            // OCaml: pp f "@[<hov2>(%a@ with@ %a)@]" when there are constraints
            // or pp f "@[<hov2>%a@]" when empty
            if constraints.is_empty() {
                f.open_box(BoxKind::HOV, 2);
                print_module_type(f, arena, arena.get_mod_type(*mt_idx));
                f.close_box();
            } else {
                f.open_box(BoxKind::HOV, 2);
                f.string("(");
                print_module_type(f, arena, arena.get_mod_type(*mt_idx));
                f.space();
                f.string("with");
                for (i, constraint) in constraints.iter().enumerate() {
                    if i > 0 {
                        f.space();
                        f.string("and");
                    }
                    f.space();
                    match constraint {
                        WithConstraint::Pwith_type(lid, decl) => {
                            // OCaml: pp f "type@ %a %a =@ %a" params lid type_decl
                            f.string("type");
                            f.space(); // @ after type
                            // Print type params
                            if !decl.ptype_params.is_empty() {
                                if decl.ptype_params.len() == 1 {
                                    print_core_type(
                                        f,
                                        arena,
                                        arena.get_core_type(decl.ptype_params[0].0),
                                    );
                                    f.string(" ");
                                } else {
                                    f.string("(");
                                    for (i, (t, _)) in decl.ptype_params.iter().enumerate() {
                                        if i > 0 {
                                            f.string(",");
                                        }
                                        print_core_type(f, arena, arena.get_core_type(*t));
                                    }
                                    f.string(") ");
                                }
                            } else {
                                f.string(" "); // space before lid when params empty
                            }
                            print_longident_idx(f, arena, lid.txt);
                            f.string(" =");
                            f.space(); // @ after =
                            // type_declaration prints @; then private then manifest then constraints
                            f.space(); // @; in type_declaration
                            if decl.ptype_private == PrivateFlag::Private {
                                f.string("private ");
                            }
                            if let Some(manifest) = &decl.ptype_manifest {
                                print_core_type(f, arena, arena.get_core_type(*manifest));
                            }
                            // Print type constraints
                            for (ct1, ct2, _) in &decl.ptype_cstrs {
                                f.string(" constraint ");
                                print_core_type(f, arena, arena.get_core_type(*ct1));
                                f.string(" = ");
                                print_core_type(f, arena, arena.get_core_type(*ct2));
                            }
                        }
                        WithConstraint::Pwith_module(lid1, lid2) => {
                            f.string("module ");
                            print_longident_idx(f, arena, lid1.txt);
                            f.string(" = ");
                            print_longident_idx(f, arena, lid2.txt);
                        }
                        WithConstraint::Pwith_typesubst(lid, decl) => {
                            // Same pattern as Pwith_type but with :=
                            f.string("type");
                            f.space();
                            // Print type params
                            if !decl.ptype_params.is_empty() {
                                if decl.ptype_params.len() == 1 {
                                    print_core_type(
                                        f,
                                        arena,
                                        arena.get_core_type(decl.ptype_params[0].0),
                                    );
                                    f.string(" ");
                                } else {
                                    f.string("(");
                                    for (i, (t, _)) in decl.ptype_params.iter().enumerate() {
                                        if i > 0 {
                                            f.string(",");
                                        }
                                        print_core_type(f, arena, arena.get_core_type(*t));
                                    }
                                    f.string(") ");
                                }
                            } else {
                                f.string(" ");
                            }
                            print_longident_idx(f, arena, lid.txt);
                            f.string(" :=");
                            f.space();
                            f.space();
                            if decl.ptype_private == PrivateFlag::Private {
                                f.string("private ");
                            }
                            if let Some(manifest) = &decl.ptype_manifest {
                                print_core_type(f, arena, arena.get_core_type(*manifest));
                            }
                            // Print type constraints
                            for (ct1, ct2, _) in &decl.ptype_cstrs {
                                f.string(" constraint ");
                                print_core_type(f, arena, arena.get_core_type(*ct1));
                                f.string(" = ");
                                print_core_type(f, arena, arena.get_core_type(*ct2));
                            }
                        }
                        WithConstraint::Pwith_modsubst(lid1, lid2) => {
                            f.string("module ");
                            print_longident_idx(f, arena, lid1.txt);
                            f.string(" := ");
                            print_longident_idx(f, arena, lid2.txt);
                        }
                    }
                }
                f.string(")");
                f.close_box();
            }
        }
        ModuleTypeDesc::Pmty_typeof(mexpr) => {
            f.string("module type of ");
            print_module_expr(f, arena, arena.get_mod_expr(*mexpr));
        }
        ModuleTypeDesc::Pmty_extension(ext_inner) => {
            let (ref name, ref payload) = **ext_inner;
            f.open_box(BoxKind::H, 2);
            f.string("[%");
            f.string(arena.get_string(name.txt));
            f.space();
            print_payload(f, arena, payload);
            f.string("]");
            f.close_box();
        }
        ModuleTypeDesc::Pmty_alias(lid) => {
            f.string("(module ");
            print_longident_idx(f, arena, lid.txt);
            f.string(")");
        }
    }
}

// ============================================================================
// Signature items
// ============================================================================

/// pprintast.ml `value_description`: the primitive after the type.
fn print_value_description_prim<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    prim: &Option<PrimitiveRepr>,
) {
    let quoted = |f: &mut Formatter<W>, s: &str| {
        f.string("\"");
        f.string(s);
        f.string("\"");
    };
    match prim {
        None => {}
        Some(PrimitiveRepr::PrimName(s)) => {
            f.space();
            f.string("=");
            f.space();
            quoted(f, arena.get_string(*s));
        }
        Some(PrimitiveRepr::PrimFfi { name, .. }) => {
            f.space();
            f.string("=");
            f.space();
            quoted(f, name);
            f.space();
            quoted(f, "#rescript-external");
        }
        Some(PrimitiveRepr::PrimInlineConst(_)) => {
            f.space();
            f.string("=");
            f.space();
            quoted(f, "#rescript-inline");
        }
    }
}

fn print_signature_item<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, item: &SignatureItem) {
    match &*item.psig_desc {
        SignatureItemDesc::Psig_value(vd) => {
            // OCaml: pp f "@[<2>%s@ %a@ :@ %a@]%a"
            f.open_box(BoxKind::Box, 2);
            if vd.pval_prim.is_none() {
                f.string("val");
            } else {
                f.string("external");
            }
            f.space();
            f.string(arena.get_string(vd.pval_name.txt));
            f.space();
            f.string(":");
            f.space();
            // OCaml value_description: pp f "@[<hov2>%a%a@]"
            f.open_box(BoxKind::HOV, 2);
            print_core_type(f, arena, arena.get_core_type(vd.pval_type));
            print_value_description_prim(f, arena, &vd.pval_prim);
            f.close_box();
            f.close_box();
            print_item_attributes(f, arena, &vd.pval_attributes);
        }
        SignatureItemDesc::Psig_type(inner) => {
            let (ref rec_flag, ref decls) = **inner;
            // OCaml: @[<2>type %a%a%s%s%a@]%a for first, @[<2>and %a@]%a for others
            // Each declaration is wrapped in a box with indent 2
            let rec_str = match rec_flag {
                RecFlag::Recursive => "",
                RecFlag::Nonrecursive => " nonrec",
            };
            for (i, decl) in decls.iter().enumerate() {
                if i > 0 {
                    f.newline();
                }
                // OCaml: @[<2> - Open structural box with indent 2 for type declaration
                f.open_box(BoxKind::Box, 2);
                if i == 0 {
                    f.string("type");
                    f.string(rec_str);
                    f.string(" ");
                } else {
                    f.string("and ");
                }
                print_type_declaration(f, arena, decl);
                f.close_box();
                // OCaml: item attributes printed OUTSIDE the box
                print_item_attributes(f, arena, &decl.ptype_attributes);
            }
        }
        SignatureItemDesc::Psig_typext(ext) => {
            // Same format as Pstr_typext
            f.open_box(BoxKind::HV, 2);
            f.string("type ");
            // Print type params if present
            if !ext.ptyext_params.is_empty() {
                if ext.ptyext_params.len() == 1 {
                    // Single param: no parens, like OCaml's "type _ Tid.t +="
                    print_core_type(f, arena, arena.get_core_type(ext.ptyext_params[0].0));
                    f.string(" ");
                } else {
                    f.string("(");
                    for (i, (ty, _variance)) in ext.ptyext_params.iter().enumerate() {
                        if i > 0 {
                            f.string(",");
                        }
                        print_core_type(f, arena, arena.get_core_type(*ty));
                    }
                    f.string(") ");
                }
            }
            print_longident_idx(f, arena, ext.ptyext_path.txt);
            f.string(" += ");
            if matches!(ext.ptyext_private, PrivateFlag::Private) {
                f.string("private ");
            }
            // Extra space before line break to match OCaml's "+=  \n"
            f.string(" ");
            for ctor in ext.ptyext_constructors.iter() {
                f.newline();
                f.string("| ");
                print_extension_constructor(f, arena, ctor);
            }
            f.close_box();
            print_item_attributes(f, arena, &ext.ptyext_attributes);
        }
        SignatureItemDesc::Psig_exception(ext) => {
            // OCaml: pp f "@[<hov2>exception@ %a@]"
            f.open_box(BoxKind::HOV, 2);
            f.string("exception");
            f.space(); // @ after "exception"
            print_extension_constructor(f, arena, ext);
            f.close_box();
        }
        SignatureItemDesc::Psig_module(md) => {
            // OCaml has special case: if pmd_type is Pmty_alias with no attrs, use = syntax
            f.string("module ");
            f.string(arena.get_string(md.pmd_name.txt));
            let pmd_type = arena.get_mod_type(md.pmd_type);
            if let ModuleTypeDesc::Pmty_alias(lid) = &*pmd_type.pmty_desc {
                if pmd_type.pmty_attributes.is_empty() {
                    // module Name = Alias
                    f.string(" = ");
                    print_longident_idx(f, arena, lid.txt);
                    print_item_attributes(f, arena, &md.pmd_attributes);
                    return;
                }
            }
            // module Name : ModuleType
            f.string(" : ");
            print_module_type(f, arena, pmd_type);
            print_item_attributes(f, arena, &md.pmd_attributes);
        }
        SignatureItemDesc::Psig_recmodule(mds) => {
            // OCaml: First decl is @[<hov2>module@ rec@ %s:@ %a@]%a
            //        Others are @ @[<hov2>and@ %s:@ %a@]%a
            for (i, md) in mds.iter().enumerate() {
                if i > 0 {
                    // Break before "and" for subsequent declarations
                    f.break_(1, 0);
                }
                f.open_box(BoxKind::HOV, 2);
                if i == 0 {
                    f.string("module");
                    f.space();
                    f.string("rec");
                    f.space();
                } else {
                    f.string("and");
                    f.space();
                }
                f.string(arena.get_string(md.pmd_name.txt));
                f.string(":");
                f.space();
                print_module_type(f, arena, arena.get_mod_type(md.pmd_type));
                f.close_box();
                print_item_attributes(f, arena, &md.pmd_attributes);
            }
        }
        SignatureItemDesc::Psig_modtype(mtd) => {
            // OCaml: pp f "@[<hov2>module@ type@ %s%a@]%a"
            // where inner is: pp_print_space f (); pp f "@ =@ %a" (module_type ctxt) mt
            // This produces two spaces before = when not breaking: "Sig  ="
            f.open_box(BoxKind::HOV, 2);
            f.string("module");
            f.space();
            f.string("type");
            f.space();
            f.string(arena.get_string(mtd.pmtd_name.txt));
            if let Some(mt) = &mtd.pmtd_type {
                // pp_print_space + "@ =" gives two spaces before =
                f.string(" "); // literal space from pp_print_space
                f.space(); // break hint before =
                f.string("=");
                f.space();
                print_module_type(f, arena, arena.get_mod_type(*mt));
            }
            f.close_box();
            print_item_attributes(f, arena, &mtd.pmtd_attributes);
        }
        SignatureItemDesc::Psig_open(od) => {
            f.string("open");
            if matches!(od.popen_override, OverrideFlag::Override) {
                f.string("!");
            }
            f.string(" ");
            print_longident_idx(f, arena, od.popen_lid.txt);
            print_item_attributes(f, arena, &od.popen_attributes);
        }
        SignatureItemDesc::Psig_include(incl) => {
            // OCaml: @[<hov2>include@ %a@]%a
            f.open_box(BoxKind::HOV, 2);
            f.string("include");
            f.space();
            print_module_type(f, arena, arena.get_mod_type(incl.pincl_mod));
            f.close_box();
            print_item_attributes(f, arena, &incl.pincl_attributes);
        }
        SignatureItemDesc::Psig_attribute(attr_inner) => {
            let (ref name, ref payload) = **attr_inner;
            // Standalone/floating attributes use [@@@...] (3 @)
            f.string("[@@@");
            f.string(arena.get_string(name.txt));
            if !payload_is_empty(payload) {
                f.string(" ");
                print_payload(f, arena, payload);
            } else {
                f.string(" ");
            }
            f.string("]");
        }
        SignatureItemDesc::Psig_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            let (ref name, ref payload) = *ext;
            f.open_box(BoxKind::H, 2);
            f.string("[%%");
            f.string(arena.get_string(name.txt));
            f.space();
            print_payload(f, arena, payload);
            f.string("]");
            print_item_attributes(f, arena, attrs);
            f.close_box();
        }
    }
}

fn print_item_attributes<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    attrs: &[(Located<StrIdx>, Payload)],
) {
    // OCaml: and item_attribute ctxt f (s, e) = pp f "@[<2>[@@@@%s@ %a]@]" s.txt (payload ctxt) e
    // Each attribute is wrapped in a box with indent 2, with a break hint after the name
    let attrs = printable_attributes(arena, attrs);
    for (name, payload) in attrs {
        f.open_box(BoxKind::Box, 2);
        f.string("[@@");
        f.string(arena.get_string(name.txt));
        f.space(); // Break hint after name (matches OCaml's `@ `)
        if !payload_is_empty(payload) {
            print_payload(f, arena, payload);
        }
        f.string("]");
        f.close_box();
    }
}

/// Print attributes with single @ (for expressions, types, patterns)
/// OCaml: and attribute ctxt f (s, e) = pp f "@[<2>[@@%s@ %a]@]" s.txt (payload ctxt) e
fn print_attributes<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    attrs: &[(Located<StrIdx>, Payload)],
) {
    let attrs = printable_attributes(arena, attrs);
    for (name, payload) in attrs {
        f.open_box(BoxKind::Box, 2);
        f.string("[@");
        f.string(arena.get_string(name.txt));
        f.space(); // Break hint after name (matches OCaml's `@ `)
        if !payload_is_empty(payload) {
            print_payload(f, arena, payload);
        }
        f.string("]");
        f.close_box();
    }
}

/// `simple_expr` of a `Pexp_tuple`: also prints a multi-argument constructor
/// payload, which pprintast.ml rebuilds with `Ast_helper.Exp.tuple`.
fn print_expr_tuple<W: Write>(
    f: &mut Formatter<W>,
    arena: &ParseArena,
    exprs: &[ExprIdx],
    ctx: PrintCtx,
) {
    // OCaml: @[<hov2>(%a)@] with (list (simple_expr ctxt) ~sep:",@;")
    f.open_box(BoxKind::HOV, 2);
    f.string("(");
    for (i, e) in exprs.iter().enumerate() {
        if i > 0 {
            f.string(",");
            f.space();
        }
        print_expression_simple_ctx(f, arena, arena.get_expr(*e), ctx);
    }
    f.string(")");
    f.close_box();
}

/// `Ppat_tuple` printing; also used for multi-argument constructor payloads
/// that pprintast.ml rebuilds with `Ast_helper.Pat.tuple`.
fn print_pat_tuple<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, pats: &[PatIdx]) {
    // OCaml: @[<1>(%a)@] with sep ",@;"
    f.open_box(BoxKind::Box, 1);
    f.string("(");
    for (i, p_idx) in pats.iter().enumerate() {
        if i > 0 {
            f.string(",");
            f.space(); // ,@; separator
        }
        let p = arena.get_pat(*p_idx);
        // Alias patterns inside tuples need parentheses
        let needs_parens = matches!(p.ppat_desc, PatternDesc::Ppat_alias(..));
        if needs_parens {
            f.string("(");
        }
        print_pattern(f, arena, p);
        if needs_parens {
            f.string(")");
        }
    }
    f.string(")");
    f.close_box();
}

/// `Ptyp_tuple` printing; also used for multi-type `Rtag` groups that
/// pprintast.ml rebuilds with `Ast_helper.Typ.tuple`.
fn print_type_tuple<W: Write>(f: &mut Formatter<W>, arena: &ParseArena, types: &[CoreTypeIdx]) {
    // OCaml: pp f "(%a)" (list (core_type1 ctxt) ~sep:"@;*@;") l
    f.string("(");
    for (i, t_idx) in types.iter().enumerate() {
        if i > 0 {
            f.space(); // @; before *
            f.string("*");
            f.space(); // @; after *
        }
        let t = arena.get_core_type(*t_idx);
        // Alias types inside tuple need parens for precedence
        let needs_parens = matches!(t.ptyp_desc, CoreTypeDesc::Ptyp_alias(..));
        if needs_parens {
            f.string("(");
        }
        print_core_type(f, arena, t);
        if needs_parens {
            f.string(")");
        }
    }
    f.string(")");
}
