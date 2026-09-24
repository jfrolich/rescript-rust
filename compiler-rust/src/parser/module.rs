//! Module parsing for ReScript.
//!
//! This module contains the module parsing logic, converting tokens
//! into module AST nodes (structures, signatures, module expressions, etc.).

use std::borrow::Cow;
use std::cell::RefCell;

use crate::location::Position;
use crate::parse_arena::{CoreTypeIdx, LidentIdx, LocIdx, Located, PosIdx, StrIdx};

// Import Location as alias to LocIdx from ast
use super::ast::Location;
use super::ast::*;
use super::core::{error_messages, is_es6_arrow_functor, mknoloc, recover, with_loc};
use super::diagnostics::DiagnosticCategory;
use super::expr;
use super::grammar;
use super::grammar::Grammar;
use super::longident::Longident;
use super::pattern;
use super::state::Parser;
use super::token::Token;
use super::typ;

// ============================================================================
// Consecutive Statement/Expression Checking
// ============================================================================

/// Check and emit "consecutive statements" error if statements on same line without semicolon.
///
/// Matches OCaml's `parse_newline_or_semicolon_structure`:
/// - If token is Semicolon, consume it
/// - If token can start a structure item AND on same line as previous, emit error
/// - Otherwise, do nothing
fn parse_newline_or_semicolon_structure(p: &mut Parser<'_>) {
    if p.token == Token::Semicolon {
        p.next();
        return;
    }

    if grammar::is_structure_item_start(&p.token) {
        // Check if we're on the same line as the previous token
        // OCaml: if p.prev_end_pos.pos_lnum < p.start_pos.pos_lnum then () else err
        if p.prev_end_pos.line >= p.start_pos.line {
            // Same line: emit error
            // Use err_at which respects regions (like OCaml's Parser.err)
            p.err_at(
                p.prev_end_pos.clone(),
                p.end_pos.clone(),
                DiagnosticCategory::message(
                    "Consecutive statements on a line must be separated by ';' or a newline",
                ),
            );
        }
    }
}

/// Check and emit "consecutive statements" error for signature items.
///
/// Matches OCaml's `parse_newline_or_semicolon_signature`:
/// - If token is Semicolon, consume it
/// - If token can start a signature item AND on same line as previous, emit error
/// - Otherwise, do nothing
fn parse_newline_or_semicolon_signature(p: &mut Parser<'_>) {
    if p.token == Token::Semicolon {
        p.next();
        return;
    }

    if grammar::is_signature_item_start(&p.token) {
        // Check if we're on the same line as the previous token
        // OCaml: if p.prev_end_pos.pos_lnum < p.start_pos.pos_lnum then () else err
        if p.prev_end_pos.line >= p.start_pos.line {
            // Same line: emit error
            // Use err_at which respects regions (like OCaml's Parser.err)
            p.err_at(
                p.prev_end_pos.clone(),
                p.end_pos.clone(),
                DiagnosticCategory::message(
                    "consecutive specifications on a line must be separated by ';' or a newline",
                ),
            );
        }
    }
}

// ============================================================================
// Inline Record Desugaring Context
// ============================================================================

/// Context for collecting inline record types during type declaration parsing.
/// Inline records like `type t = {permissions: {all: {stuff: bool}}}` get
/// desugared into separate type declarations with dotted names like `t.permissions.all`.
#[derive(Debug)]
pub struct InlineTypesContext {
    /// Collected inline types: (dotted_name as StrIdx, location, type_kind, params).
    ///
    /// OCaml compiler/syntax/src/res_core.ml:27-36 stores `params` on each
    /// inline type definition, so external inline records keep the parameter
    /// set from the moment that record was discovered.
    pub found_inline_types: Vec<(StrIdx, Location, TypeKind, Vec<(CoreTypeIdx, Variance)>)>,
    /// Type parameters from the outer type declaration
    pub params: Vec<(CoreTypeIdx, Variance)>,
    /// Location of the outer type's name (used for inline type declarations)
    pub outer_name_loc: Location,
}

impl InlineTypesContext {
    fn new(params: Vec<(CoreTypeIdx, Variance)>, outer_name_loc: Location) -> Self {
        Self {
            found_inline_types: vec![],
            params,
            outer_name_loc,
        }
    }
}

/// Parse label declarations using the parser's inline types context fields.
/// This is called from typ.rs when extracting inline records inside type constructor args.
pub fn parse_label_declarations_for_inline(
    p: &mut Parser<'_>,
    lbrace_pos_idx: Option<PosIdx>,
) -> Vec<LabelDeclaration> {
    // Create a temporary RefCell<InlineTypesContext> from parser fields
    // to reuse the existing parse_label_declarations logic.
    let found_stridx: Vec<(StrIdx, Location, TypeKind, Vec<(CoreTypeIdx, Variance)>)> =
        p.inline_types_found.take().unwrap_or_default();
    let inline_ctx = RefCell::new(InlineTypesContext {
        found_inline_types: found_stridx,
        params: p.inline_types_params.clone(),
        outer_name_loc: Location::none(),
    });
    // Convert current_type_name_path from Vec<String> to Vec<StrIdx>
    let current_path_strings = p.current_type_name_path.clone();
    let current_path: Option<Vec<StrIdx>> = current_path_strings
        .map(|path| path.into_iter().map(|s| p.arena_mut().intern(&s)).collect());

    let labels =
        parse_label_declarations(p, Some(&inline_ctx), current_path.as_ref(), lbrace_pos_idx);

    // Copy back any found inline types to the parser fields.
    let ctx = inline_ctx.into_inner();
    let InlineTypesContext {
        found_inline_types,
        params,
        ..
    } = ctx;
    p.inline_types_found = Some(found_inline_types);
    p.inline_types_params = params;

    labels
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Convert a module type to a package type (for Ptyp_package).
/// For a simple module type identifier like `T`, creates `(T, [])`.
/// For `T with type t = int`, creates `(T, [(t, int)])`.
fn module_type_to_package(p: &mut Parser<'_>, mt: &ModuleType) -> PackageType {
    match &*mt.pmty_desc {
        ModuleTypeDesc::Pmty_ident(lid) => (lid.clone(), vec![]),
        ModuleTypeDesc::Pmty_with(inner) => {
            let (ref base_idx, ref constraints) = **inner;
            // For "T with type t = int", extract base identifier and constraints
            let base = p.arena().get_mod_type(*base_idx);
            let lid = if let ModuleTypeDesc::Pmty_ident(lid) = &*base.pmty_desc {
                lid.clone()
            } else {
                let lid_idx = p.push_lident_static("_");
                with_loc(lid_idx, mt.pmty_loc.clone())
            };

            // Convert WithConstraint to package type constraints
            let pkg_constraints: Vec<(Loc<LidentIdx>, CoreTypeIdx)> = constraints
                .iter()
                .filter_map(|c| match c {
                    WithConstraint::Pwith_type(type_lid, type_decl) => {
                        // Extract the manifest type from the type declaration
                        type_decl
                            .ptype_manifest
                            .as_ref()
                            .map(|manifest| (type_lid.clone(), manifest.clone()))
                    }
                    WithConstraint::Pwith_typesubst(type_lid, type_decl) => {
                        // Type substitution also has a manifest
                        type_decl
                            .ptype_manifest
                            .as_ref()
                            .map(|manifest| (type_lid.clone(), manifest.clone()))
                    }
                    // Module constraints are not relevant for package types
                    _ => None,
                })
                .collect();

            (lid, pkg_constraints)
        }
        _ => {
            let lid_idx = p.push_lident_static("_");
            (with_loc(lid_idx, mt.pmty_loc.clone()), vec![])
        }
    }
}

// ============================================================================
// Structure (Implementation) Parsing
// ============================================================================

/// Parse a structure (list of structure items).
/// Matches OCaml's parse_implementation which uses parse_region.
/// Note: OCaml does NOT create regions per structure item - the region is shared
/// so that after one error, subsequent errors in the same region are silenced.
pub fn parse_structure(p: &mut Parser<'_>) -> Structure {
    // OCaml uses parse_region with Grammar::Implementation
    p.leave_breadcrumb(Grammar::Implementation);

    let mut items = vec![];

    loop {
        if let Some(item) = p.pending_structure_items.pop() {
            items.push(item);
            continue;
        }
        if p.token == Token::Eof {
            break;
        }
        if let Some(item) = parse_structure_item(p) {
            items.push(item);
        } else {
            use super::core::recover::should_abort_list_parse;

            if p.token == Token::Eof || should_abort_list_parse(p) {
                break;
            }

            // OCaml compiler/syntax/src/res_core.ml:1213-1227 and
            // compiler/syntax/src/res_core.ml:7748-7752 implement top-level
            // structures with parse_region, which reports unexpected tokens
            // instead of pre-skipping extra semicolons.
            p.err_unexpected();
            p.next();
        }
    }

    p.eat_breadcrumb();
    items
}

/// Parse a single structure item.
pub fn parse_structure_item(p: &mut Parser<'_>) -> Option<StructureItem> {
    // Save start position as PosIdx to enable sharing with inner locations
    let start_pos_idx = p.start_pos_idx();
    let start_pos = p.start_pos;

    // Parse attributes
    let attrs = parse_attributes(p);

    // Track the PosIdx used for this structure item's location
    // For Pstr_value, this will be the same as the first binding's start
    let item_start_idx = start_pos_idx;
    // Track shared LocIdx for when we want to share the entire location (e.g., with value_binding)
    let mut item_loc_idx: Option<LocIdx> = None;

    let desc = match &p.token {
        Token::Open => {
            // OCaml's popen_loc starts at 'open', not at outer attributes
            let open_start_idx = p.start_pos_idx();
            p.next();
            // Check for open! override flag
            let override_flag = if p.token == Token::Bang {
                p.next();
                OverrideFlag::Override
            } else {
                OverrideFlag::Fresh
            };
            let lid = parse_module_long_ident(p);
            let loc = p.mk_loc_idx_to_prev_end(open_start_idx);
            parse_newline_or_semicolon_structure(p);
            Some(StructureItemDesc::Pstr_open(Box::new(OpenDescription {
                popen_lid: lid,
                popen_override: override_flag,
                popen_loc: loc,
                popen_attributes: attrs.clone(),
            })))
        }
        Token::Let { unwrap } => {
            let unwrap = *unwrap;
            p.next();
            // PosIdx after let?/let? rec for let.unwrap attribute location.
            // OCaml uses p.start_pos after optional `rec`.
            let mut let_end_pos_idx = p.start_pos_idx();
            let rec_flag = if p.token == Token::Rec {
                p.next();
                let_end_pos_idx = p.start_pos_idx();
                RecFlag::Recursive
            } else {
                RecFlag::Nonrecursive
            };
            // Check for let? rec combination - not allowed
            // OCaml: if rec_flag = Asttypes.Recursive && unwrap then emit error
            if rec_flag == RecFlag::Recursive && unwrap {
                // Error location: from start of `let?` to start of next token after `rec`
                p.err_at(
                    start_pos.clone(),
                    p.start_pos.clone(),
                    DiagnosticCategory::Message(
                        "let? is not allowed to be recursive. Use a regular `let` or remove `rec`."
                            .to_string(),
                    ),
                );
            }
            // Pass start_pos_idx to enable position sharing with structure_item
            let (bindings, _binding_loc_idx) = parse_let_bindings(
                p,
                start_pos_idx,
                let_end_pos_idx,
                rec_flag,
                attrs.clone(),
                unwrap,
            );
            parse_newline_or_semicolon_structure(p);
            // Don't share LocIdx - OCaml creates separate Location objects for pstr_loc and pvb_loc.
            // The internal positions (PosIdx) are shared, but the Location records themselves are separate.
            Some(StructureItemDesc::Pstr_value(Box::new((
                rec_flag, bindings,
            ))))
        }
        Token::Typ => {
            // OCaml uses begin_region/end_region around type parsing
            // This allows errors within one type definition to be de-duplicated,
            // but errors from different type definitions can both be reported.
            p.begin_region();

            // Get the position for the type declaration start.
            // If attributes were parsed (including doc comments), we need a fresh PosIdx
            // at the 'type' keyword position. If no attributes, we reuse item_start_idx
            // to maintain binary sharing (the positions are the same).
            let type_start_idx = if attrs.is_empty() {
                item_start_idx
            } else {
                p.start_pos_idx()
            };
            let result = parse_type_definition_or_extension(p, &attrs, type_start_idx);
            // OCaml `parse_structure_item_region` (res_core.ml:6666-6678).
            parse_newline_or_semicolon_structure(p);
            p.end_region();
            result
        }
        Token::External => {
            p.next();
            // Use item_start_idx (which equals start_pos_idx) to share position with pstr_loc
            let (vd, inline_types) =
                parse_external_value_description(p, attrs.clone(), item_start_idx);
            parse_newline_or_semicolon_structure(p);
            if inline_types.is_empty() {
                Some(StructureItemDesc::Pstr_primitive(Box::new(vd)))
            } else {
                // OCaml compiler/syntax/src/res_core.ml:6729-6741 emits the
                // generated inline type item first, then queues the primitive.
                let loc = p.mk_loc_idx_to_prev_end(item_start_idx);
                item_loc_idx = Some(loc.clone());
                p.pending_structure_items.push(StructureItem {
                    pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(vd))),
                    pstr_loc: loc,
                });
                Some(StructureItemDesc::Pstr_type(Box::new((
                    RecFlag::Recursive,
                    inline_types,
                ))))
            }
        }
        Token::Exception => {
            // Capture start position BEFORE consuming 'exception' for accurate location
            let exception_start_idx = p.start_pos_idx();
            p.next();
            let ext = parse_extension_constructor(p, attrs.clone(), Some(exception_start_idx));
            parse_newline_or_semicolon_structure(p);
            Some(StructureItemDesc::Pstr_exception(Box::new(ext)))
        }
        Token::Module => {
            // OCaml uses begin_region/end_region around module parsing
            p.begin_region();

            // Capture module_start BEFORE consuming 'module' for accurate locations
            let module_start_idx = p.start_pos_idx();
            p.next();
            // Check for first-class module expression: module(...)
            let result = if p.token == Token::Lparen {
                // Parse the first-class module, then continue with primary/binary parsing
                let pack_expr =
                    super::expr::parse_first_class_module_expr_from_paren(p, start_pos_idx);
                // Continue parsing the expression (handles ->, [], etc.)
                let expr = super::expr::parse_expr_with_operand(p, pack_expr);
                parse_newline_or_semicolon_structure(p);
                let expr_idx = p.arena_mut().push_expr(expr);
                Some(StructureItemDesc::Pstr_eval(Box::new((
                    expr_idx,
                    attrs.clone(),
                ))))
            } else {
                let def = parse_module_definition(p, module_start_idx, attrs.clone());
                parse_newline_or_semicolon_structure(p);
                def
            };

            p.end_region();
            result
        }
        Token::Include => {
            // OCaml: parse_include_statement captures start_pos before consuming Include
            let include_start_idx = p.start_pos_idx();
            p.next();
            let mod_expr = parse_module_expr(p);
            parse_newline_or_semicolon_structure(p);
            let mod_expr_idx = p.arena_mut().push_mod_expr(mod_expr);
            Some(StructureItemDesc::Pstr_include(Box::new(
                IncludeDeclaration {
                    pincl_mod: mod_expr_idx,
                    pincl_loc: p.mk_loc_idx_to_prev_end(include_start_idx),
                    pincl_attributes: attrs.clone(),
                },
            )))
        }
        Token::At | Token::AtAt => {
            // Floating attribute or extension
            // Capture start_pos before consuming @ or @@ so attribute location includes it
            let attr_start_idx = p.start_pos_idx();
            if p.token == Token::AtAt {
                p.next();
                let attr = parse_attribute_body(p, attr_start_idx);
                parse_newline_or_semicolon_structure(p);
                Some(StructureItemDesc::Pstr_attribute(Box::new(attr)))
            } else {
                // @ might be a doc comment or similar
                p.next();
                let attr = parse_attribute_body(p, attr_start_idx);
                parse_newline_or_semicolon_structure(p);
                Some(StructureItemDesc::Pstr_attribute(Box::new(attr)))
            }
        }
        Token::ModuleComment { content, .. } => {
            // Module-level doc comment (triple star /*** ... */) becomes a standalone res.doc attribute
            let content = content.clone();
            let doc_start_idx = p.start_pos_idx();
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(doc_start_idx);
            item_loc_idx = Some(loc);
            let attr = super::core::doc_comment_to_attribute(p.arena_mut(), loc, content);
            Some(StructureItemDesc::Pstr_attribute(Box::new(attr)))
        }
        Token::PercentPercent => {
            // Structure-level extension (%%raw(...), %%private(...), etc.)
            // Capture start position BEFORE consuming %% so extension location includes it
            let ext_start_idx = p.start_pos_idx();
            p.next();
            let id = parse_extension_id(p, ext_start_idx);
            // Parse optional payload
            let is_adjacent = p.start_pos.cnum == p.prev_end_pos.cnum;
            let payload = if p.token == Token::Lparen && is_adjacent {
                p.next();
                let payload = parse_payload(p);
                p.expect(Token::Rparen);
                payload
            } else {
                Payload::PStr(Box::new(vec![]))
            };
            parse_newline_or_semicolon_structure(p);
            Some(StructureItemDesc::Pstr_extension(Box::new((
                (id, payload),
                attrs.clone(),
            ))))
        }
        _ => {
            // Could be an expression
            if is_expr_start(&p.token) {
                let expr = expr::parse_expr(p);
                parse_newline_or_semicolon_structure(p);
                let expr_idx = p.arena_mut().push_expr(expr);
                Some(StructureItemDesc::Pstr_eval(Box::new((
                    expr_idx,
                    attrs.clone(),
                ))))
            } else if let Some(attr) = attrs.first() {
                // OCaml: when attrs are present but no valid item follows,
                // report the "Did you forget to attach" error and produce exprhole
                let attr_name_str = p.arena().get_string(attr.0.txt).to_string();
                let attr_loc = p.to_location(attr.0.loc);
                p.err_at(
                    attr_loc.loc_start.clone(),
                    attr_loc.loc_end.clone(),
                    DiagnosticCategory::message(&error_messages::attribute_without_node(
                        &attr_name_str,
                    )),
                );
                let expr = expr::parse_expr(p);
                parse_newline_or_semicolon_structure(p);
                let expr_idx = p.arena_mut().push_expr(expr);
                Some(StructureItemDesc::Pstr_eval(Box::new((
                    expr_idx,
                    attrs.clone(),
                ))))
            } else {
                // OCaml compiler/syntax/src/res_core.ml:6789-6798 returns
                // None for an unrecognized structure-item token; the
                // surrounding parse_region/parse_delimited_region reports the
                // unexpected token and advances.
                None
            }
        }
    };

    desc.map(|d| StructureItem {
        pstr_desc: Box::new(d),
        pstr_loc: match item_loc_idx {
            Some(loc_idx) => loc_idx,
            None => p.mk_loc_idx_to_prev_end(item_start_idx),
        },
    })
}

/// OCaml `TypeDef`/`TypeExt` (compiler/syntax/src/res_core.ml:311-315).
pub(super) enum TypeDefOrExt {
    TypeDef(RecFlag, Vec<TypeDeclaration>),
    TypeExt(TypeExtension),
}

/// OCaml `parse_type_definition_or_extension` (compiler/syntax/src/res_core.ml:6487-6535).
/// `type_start_idx` is the position of the `type` keyword.
pub(super) fn parse_type_definition_or_extension_item(
    p: &mut Parser<'_>,
    attrs: &Attributes,
    type_start_idx: crate::parse_arena::PosIdx,
) -> TypeDefOrExt {
    p.expect(Token::Typ);
    let rec_flag = match &p.token {
        Token::Rec => {
            p.next();
            RecFlag::Recursive
        }
        Token::Lident(s) if s == "nonrec" => {
            p.next();
            RecFlag::Nonrecursive
        }
        _ => RecFlag::Nonrecursive,
    };
    let (path, name_loc) = parse_value_path(p);
    let params = parse_type_params(p, &path);
    if p.token == Token::PlusEqual {
        let lid_idx = super::core::build_longident_idx(p, &path);
        let name = with_loc(lid_idx, name_loc);
        return TypeDefOrExt::TypeExt(parse_type_extension(p, params, attrs.clone(), name));
    }
    // The shape of a type name should be `Lident`: `t` is accepted, `User.t` is not.
    let last = path.last().cloned().unwrap_or_default();
    if path.len() > 1 {
        let loc = p.arena().to_location(name_loc);
        p.err_at(
            loc.loc_start,
            loc.loc_end,
            DiagnosticCategory::Message(format!(
                "A type declaration's name cannot contain a module access. Did you mean `{last}`?"
            )),
        );
    }
    let (decls, has_inline_types) = parse_type_definitions(
        p,
        attrs.clone(),
        with_loc(last, name_loc),
        params,
        type_start_idx,
    );
    let rec_flag = if has_inline_types {
        RecFlag::Recursive
    } else {
        rec_flag
    };
    TypeDefOrExt::TypeDef(rec_flag, decls)
}

pub(super) fn parse_type_definition_or_extension(
    p: &mut Parser<'_>,
    attrs: &Attributes,
    type_start_idx: crate::parse_arena::PosIdx,
) -> Option<StructureItemDesc> {
    Some(
        match parse_type_definition_or_extension_item(p, attrs, type_start_idx) {
            TypeDefOrExt::TypeDef(rec_flag, decls) => {
                StructureItemDesc::Pstr_type(Box::new((rec_flag, decls)))
            }
            TypeDefOrExt::TypeExt(ext) => StructureItemDesc::Pstr_typext(Box::new(ext)),
        },
    )
}

/// OCaml `parse_value_path` (compiler/syntax/src/res_core.ml:742-776). An
/// uppercase path is followed by `next_unsafe`, which consumes one more token.
pub(super) fn parse_value_path(p: &mut Parser<'_>) -> (Vec<String>, LocIdx) {
    let start_pos_idx = p.start_pos_idx();
    let path = match &p.token {
        Token::Lident(ident) => {
            let ident = ident.to_string();
            p.next();
            vec![ident]
        }
        Token::Uident(_) => parse_value_path_for_type(p).0,
        _ => {
            p.err_unexpected();
            p.next_unsafe();
            vec!["_".to_string()]
        }
    };
    (path, p.mk_loc_idx_to_prev_end(start_pos_idx))
}

/// OCaml `parse_type_params ~parent` (compiler/syntax/src/res_core.ml:5749-5790).
fn parse_type_params(p: &mut Parser<'_>, parent: &[String]) -> Vec<(CoreTypeIdx, Variance)> {
    let opening = p.token.clone().into_owned();
    if !matches!(opening, Token::LessThan | Token::Lparen)
        || p.start_pos.line != p.prev_end_pos.line
    {
        return vec![];
    }
    p.set_diamond_mode();
    let opening_start = p.start_pos.clone();
    p.leave_breadcrumb(Grammar::TypeParams);
    p.next();
    let params = super::core::parse_comma_delimited_region(
        p,
        Grammar::TypeParams,
        Token::GreaterThan,
        parse_type_param,
    );
    if p.token == Token::Rparen && opening == Token::Lparen {
        let suggested = format_type_with_angle_brackets(p, &parent.join("."), &params);
        let end = p.end_pos.clone();
        p.err_at(
            opening_start,
            end,
            DiagnosticCategory::Message(format!(
                "Type parameters require angle brackets:\n  {suggested}"
            )),
        );
        p.next();
    } else {
        p.expect(Token::GreaterThan);
    }
    p.pop_diamond_mode();
    p.eat_breadcrumb();
    params
}

/// OCaml `parse_type_definitions` (compiler/syntax/src/res_core.ml:6459-6481):
/// the first declaration continues after the already parsed name and params;
/// each `and` declaration goes through `parse_type_def`. Returns the inline
/// record declarations found in the first declaration ahead of the others.
fn parse_type_definitions(
    p: &mut Parser<'_>,
    attrs: Attributes,
    name: Located<String>,
    params: Vec<(CoreTypeIdx, Variance)>,
    start_idx: crate::parse_arena::PosIdx,
) -> (Vec<TypeDeclaration>, bool) {
    let inline_ctx = RefCell::new(InlineTypesContext::new(vec![], Location::none()));
    let first =
        parse_type_declaration_body(p, attrs, Some(&inline_ctx), start_idx, name, params);
    let mut decls = vec![];
    let ctx = inline_ctx.into_inner();
    let has_inline_types = !ctx.found_inline_types.is_empty();
    if has_inline_types {
        let inline_str_idx = p.arena_mut().intern("res.inlineRecordDefinition");
        let inline_attr: Attribute = (mknoloc(inline_str_idx), Payload::PStr(Box::new(vec![])));
        for (inline_name_idx, loc, type_kind, params) in ctx.found_inline_types.iter() {
            decls.push(TypeDeclaration {
                ptype_name: with_loc(*inline_name_idx, ctx.outer_name_loc.clone()),
                ptype_params: params.clone(),
                ptype_cstrs: vec![],
                ptype_kind: type_kind.clone(),
                ptype_private: PrivateFlag::Public,
                ptype_manifest: None,
                ptype_attributes: Attributes::from_vec(vec![inline_attr.clone()]),
                ptype_loc: loc.clone(),
            });
        }
    }
    decls.extend(first);
    loop {
        let start_idx = p.start_pos_idx();
        let attrs = parse_attributes_and_binding(p);
        if p.token != Token::And {
            break;
        }
        p.next();
        decls.extend(parse_type_def(p, attrs, start_idx));
    }
    (decls, has_inline_types)
}

/// OCaml `parse_type_def` (compiler/syntax/src/res_core.ml:6402-6421).
fn parse_type_def(
    p: &mut Parser<'_>,
    attrs: Attributes,
    start_idx: crate::parse_arena::PosIdx,
) -> Option<TypeDeclaration> {
    p.leave_breadcrumb(Grammar::TypeDef);
    p.leave_breadcrumb(Grammar::TypeConstrName);
    let (name, loc) = super::core::parse_lident(p);
    p.eat_breadcrumb();
    let params = parse_type_params(p, std::slice::from_ref(&name));
    let decl = parse_type_declaration_body(p, attrs, None, start_idx, with_loc(name, loc), params);
    p.eat_breadcrumb();
    decl
}

/// OCaml `parse_type_extension ~params ~attrs ~name` (compiler/syntax/src/res_core.ml:6423-6457).
fn parse_type_extension(
    p: &mut Parser<'_>,
    params: Vec<(CoreTypeIdx, Variance)>,
    attrs: Attributes,
    name: Loc<LidentIdx>,
) -> TypeExtension {
    p.expect(Token::PlusEqual);
    let private = if p.optional(&Token::Private) {
        PrivateFlag::Private
    } else {
        PrivateFlag::Public
    };
    let constructors = parse_type_extension_constructors(p);
    TypeExtension {
        ptyext_path: name,
        ptyext_params: params,
        ptyext_constructors: constructors,
        ptyext_private: private,
        ptyext_attributes: attrs,
    }
}

// ============================================================================
// Signature Parsing
// ============================================================================

/// Parse a signature (list of signature items).
///
/// This matches OCaml's `parse_region p ~grammar:Grammar.Specification ~f:parse_signature_item_region`.
/// When a signature item cannot be parsed (returns None), we emit an "unexpected" error and
/// advance the token to avoid infinite loops.
pub fn parse_signature(p: &mut Parser<'_>) -> Signature {
    use super::core::recover::should_abort_list_parse;
    use super::grammar::Grammar;

    // OCaml: Parser.leave_breadcrumb p Grammar.Specification
    p.leave_breadcrumb(Grammar::Specification);

    let mut items = vec![];

    loop {
        if let Some(item) = p.pending_signature_items.pop() {
            items.push(item);
            continue;
        }
        // Skip semicolons
        while p.token == Token::Semicolon {
            p.next();
        }

        match parse_signature_item(p) {
            Some(item) => items.push(item),
            None => {
                // OCaml's parse_region: when f returns None, check if we should abort
                if p.token == Token::Eof || should_abort_list_parse(p) {
                    break;
                }
                // Emit unexpected token error and advance to avoid infinite loop
                p.err_unexpected();
                p.next();
            }
        }
    }

    // OCaml: Parser.eat_breadcrumb p
    p.eat_breadcrumb();

    items
}

/// Parse a single signature item.
pub fn parse_signature_item(p: &mut Parser<'_>) -> Option<SignatureItem> {
    let start_pos_idx = p.start_pos_idx();
    let mut item_loc_idx: Option<LocIdx> = None;

    // Parse attributes
    let attrs = parse_attributes(p);

    let desc = match &p.token {
        Token::Open => {
            // OCaml's popen_loc starts at 'open', not at outer attributes
            let open_start_idx = p.start_pos_idx();
            p.next();
            // Check for override flag: open! M
            let override_flag = if p.token == Token::Bang {
                p.next();
                OverrideFlag::Override
            } else {
                OverrideFlag::Fresh
            };
            let lid = parse_module_long_ident(p);
            parse_newline_or_semicolon_signature(p);
            let loc = p.mk_loc_idx_to_prev_end(open_start_idx);
            Some(SignatureItemDesc::Psig_open(Box::new(OpenDescription {
                popen_lid: lid,
                popen_override: override_flag,
                popen_loc: loc,
                popen_attributes: attrs.clone(),
            })))
        }
        Token::Let { unwrap } => {
            let unwrap = *unwrap;
            // For signature let declarations, OCaml uses regions
            p.begin_region();
            // OCaml's value_description location starts at 'let', not at the attributes
            let let_pos_idx = p.start_pos_idx();
            // If unwrap (let?), emit error - not allowed in signatures
            if unwrap {
                p.err_at(
                    p.arena().get_position(start_pos_idx).clone(),
                    p.end_pos.clone(),
                    DiagnosticCategory::Message(
                        "let? is not allowed in signatures. Use a regular `let` instead."
                            .to_string(),
                    ),
                );
            }
            p.next();
            let vd = parse_value_description(p, attrs.clone(), let_pos_idx, true);
            parse_newline_or_semicolon_signature(p);
            p.end_region();
            Some(SignatureItemDesc::Psig_value(Box::new(vd)))
        }
        Token::Typ => {
            // OCaml uses regions around type parsing in signatures
            p.begin_region();
            // Get the position for the type declaration start.
            // If attributes were parsed (including doc comments), we need a fresh PosIdx
            // at the 'type' keyword position. If no attributes, we reuse start_pos_idx
            // to maintain binary sharing (the positions are the same).
            let type_start_idx = if attrs.is_empty() {
                start_pos_idx
            } else {
                p.start_pos_idx()
            };
            let result = match parse_type_definition_or_extension_item(p, &attrs, type_start_idx) {
                TypeDefOrExt::TypeExt(ext) => {
                    parse_newline_or_semicolon_signature(p);
                    Some(SignatureItemDesc::Psig_typext(Box::new(ext)))
                }
                TypeDefOrExt::TypeDef(rec_flag, decls) => {
                    parse_newline_or_semicolon_signature(p);
                    Some(SignatureItemDesc::Psig_type(Box::new((rec_flag, decls))))
                }
            };
            p.end_region();
            result
        }
        Token::External => {
            p.next();
            // Use start_pos_idx to share position with psig_loc
            let (vd, inline_types) =
                parse_external_value_description(p, attrs.clone(), start_pos_idx);
            parse_newline_or_semicolon_signature(p);
            if inline_types.is_empty() {
                Some(SignatureItemDesc::Psig_value(Box::new(vd)))
            } else {
                // OCaml compiler/syntax/src/res_core.ml:7383-7395 emits the
                // generated inline type item first, then queues the value item.
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                item_loc_idx = Some(loc.clone());
                p.pending_signature_items.push(SignatureItem {
                    psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(vd))),
                    psig_loc: loc,
                });
                Some(SignatureItemDesc::Psig_type(Box::new((
                    RecFlag::Recursive,
                    inline_types,
                ))))
            }
        }
        Token::Exception => {
            // Capture start position BEFORE consuming 'exception' for accurate location
            let exception_start_idx = p.start_pos_idx();
            p.next();
            let ext = parse_extension_constructor(p, attrs.clone(), Some(exception_start_idx));
            parse_newline_or_semicolon_signature(p);
            Some(SignatureItemDesc::Psig_exception(Box::new(ext)))
        }
        Token::Module => {
            // OCaml uses regions around module parsing in signatures
            p.begin_region();
            let _module_start_idx = p.start_pos_idx();
            p.next();
            let result = if p.token == Token::Typ {
                p.next();
                let mtd = parse_module_type_declaration(p, attrs.clone(), false);
                // No parse_newline_or_semicolon_signature for module type - matches OCaml
                Some(SignatureItemDesc::Psig_modtype(Box::new(mtd)))
            } else if p.token == Token::Rec {
                p.next();
                // For recursive modules, OCaml's pmd_loc includes attributes BEFORE 'module rec'
                // OCaml passes start_pos (captured BEFORE attributes) to parse_rec_module_spec
                let mds = parse_rec_module_declarations(p, attrs.clone(), start_pos_idx);
                parse_newline_or_semicolon_signature(p);
                Some(SignatureItemDesc::Psig_recmodule(Box::new(mds)))
            } else {
                // For non-recursive modules, location starts at name (not 'module')
                let md = parse_module_declaration(p, attrs.clone(), None);
                parse_newline_or_semicolon_signature(p);
                Some(SignatureItemDesc::Psig_module(Box::new(md)))
            };
            p.end_region();
            result
        }
        Token::Include => {
            p.next();
            let mod_type = parse_module_type(p);
            parse_newline_or_semicolon_signature(p);
            let mod_type_idx = p.arena_mut().push_mod_type(mod_type);
            Some(SignatureItemDesc::Psig_include(Box::new(
                IncludeDescription {
                    pincl_mod: mod_type_idx,
                    pincl_loc: p.mk_loc_idx_to_prev_end(start_pos_idx),
                    pincl_attributes: attrs.clone(),
                },
            )))
        }
        Token::At | Token::AtAt => {
            // Capture start_pos before consuming @ or @@ so attribute location includes it
            let attr_start_idx = p.start_pos_idx();
            if p.token == Token::AtAt {
                p.next();
                let attr = parse_attribute_body(p, attr_start_idx);
                parse_newline_or_semicolon_signature(p);
                Some(SignatureItemDesc::Psig_attribute(Box::new(attr)))
            } else {
                p.next();
                let attr = parse_attribute_body(p, attr_start_idx);
                parse_newline_or_semicolon_signature(p);
                Some(SignatureItemDesc::Psig_attribute(Box::new(attr)))
            }
        }
        Token::ModuleComment { content, .. } => {
            // Module-level doc comment (triple star /*** ... */) becomes a standalone res.doc attribute
            // Note: OCaml does NOT call parse_newline_or_semicolon_signature for ModuleComment
            let content = content.clone();
            let doc_start_idx = p.start_pos_idx();
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(doc_start_idx);
            let attr = super::core::doc_comment_to_attribute(p.arena_mut(), loc, content);
            // OCaml uses the same `loc` pointer for both Psig_attribute and the attr itself.
            item_loc_idx = Some(loc);
            Some(SignatureItemDesc::Psig_attribute(Box::new(attr)))
        }
        Token::Percent | Token::PercentPercent => {
            let ext = parse_extension(p);
            parse_newline_or_semicolon_signature(p);
            Some(SignatureItemDesc::Psig_extension(Box::new((
                ext,
                attrs.clone(),
            ))))
        }
        _ => {
            // OCaml: when attrs are present but no valid item follows, report the error
            // and return a sigitemhole placeholder
            if let Some(attr) = attrs.first() {
                let attr_name_str = p.arena().get_string(attr.0.txt).to_string();
                let attr_loc = p.to_location(attr.0.loc);
                p.err_at(
                    attr_loc.loc_start.clone(),
                    attr_loc.loc_end.clone(),
                    DiagnosticCategory::message(&error_messages::attribute_without_node(
                        &attr_name_str,
                    )),
                );
                // Return sigitemhole as recovery
                return Some(super::core::recover::default_signature_item(p.arena_mut()));
            }
            None
        }
    };

    desc.map(|d| {
        // OCaml includes optional trailing semicolon in signature_item location
        let end_pos_idx = if p.token == Token::Semicolon {
            p.end_pos_idx()
        } else {
            p.prev_end_pos_idx()
        };
        let psig_loc = match item_loc_idx {
            Some(loc_idx)
                if p.loc_start_idx(loc_idx) == start_pos_idx
                    && p.loc_end_idx(loc_idx) == end_pos_idx =>
            {
                loc_idx
            }
            _ => p.mk_loc_idx(start_pos_idx, end_pos_idx),
        };
        SignatureItem {
            psig_desc: Box::new(d),
            psig_loc,
        }
    })
}

// ============================================================================
// Module Expression Parsing
// ============================================================================

/// Parse a module expression.
pub fn parse_module_expr(p: &mut Parser<'_>) -> ModuleExpr {
    let start_pos_idx = p.start_pos_idx();

    // Handle await keyword
    // OCaml lines 6622-6629: capture await start_pos BEFORE consuming, end_pos AFTER consuming
    // NOTE: OCaml uses p.end_pos after consuming await, which is the end of the NEXT token
    let await_loc = if p.token == Token::Await {
        let await_start_idx = p.start_pos_idx();
        p.next();
        // OCaml: let end_pos = p.end_pos in - this is the end of the token AFTER await
        let await_end_idx = p.end_pos_idx();
        Some(p.mk_loc_idx(await_start_idx, await_end_idx))
    } else {
        None
    };

    // Parse attributes (e.g., @functorAttr)
    let mut attrs = parse_attributes(p);

    // Add await attribute if present
    // OCaml line 6632: make_await_attr loc_await
    if let Some(loc) = await_loc {
        let await_idx = p.arena_mut().intern("res.await");
        attrs.insert(
            0,
            (
                Located {
                    txt: await_idx,
                    loc,
                },
                Payload::PStr(Box::new(vec![])),
            ),
        );
    }

    // Check if this is a functor: (args) => body or (args) : type => body
    // For primary expressions, capture start_pos for location override (OCaml line 6503)
    let (expr, primary_start_pos_idx) = if is_es6_arrow_functor(p) {
        (parse_functor_module_expr(p), None)
    } else {
        let primary_start_idx = p.start_pos_idx();
        (parse_primary_module_expr(p), Some(primary_start_idx))
    };

    // Handle module application: F(X)
    let mut expr = parse_module_apply(p, expr);

    // OCaml line 6512: {mod_expr with pmod_loc = mk_loc start_pos p.prev_end_pos}
    // Override the outermost location after module application processing
    if let Some(primary_start_idx) = primary_start_pos_idx {
        expr.pmod_loc = p.mk_loc_idx_to_prev_end(primary_start_idx);
    }

    // Handle module constraint: M : S
    let expr = if p.token == Token::Colon {
        p.next();
        let mod_type = parse_module_type(p);
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let expr_idx = p.arena_mut().push_mod_expr(expr);
        let mod_type_idx = p.arena_mut().push_mod_type(mod_type);
        ModuleExpr {
            pmod_desc: Box::new(ModuleExprDesc::Pmod_constraint(expr_idx, mod_type_idx)),
            pmod_loc: loc,
            pmod_attributes: Attributes::new(),
        }
    } else {
        expr
    };

    // Attach attributes to the module expression
    if attrs.is_empty() {
        expr
    } else {
        let mut combined_attrs = expr.pmod_attributes.clone();
        combined_attrs.extend(attrs);
        ModuleExpr {
            pmod_attributes: combined_attrs,
            ..expr
        }
    }
}

/// Parse a module expression without consuming a trailing `: type` constraint.
/// Used for first-class modules where the constraint becomes Pexp_constraint + Ptyp_package.
pub fn parse_module_expr_without_constraint(p: &mut Parser<'_>) -> ModuleExpr {
    let _start_pos_idx = p.start_pos_idx();

    // Handle await keyword
    // OCaml lines 6622-6629: capture await start_pos BEFORE consuming, end_pos AFTER consuming
    // NOTE: OCaml uses p.end_pos after consuming await, which is the end of the NEXT token
    let await_loc = if p.token == Token::Await {
        let await_start_idx = p.start_pos_idx();
        p.next();
        // OCaml: let end_pos = p.end_pos in - this is the end of the token AFTER await
        let await_end_idx = p.end_pos_idx();
        Some(p.mk_loc_idx(await_start_idx, await_end_idx))
    } else {
        None
    };

    // Parse attributes (e.g., @functorAttr)
    let mut attrs = parse_attributes(p);

    // Add await attribute if present
    // OCaml line 6632: make_await_attr loc_await
    if let Some(loc) = await_loc {
        let await_idx = p.arena_mut().intern("res.await");
        attrs.insert(
            0,
            (
                Located {
                    txt: await_idx,
                    loc,
                },
                Payload::PStr(Box::new(vec![])),
            ),
        );
    }

    // Check if this is a functor: (args) => body or (args) : type => body
    // For primary expressions, capture start_pos for location override (OCaml line 6503)
    let (expr, primary_start_pos_idx) = if is_es6_arrow_functor(p) {
        (parse_functor_module_expr(p), None)
    } else {
        let primary_start_idx = p.start_pos_idx();
        (parse_primary_module_expr(p), Some(primary_start_idx))
    };

    // Handle module application: F(X)
    let mut expr = parse_module_apply(p, expr);

    // OCaml line 6512: {mod_expr with pmod_loc = mk_loc start_pos p.prev_end_pos}
    // Override the outermost location after module application processing
    if let Some(primary_start_idx) = primary_start_pos_idx {
        expr.pmod_loc = p.mk_loc_idx_to_prev_end(primary_start_idx);
    }

    // NOTE: We intentionally DON'T handle `: type` constraint here

    // Attach attributes to the module expression
    if attrs.is_empty() {
        expr
    } else {
        let mut combined_attrs = expr.pmod_attributes.clone();
        combined_attrs.extend(attrs);
        ModuleExpr {
            pmod_attributes: combined_attrs,
            ..expr
        }
    }
}

/// Parse a primary module expression.
fn parse_primary_module_expr(p: &mut Parser<'_>) -> ModuleExpr {
    let start_pos_idx = p.start_pos_idx();

    match &p.token {
        Token::Uident(_) => {
            // Module path - use lid.loc directly (OCaml: Ast_helper.Mod.ident ~loc:longident.loc)
            let lid = parse_module_long_ident(p);
            ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_ident(lid.clone())),
                pmod_loc: lid.loc,
                pmod_attributes: Attributes::new(),
            }
        }
        Token::Lbrace => {
            // Module structure: { ... }
            p.next();
            let items = parse_structure_in_braces(p);
            p.expect(Token::Rbrace);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(items))),
                pmod_loc: loc,
                pmod_attributes: Attributes::new(),
            }
        }
        Token::Lparen => {
            // Check if this is a functor: (args) => body or (args) : type => body
            if is_es6_arrow_functor(p) {
                parse_functor_module_expr(p)
            } else {
                // Parenthesized module expression
                p.next();
                if p.token == Token::Rparen {
                    // Unit module expression: ()
                    p.next();
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    ModuleExpr {
                        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(vec![]))),
                        pmod_loc: loc,
                        pmod_attributes: Attributes::new(),
                    }
                } else {
                    let inner = parse_module_expr(p);
                    p.expect(Token::Rparen);
                    // OCaml: parse_atomic_module_expr does NOT update the location to include parens.
                    // It just returns mod_expr as-is, keeping the inner expression's original location.
                    inner
                }
            }
        }
        Token::Percent => {
            // Module extension
            let ext = parse_extension(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_extension(Box::new(ext))),
                pmod_loc: loc,
                pmod_attributes: Attributes::new(),
            }
        }
        Token::At => {
            // Attributes on module expression - should be handled at parse_module_expr level
            // But we might get here for nested calls, so parse and attach
            let attrs = parse_attributes(p);
            let inner = parse_primary_module_expr(p);
            let mut combined_attrs = inner.pmod_attributes.clone();
            combined_attrs.extend(attrs);
            ModuleExpr {
                pmod_attributes: combined_attrs,
                ..inner
            }
        }
        _ => {
            // Try to parse as unpack: unpack(expr : pkg_type)
            if matches!(&p.token, Token::Lident(s) if s == "unpack") {
                p.next();
                p.expect(Token::Lparen);
                let expr = expr::parse_expr(p);
                let final_expr = if p.token == Token::Colon {
                    // OCaml captures colon position for package type location start
                    let colon_pos_idx = p.start_pos_idx();
                    p.next();
                    // Parse module type and convert to Ptyp_package
                    let mod_type = parse_module_type(p);
                    // Create Ptyp_package from module type
                    // OCaml uses colon_start for the package type location start
                    let pkg_loc = p.mk_loc_idx_to_end_of(colon_pos_idx, mod_type.pmty_loc);
                    let pkg_type = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_package(Box::new(
                            module_type_to_package(p, &mod_type),
                        ))),
                        ptyp_loc: pkg_loc,
                        ptyp_attributes: Attributes::new(),
                    };
                    let pkg_type_idx = p.arena_mut().push_core_type(pkg_type);
                    // OCaml: expect Rparen first, then create constraint with loc including Rparen
                    p.expect(Token::Rparen);
                    let constraint_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let expr_idx = p.arena_mut().push_expr(expr);
                    Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                            expr_idx,
                            pkg_type_idx,
                        )))),
                        pexp_loc: constraint_loc,
                        pexp_attributes: Attributes::new(),
                    }
                } else {
                    p.expect(Token::Rparen);
                    expr
                };
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let final_expr_idx = p.arena_mut().push_expr(final_expr);
                ModuleExpr {
                    pmod_desc: Box::new(ModuleExprDesc::Pmod_unpack(final_expr_idx)),
                    pmod_loc: loc,
                    pmod_attributes: Attributes::new(),
                }
            } else {
                p.err_unexpected();
                recover::default_module_expr()
            }
        }
    }
}

/// Parse module application.
fn parse_module_apply(p: &mut Parser<'_>, func: ModuleExpr) -> ModuleExpr {
    let mut result = func;

    // Module application only happens on the same line
    // A ( on a new line should not be treated as module application
    while p.token == Token::Lparen && p.prev_end_pos.line >= p.start_pos.line {
        // OCaml: let start_pos = p.Parser.start_pos in
        // Capture lparen position before consuming it
        let lparen_pos_idx = p.start_pos_idx();
        p.next();

        let args = if p.token == Token::Rparen {
            // Empty argument: F()
            p.next();
            // OCaml: let loc = mk_loc start_pos p.prev_end_pos in
            // For empty args, loc spans from lparen to after rparen
            let loc = p.mk_loc_idx_to_prev_end(lparen_pos_idx);
            vec![ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(vec![]))),
                pmod_loc: loc,
                pmod_attributes: Attributes::new(),
            }]
        } else {
            let mut args = vec![];
            loop {
                args.push(parse_module_expr(p));
                if p.token == Token::Comma {
                    p.next();
                    // Trailing comma.
                    if p.token == Token::Rparen {
                        break;
                    }
                    continue;
                }
                break;
            }
            p.expect(Token::Rparen);
            args
        };

        // OCaml: List.fold_left (fun mod_expr arg ->
        //   Ast_helper.Mod.apply
        //     ~loc:(mk_loc mod_expr.pmod_loc.loc_start arg.pmod_loc.loc_end)
        //     mod_expr arg)
        //   mod_expr args
        // Each nested apply gets loc from current result start to current arg end
        for arg in args {
            // Reuse the existing PosIdx from result.pmod_loc to match OCaml's sharing
            let start_idx = p.loc_start_idx(result.pmod_loc);
            let end_idx = p.loc_end_idx(arg.pmod_loc);
            let loc = p.mk_loc_idx_full(start_idx, end_idx);
            let result_idx = p.arena_mut().push_mod_expr(result);
            let arg_idx = p.arena_mut().push_mod_expr(arg);
            result = ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_apply(result_idx, arg_idx)),
                pmod_loc: loc,
                pmod_attributes: Attributes::new(),
            };
        }
    }

    result
}

// ============================================================================
// Functor Parsing
// ============================================================================

/// A functor argument parsed from source.
#[derive(Debug, Clone)]
struct FunctorArg {
    attrs: Attributes,
    name: Loc<StrIdx>,
    mod_type: Option<ModuleType>,
    start_pos_idx: PosIdx,
}

/// Parse a single functor argument.
/// functor-arg ::= Uident : modtype | _ : modtype | modtype (punning for _ : modtype)
fn parse_functor_arg(p: &mut Parser<'_>) -> Option<FunctorArg> {
    let start_pos_idx = p.start_pos_idx();
    let attrs = parse_attributes(p);

    match &p.token {
        Token::Uident(ident) => {
            let ident = ident.clone();
            let ident_end_pos_idx = p.end_pos_idx();
            p.next();

            match &p.token {
                Token::Colon => {
                    // Named parameter: Uident : modtype
                    p.next();
                    let mod_type = parse_module_type(p);
                    let loc = p.mk_loc_idx(start_pos_idx, ident_end_pos_idx);
                    let str_idx = p.arena_mut().push_interned_string(&ident);
                    Some(FunctorArg {
                        attrs,
                        name: with_loc(str_idx, loc),
                        mod_type: Some(mod_type),
                        start_pos_idx,
                    })
                }
                Token::Dot => {
                    // Module path as type: Foo.Bar (punning for _ : Foo.Bar)
                    // Continue parsing the module path
                    let ident_str_idx = p.arena_mut().push_interned_string(&ident);
                    let mut lid = Longident::Lident(ident_str_idx);
                    while p.token == Token::Dot {
                        p.next();
                        match &p.token {
                            Token::Uident(name) => {
                                let name_clone = name.clone();
                                let name_str_idx = p.arena_mut().push_interned_string(&name_clone);
                                lid = Longident::Ldot(Box::new(lid), name_str_idx);
                                p.next();
                            }
                            _ => break,
                        }
                    }
                    let lid_idx = p.push_longident(lid);
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let mod_type = ModuleType {
                        pmty_desc: Box::new(ModuleTypeDesc::Pmty_ident(with_loc(
                            lid_idx,
                            loc.clone(),
                        ))),
                        pmty_loc: loc,
                        pmty_attributes: Attributes::new(),
                    };
                    Some(FunctorArg {
                        attrs,
                        name: mknoloc(p.arena_mut().intern("_")),
                        mod_type: Some(mod_type),
                        start_pos_idx,
                    })
                }
                _ => {
                    // Just Uident (punning for _ : Uident)
                    let loc = p.mk_loc_idx(start_pos_idx, ident_end_pos_idx);
                    let lid_idx = p.push_lident(&*ident);
                    let mod_ident = with_loc(lid_idx, loc.clone());
                    let mod_type = ModuleType {
                        pmty_desc: Box::new(ModuleTypeDesc::Pmty_ident(mod_ident)),
                        pmty_loc: loc,
                        pmty_attributes: Attributes::new(),
                    };
                    Some(FunctorArg {
                        attrs,
                        name: mknoloc(p.arena_mut().intern("_")),
                        mod_type: Some(mod_type),
                        start_pos_idx,
                    })
                }
            }
        }
        Token::Underscore => {
            // Anonymous parameter: _ : modtype
            p.next();
            let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            p.expect(Token::Colon);
            let mod_type = parse_module_type(p);
            let underscore_idx = p.arena_mut().intern("_");
            Some(FunctorArg {
                attrs,
                name: with_loc(underscore_idx, name_loc),
                mod_type: Some(mod_type),
                start_pos_idx,
            })
        }
        Token::Lparen => {
            // Unit parameter: ()
            p.next();
            p.expect(Token::Rparen);
            let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let star_idx = p.arena_mut().intern("*");
            Some(FunctorArg {
                attrs,
                name: with_loc(star_idx, name_loc),
                mod_type: None,
                start_pos_idx,
            })
        }
        Token::Lbrace => {
            // Anonymous module signature: { ... } (punning for _ : { ... })
            let mod_type = parse_module_type(p);
            Some(FunctorArg {
                attrs,
                name: mknoloc(p.arena_mut().intern("_")),
                mod_type: Some(mod_type),
                start_pos_idx,
            })
        }
        _ => None,
    }
}

/// Parse functor arguments: ( arg1, arg2, ... )
fn parse_functor_args(p: &mut Parser<'_>) -> Vec<FunctorArg> {
    // Capture position before ( - OCaml includes ( in the first arg's location
    let paren_start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lparen);

    let mut args = vec![];
    let mut is_first = true;
    while p.token != Token::Rparen && p.token != Token::Eof {
        if let Some(mut arg) = parse_functor_arg(p) {
            // For the first argument, OCaml includes the opening ( in the functor location
            if is_first {
                arg.start_pos_idx = paren_start_pos_idx;
                is_first = false;
            }
            args.push(arg);
        } else {
            break;
        }

        // Handle comma
        if p.token == Token::Comma {
            p.next();
        } else {
            break;
        }
    }

    p.expect(Token::Rparen);

    // If no args were parsed, treat as unit functor: ()
    if args.is_empty() {
        let star_idx = p.arena_mut().intern("*");
        vec![FunctorArg {
            attrs: Attributes::new(),
            name: with_loc(star_idx, p.mk_loc_idx_to_prev_end(paren_start_pos_idx)),
            mod_type: None,
            start_pos_idx: paren_start_pos_idx,
        }]
    } else {
        args
    }
}

/// Parse a functor module expression: (args) => body
fn parse_functor_module_expr(p: &mut Parser<'_>) -> ModuleExpr {
    let args = parse_functor_args(p);

    // Optional return type constraint: (args) : RetType => body
    // Use parse_module_type_no_arrow to avoid interpreting `Set => A` as a functor type
    let return_type = if p.token == Token::Colon {
        p.next();
        Some(parse_module_type_no_arrow(p))
    } else {
        None
    };

    p.expect(Token::EqualGreater);

    // Parse the body
    let rhs_module_expr = parse_module_expr(p);

    // Apply return type constraint if present
    // Pmod_constraint(expr, type) represents "expr : type"
    // OCaml creates a backwards location from mod_expr start to mod_type end,
    // which acts as a ghost location since the body comes after the type constraint
    let rhs_module_expr = match return_type {
        Some(mod_type) => {
            // Reuse the existing PosIdx from rhs_module_expr.pmod_loc to match OCaml's sharing
            let start_idx = p.loc_start_idx(rhs_module_expr.pmod_loc);
            let end_idx = p.loc_end_idx(mod_type.pmty_loc);
            let loc = p.mk_loc_idx_full(start_idx, end_idx);
            let expr_idx = p.arena_mut().push_mod_expr(rhs_module_expr);
            let mod_type_idx = p.arena_mut().push_mod_type(mod_type);
            ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_constraint(expr_idx, mod_type_idx)),
                pmod_loc: loc,
                pmod_attributes: Attributes::new(),
            }
        }
        None => rhs_module_expr,
    };

    let end_pos_idx = p.prev_end_pos_idx();

    // Fold arguments into nested functors (right to left)
    args.into_iter().rev().fold(rhs_module_expr, |acc, arg| {
        let loc = p.mk_loc_idx(arg.start_pos_idx, end_pos_idx);
        let acc_idx = p.arena_mut().push_mod_expr(acc);
        let mod_type_idx = arg.mod_type.map(|mt| p.arena_mut().push_mod_type(mt));
        ModuleExpr {
            pmod_desc: Box::new(ModuleExprDesc::Pmod_functor(Box::new((
                arg.name,
                mod_type_idx,
                acc_idx,
            )))),
            pmod_loc: loc,
            pmod_attributes: arg.attrs,
        }
    })
}

/// Parse structure items within braces.
fn parse_structure_in_braces(p: &mut Parser<'_>) -> Vec<StructureItem> {
    parse_structure_delimited(p, Token::Rbrace)
}

/// OCaml `parse_delimited_region ~grammar:Grammar.Structure ~closing
/// ~f:(parse_structure_item_region pending_structure_items)`
/// (compiler/syntax/src/res_core.ml:1158-1175, 6645-6651). Each region owns its
/// pending items, so they are drained here rather than leaking outward.
fn parse_structure_delimited(p: &mut Parser<'_>, closing: Token<'static>) -> Vec<StructureItem> {
    use super::core::recover::should_abort_list_parse;

    let outer_pending = std::mem::take(&mut p.pending_structure_items);
    p.leave_breadcrumb(Grammar::Structure);
    let mut items = vec![];

    loop {
        if let Some(item) = p.pending_structure_items.pop() {
            items.push(item);
            continue;
        }
        if p.token == closing || p.token == Token::Eof {
            break;
        }
        if let Some(item) = parse_structure_item(p) {
            items.push(item);
        } else if p.token == closing || p.token == Token::Eof || should_abort_list_parse(p) {
            break;
        } else {
            p.err_unexpected();
            p.next();
        }
    }

    p.eat_breadcrumb();
    p.pending_structure_items = outer_pending;
    items
}

// ============================================================================
// Module Type Parsing
// ============================================================================

/// Parse a module type.
pub fn parse_module_type(p: &mut Parser<'_>) -> ModuleType {
    parse_module_type_impl(p, true, true)
}

/// Parse a module type without allowing ES6 arrow functor types.
/// Used when parsing return type constraints in functor expressions.
pub fn parse_module_type_no_arrow(p: &mut Parser<'_>) -> ModuleType {
    parse_module_type_impl(p, false, true)
}

/// Parse a module type without `with` constraint support.
/// Used for functor body types where `with` should apply to the outer functor.
fn parse_module_type_no_with(p: &mut Parser<'_>) -> ModuleType {
    parse_module_type_impl(p, true, false)
}

fn parse_module_type_impl(p: &mut Parser<'_>, es6_arrow: bool, parse_with: bool) -> ModuleType {
    // Parse attributes (e.g. `@attr module type of M`)
    let attrs = parse_attributes(p);

    // Capture start position AFTER attributes - OCaml's module type locations
    // don't include leading attributes
    let _start_pos = p.start_pos.clone();
    let start_pos_idx = p.start_pos_idx();

    // Parse functor types first (if allowed), then fall back to primary module types.
    let typ = if es6_arrow {
        parse_functor_module_type(p)
    } else {
        parse_primary_module_type(p)
    };

    // OCaml attaches attributes to the inner module type BEFORE parsing `with` constraints.
    // This means `@attr Foo with type t = int` becomes `Pmty_with(Box::new((Foo[@attr], constraints)))`,
    // not `Pmty_with(Box::new((Foo, constraints)))[@attr]`.
    let mut typ = typ;
    if !attrs.is_empty() {
        typ.pmty_attributes.extend(attrs);
    }

    // Handle with constraint: S with type t = ...
    // Only if parse_with is true - functor bodies don't parse `with` so it applies to the outer functor
    if parse_with && matches!(&p.token, Token::Lident(s) if s == "with") {
        p.next();
        let constraints = parse_with_constraints(p);
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let typ_idx = p.arena_mut().push_mod_type(typ);
        ModuleType {
            pmty_desc: Box::new(ModuleTypeDesc::Pmty_with(Box::new((typ_idx, constraints)))),
            pmty_loc: loc,
            pmty_attributes: Attributes::new(),
        }
    } else {
        typ
    }
}

fn parse_functor_module_type(p: &mut Parser<'_>) -> ModuleType {
    // Parenthesized functor params: `() => MT` or `(_ : S, X: T) => MT`
    if p.token == Token::Lparen && is_paren_functor_module_type(p) {
        return parse_paren_functor_module_type(p);
    }

    // Sugar: `S => MT` (unnamed parameter)
    let start_pos_idx = p.start_pos_idx();
    let param_type = parse_primary_module_type(p);
    if p.token == Token::EqualGreater {
        p.next();
        // Use parse_module_type_no_with so `with` constraints apply to the outer functor
        let body = parse_module_type_no_with(p);
        let loc = p.mk_loc_idx_to_end_of(start_pos_idx, body.pmty_loc);
        let param_type_idx = p.arena_mut().push_mod_type(param_type);
        let body_idx = p.arena_mut().push_mod_type(body);
        return ModuleType {
            pmty_desc: Box::new(ModuleTypeDesc::Pmty_functor(Box::new((
                mknoloc(p.arena_mut().intern("_")),
                Some(param_type_idx),
                body_idx,
            )))),
            pmty_loc: loc,
            pmty_attributes: Attributes::new(),
        };
    }

    param_type
}

fn is_paren_functor_module_type(p: &mut Parser<'_>) -> bool {
    p.lookahead(|state| {
        let mut depth = 0;
        while state.token != Token::Eof {
            match state.token {
                Token::Lparen => depth += 1,
                Token::Rparen => {
                    depth -= 1;
                    if depth == 0 {
                        state.next();
                        break;
                    }
                }
                _ => {}
            }
            state.next();
        }

        state.token == Token::EqualGreater
    })
}

fn parse_paren_functor_module_type(p: &mut Parser<'_>) -> ModuleType {
    let functor_start_idx = p.start_pos_idx();
    p.expect(Token::Lparen);

    #[derive(Debug)]
    struct FunctorParam {
        name: StringLoc,
        param: Option<ModuleType>,
        attrs: Attributes,
        start_pos_idx: PosIdx,
    }

    let mut params = vec![];

    if p.token == Token::Rparen {
        // Unit parameter: `() => MT` - OCaml uses "*" as the name for generative functors
        let start_pos_idx = functor_start_idx;
        p.next();
        // OCaml creates a location spanning the `()` for the `*` param name
        let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let star_idx = p.arena_mut().intern("*");
        params.push(FunctorParam {
            name: with_loc(star_idx, name_loc),
            param: None,
            attrs: Attributes::new(),
            start_pos_idx,
        });
    } else {
        while p.token != Token::Rparen && p.token != Token::Eof {
            let start_pos_idx = p.start_pos_idx();
            // Parse parameter attributes like `@attr _: S` - attach to the functor type, not param
            let param_attrs = parse_attributes(p);

            match &p.token {
                Token::Underscore => {
                    p.next();
                    // OCaml's arg_name location spans from start_pos (before attrs) to end of `_`
                    let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let underscore_idx = p.arena_mut().intern("_");
                    let name = with_loc(underscore_idx, name_loc);
                    let param = if p.token == Token::Colon {
                        p.next();
                        Some(parse_module_type(p))
                    } else {
                        None
                    };
                    params.push(FunctorParam {
                        name,
                        param,
                        attrs: param_attrs,
                        start_pos_idx,
                    });
                }
                Token::Lident(_) | Token::Uident(_) => {
                    // `X: S` (named) or `S` (shorthand parameter type)
                    let is_named = p.lookahead(|state| {
                        state.next();
                        state.token == Token::Colon
                    });

                    if is_named {
                        let name = match &p.token {
                            Token::Lident(n) | Token::Uident(n) => {
                                let n = n.clone();
                                let loc = p.mk_loc_current();
                                p.next();
                                let str_idx = p.arena_mut().push_interned_string(&n);
                                with_loc(str_idx, loc)
                            }
                            _ => mknoloc(p.arena_mut().intern("_")),
                        };
                        p.expect(Token::Colon);
                        let mty = parse_module_type(p);
                        params.push(FunctorParam {
                            name,
                            param: Some(mty),
                            attrs: param_attrs,
                            start_pos_idx,
                        });
                    } else {
                        // Shorthand: `(S, T) => U` (unnamed parameter types).
                        // Match OCaml parse_functor_arg's Uident/no-colon path:
                        // build Pmty_ident directly so longident.loc and pmty_loc
                        // are the same location record.
                        let lid = parse_module_long_ident(p);
                        let loc = lid.loc;
                        let param_ty = ModuleType {
                            pmty_desc: Box::new(ModuleTypeDesc::Pmty_ident(lid)),
                            pmty_loc: loc,
                            pmty_attributes: Attributes::new(),
                        };
                        params.push(FunctorParam {
                            name: mknoloc(p.arena_mut().intern("_")),
                            param: Some(param_ty),
                            attrs: param_attrs,
                            start_pos_idx,
                        });
                    }
                }
                Token::Lparen => {
                    // Allow `()` as a unit parameter in multi-arg functors, and `(S)` as shorthand.
                    let is_unit = p.lookahead(|state| {
                        state.next();
                        state.token == Token::Rparen
                    });
                    if is_unit {
                        p.next();
                        p.expect(Token::Rparen);
                        // OCaml creates a location spanning the `()` for the `*` param name
                        let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                        let star_idx = p.arena_mut().intern("*");
                        params.push(FunctorParam {
                            name: with_loc(star_idx, name_loc),
                            param: None,
                            attrs: param_attrs,
                            start_pos_idx,
                        });
                    } else {
                        let param_ty = parse_module_type(p);
                        params.push(FunctorParam {
                            name: mknoloc(p.arena_mut().intern("_")),
                            param: Some(param_ty),
                            attrs: param_attrs,
                            start_pos_idx,
                        });
                    }
                }
                _ => {
                    break;
                }
            }

            if !p.optional(&Token::Comma) {
                break;
            }
        }
        p.expect(Token::Rparen);
    }

    p.expect(Token::EqualGreater);
    // Use parse_module_type_no_with so `with` constraints apply to the outer functor
    let body = parse_module_type_no_with(p);
    let end_pos_idx = p.loc_end_idx(body.pmty_loc);

    // OCaml includes the opening `(` in the outermost Pmty_functor location
    // For inner functors (in multi-param), use the param's start position
    // After enumerate().rev(), idx==0 is the first param in original order
    params
        .into_iter()
        .enumerate()
        .rev()
        .fold(body, |acc, (idx, param)| {
            // First param in original order (idx==0) uses functor_start (opening paren)
            let start_idx = if idx == 0 {
                functor_start_idx
            } else {
                param.start_pos_idx
            };
            let loc = p.mk_loc_idx(start_idx, end_pos_idx);
            let acc_idx = p.arena_mut().push_mod_type(acc);
            let param_idx = param.param.map(|mt| p.arena_mut().push_mod_type(mt));
            ModuleType {
                pmty_desc: Box::new(ModuleTypeDesc::Pmty_functor(Box::new((
                    param.name, param_idx, acc_idx,
                )))),
                pmty_loc: loc,
                pmty_attributes: param.attrs,
            }
        })
}

/// Parse a primary module type.
fn parse_primary_module_type(p: &mut Parser<'_>) -> ModuleType {
    let start_pos_idx = p.start_pos_idx();

    match &p.token {
        Token::Uident(_) | Token::Lident(_) => {
            // Module type path
            let lid = parse_module_type_long_ident(p);
            ModuleType {
                pmty_desc: Box::new(ModuleTypeDesc::Pmty_ident(lid)),
                pmty_loc: p.mk_loc_idx_to_prev_end(start_pos_idx),
                pmty_attributes: Attributes::new(),
            }
        }
        Token::Lbrace => {
            // Signature: { ... }
            p.next();
            let items = parse_signature_in_braces(p);
            p.expect(Token::Rbrace);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            ModuleType {
                pmty_desc: Box::new(ModuleTypeDesc::Pmty_signature(Box::new(items))),
                pmty_loc: loc,
                pmty_attributes: Attributes::new(),
            }
        }
        Token::Lparen => {
            p.next();
            let inner = parse_module_type(p);
            p.expect(Token::Rparen);
            // OCaml updates the location to include the parentheses
            ModuleType {
                pmty_loc: p.mk_loc_idx_to_prev_end(start_pos_idx),
                ..inner
            }
        }
        Token::Module => {
            // module type of M
            p.next();
            p.expect(Token::Typ);
            p.expect(Token::Of);
            let mod_expr = parse_module_expr(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let mod_expr_idx = p.arena_mut().push_mod_expr(mod_expr);
            ModuleType {
                pmty_desc: Box::new(ModuleTypeDesc::Pmty_typeof(mod_expr_idx)),
                pmty_loc: loc,
                pmty_attributes: Attributes::new(),
            }
        }
        Token::Percent => {
            // Module type extension
            let ext = parse_extension(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            ModuleType {
                pmty_desc: Box::new(ModuleTypeDesc::Pmty_extension(Box::new(ext))),
                pmty_loc: loc,
                pmty_attributes: Attributes::new(),
            }
        }
        _ => {
            p.err_unexpected();
            recover::default_module_type()
        }
    }
}

/// Parse signature items within braces.
///
/// Like parse_signature, this matches OCaml's parse_region behavior.
/// When a signature item cannot be parsed, we emit an error and advance.
///
/// Note: Uses Grammar::Signature (not Specification) because Signature terminates on Rbrace.
fn parse_signature_in_braces(p: &mut Parser<'_>) -> Vec<SignatureItem> {
    use super::core::recover::should_abort_list_parse;
    use super::grammar::Grammar;

    // OCaml: Parser.leave_breadcrumb p Grammar.Signature (not Specification!)
    // Grammar.Signature terminates on Rbrace, while Specification doesn't.
    p.leave_breadcrumb(Grammar::Signature);

    let mut items = vec![];

    loop {
        // Skip semicolons
        while p.token == Token::Semicolon {
            p.next();
        }

        match parse_signature_item(p) {
            Some(item) => items.push(item),
            None => {
                // OCaml's parse_region: when f returns None, check if we should abort
                if p.token == Token::Eof || should_abort_list_parse(p) {
                    break;
                }
                // Emit unexpected token error and advance to avoid infinite loop
                p.err_unexpected();
                p.next();
            }
        }
    }

    // OCaml: Parser.eat_breadcrumb p
    p.eat_breadcrumb();

    items
}

/// Parse with constraints.
fn parse_with_constraints(p: &mut Parser<'_>) -> Vec<WithConstraint> {
    let mut constraints = vec![];

    loop {
        if let Some(c) = parse_with_constraint(p) {
            constraints.push(c);
        }

        if p.token == Token::And {
            p.next();
        } else {
            break;
        }
    }

    constraints
}

/// Parse type constraints following a type declaration or `with type` constraint.
fn parse_type_constraints(p: &mut Parser<'_>) -> Vec<(CoreTypeIdx, CoreTypeIdx, Location)> {
    let mut cstrs = vec![];
    while p.token == Token::Constraint {
        // OCaml compiler/syntax/src/res_core.ml:5838-5866 includes the
        // `constraint` keyword in both the type variable location and the
        // tuple location.
        let cstr_start_idx = p.start_pos_idx();
        p.next();
        p.expect(Token::SingleQuote);
        let var = match &p.token {
            Token::Lident(name) | Token::Uident(name) => {
                let name = extend_cow_lifetime(name.clone());
                let var_end_idx = p.end_pos_idx();
                p.next();
                CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(name))),
                    ptyp_loc: p.mk_loc_idx(cstr_start_idx, var_end_idx),
                    ptyp_attributes: Attributes::new(),
                }
            }
            _ => {
                p.err(DiagnosticCategory::Message(
                    "Expected type variable in constraint".to_string(),
                ));
                break;
            }
        };
        p.expect(Token::Equal);
        let typ = typ::parse_typ_expr(p);
        let var_idx = p.arena_mut().push_core_type(var);
        let typ_idx = p.arena_mut().push_core_type(typ);
        cstrs.push((var_idx, typ_idx, p.mk_loc_idx_to_prev_end(cstr_start_idx)));
    }
    cstrs
}

/// Parse a single with constraint.
fn parse_with_constraint(p: &mut Parser<'_>) -> Option<WithConstraint> {
    match &p.token {
        Token::Typ => {
            p.next();
            let lid = parse_type_long_ident(p);
            // Use the StrIdx directly from the longident to enable sharing
            let type_name_idx = p.arena().get_longident(lid.txt).last_idx();
            let type_loc = lid.loc.clone();

            // OCaml `parse_type_params ~parent:type_constr` (res_core.ml:7239).
            let parent: Vec<String> = p
                .arena()
                .get_longident(lid.txt)
                .flatten_idx()
                .into_iter()
                .map(|part| p.arena().get_string(part).to_string())
                .collect();
            let params = parse_type_params(p, &parent);

            // Check for destructive substitution (:=) vs regular type equation (=)
            let is_substitution = p.token == Token::ColonEqual;
            if is_substitution {
                p.next();
            } else {
                p.expect(Token::Equal);
            }
            // Check for private keyword: type t = private string
            let private = if p.token == Token::Private {
                p.next();
                PrivateFlag::Private
            } else {
                PrivateFlag::Public
            };
            let typ = typ::parse_typ_expr(p);
            let type_constraints = if is_substitution {
                // OCaml compiler/syntax/src/res_core.ml:7285-7294 returns the
                // Pwith_typesubst branch immediately after parse_typ_expr. It
                // only parses parse_type_constraints for the `=` branch at
                // compiler/syntax/src/res_core.ml:7295-7306.
                vec![]
            } else {
                parse_type_constraints(p)
            };

            let typ_idx = p.arena_mut().push_core_type(typ);
            let decl = TypeDeclaration {
                // OCaml uses the full longident location for the type name location
                ptype_name: with_loc(type_name_idx, type_loc.clone()),
                ptype_params: params,
                ptype_cstrs: type_constraints,
                ptype_kind: TypeKind::Ptype_abstract,
                ptype_private: private,
                ptype_manifest: Some(typ_idx),
                ptype_attributes: Attributes::new(),
                ptype_loc: type_loc,
            };

            if is_substitution {
                Some(WithConstraint::Pwith_typesubst(lid, decl))
            } else {
                Some(WithConstraint::Pwith_type(lid, decl))
            }
        }
        Token::Module => {
            p.next();
            let lid = parse_module_long_ident(p);
            // Check for destructive substitution (:=) vs regular module equation (=)
            let is_substitution = p.token == Token::ColonEqual;
            if is_substitution {
                p.next();
            } else {
                p.expect(Token::Equal);
            }
            let lid2 = parse_module_long_ident(p);
            if is_substitution {
                Some(WithConstraint::Pwith_modsubst(lid, lid2))
            } else {
                Some(WithConstraint::Pwith_module(lid, lid2))
            }
        }
        _ => None,
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Check if a token can start an expression.
fn is_expr_start(token: &Token<'_>) -> bool {
    matches!(
        token,
        Token::True
            | Token::False
            | Token::Int { .. }
            | Token::Float { .. }
            | Token::String(_)
            | Token::Codepoint { .. }
            | Token::Lident(_)
            | Token::Uident(_)
            | Token::Lparen
            | Token::Lbracket
            | Token::Lbrace
            | Token::If
            | Token::Switch
            | Token::While
            | Token::For
            | Token::Try
            | Token::LessThan
            | Token::Minus
            | Token::Plus
            | Token::Bang
            | Token::Await
            | Token::Assert
            | Token::List
            | Token::Dict
            | Token::Hash
            | Token::Backtick
            | Token::Percent
            | Token::Forwardslash
            | Token::ForwardslashDot
            | Token::Underscore
    )
}

/// Parse a module long identifier.
/// Handles both module paths (Foo.Bar.Baz) and module type paths (Foo.Bar.t).
/// Module type names are typically lowercase (e.g., RGLEvents.t).
fn parse_module_long_ident(p: &mut Parser<'_>) -> Loc<LidentIdx> {
    parse_module_long_ident_with_lowercase(p, false)
}

fn parse_module_type_long_ident(p: &mut Parser<'_>) -> Loc<LidentIdx> {
    parse_module_long_ident_with_lowercase(p, true)
}

fn parse_module_long_ident_with_lowercase(p: &mut Parser<'_>, lowercase: bool) -> Loc<LidentIdx> {
    let start_pos_idx = p.start_pos_idx();
    let mut path_parts = vec![];

    loop {
        match &p.token {
            Token::Uident(name) => {
                path_parts.push(name.to_string());
                p.next();
                if p.token == Token::Dot {
                    p.next();
                    continue;
                }
                break;
            }
            Token::Lident(name) if lowercase => {
                path_parts.push(name.to_string());
                p.next();
                break;
            }
            _ => {
                p.err(DiagnosticCategory::Uident(p.token.clone().into_owned()));
                if !path_parts.is_empty() {
                    path_parts.push("_".to_string());
                }
                break;
            }
        }
    }

    if path_parts.is_empty() {
        path_parts.push("_".to_string());
    }

    let lid_idx = super::core::build_longident_idx(p, &path_parts);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    with_loc(lid_idx, loc)
}

/// Replicate OCaml's parse_value_path behavior for Uident type names.
///
/// OCaml's parse_value_path has a quirk when the name starts with Uident:
/// - Its internal `aux` function always calls `Parser.next` (consuming current token)
/// - After aux returns, `Parser.next_unsafe` always consumes one additional token
///
/// This means for `type T1 = D1`: aux consumes `T1`, next_unsafe consumes `=`,
/// so the type equation parser never sees `=` → abstract type, and `D1` becomes
/// a standalone expression.
///
/// Returns (path_parts, name_start_pos, name_end_pos).
pub(super) fn parse_value_path_for_type(p: &mut Parser<'_>) -> (Vec<String>, Position, Position) {
    let name_start = p.start_pos.clone();

    // Recursive aux function that mirrors OCaml's aux in parse_value_path
    fn aux(p: &mut Parser<'_>, path_parts: &mut Vec<String>) {
        // Save current token info BEFORE advancing (like OCaml)
        let saved_token = p.token.clone();
        let saved_start = p.start_pos.clone();
        let saved_end = p.end_pos.clone();

        // Push the current name
        if let Token::Uident(name) | Token::Lident(name) = &saved_token {
            path_parts.push(name.to_string());
        }

        // Always advance (OCaml: Parser.next p)
        p.next();

        if p.token == Token::Dot {
            // Consume the dot
            p.expect(Token::Dot);

            match &p.token {
                Token::Lident(name) => {
                    // Terminal: lowercase ident ends the path
                    path_parts.push(name.to_string());
                    // Don't consume - let it be consumed by next_unsafe below
                }
                Token::Uident(_) => {
                    // Recurse for more path segments
                    aux(p, path_parts);
                    return;
                }
                _ => {
                    // Error: unexpected token after dot
                    p.err_unexpected();
                    path_parts.push("_".to_string());
                }
            }
        } else {
            // Not a dot - emit lident error (OCaml: Diagnostics.lident token)
            // The error points at the saved token's position
            p.err_at(
                saved_start,
                saved_end,
                DiagnosticCategory::Lident(saved_token.into_owned()),
            );
            // Return path as-is (OCaml returns `path`)
            return;
        }
    }

    let mut path_parts = Vec::new();
    aux(p, &mut path_parts);

    // OCaml: Parser.next_unsafe p - consume one more token
    let name_end = p.prev_end_pos.clone();
    p.next_unsafe();

    (path_parts, name_start, name_end)
}

/// Parse a type long identifier.
fn parse_type_long_ident(p: &mut Parser<'_>) -> Loc<LidentIdx> {
    let start_pos_idx = p.start_pos_idx();
    let mut path_parts = vec![];

    match &p.token {
        Token::Lident(name) => {
            path_parts.push(name.to_string());
            p.next();
        }
        Token::Uident(_) => loop {
            match &p.token {
                Token::Uident(name) => {
                    let name = name.to_string();
                    let start = p.start_pos.clone();
                    let end = p.end_pos.clone();
                    path_parts.push(name.clone());
                    p.next();
                    if p.token == Token::Dot {
                        p.next();
                    } else {
                        p.err_at(
                            start,
                            end,
                            DiagnosticCategory::Lident(Token::Uident(name.into())),
                        );
                        break;
                    }
                }
                Token::Lident(name) => {
                    path_parts.push(name.to_string());
                    p.next();
                    break;
                }
                _ => {
                    p.err_unexpected();
                    path_parts.push("_".to_string());
                    break;
                }
            }
        },
        _ => {
            p.err_unexpected();
            path_parts.push("_".to_string());
        }
    }

    let lid_idx = super::core::build_longident_idx(p, &path_parts);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    with_loc(lid_idx, loc)
}

/// OCaml `parse_let_bindings` (compiler/syntax/src/res_core.ml:2790-2824), after
/// the `let`/`rec` tokens: the first binding, then one binding per `and`. The
/// attributes before each `and` are read by `parse_attributes_and_binding` in the
/// enclosing region, so a failed lookahead there silences that region.
pub(super) fn parse_let_bindings(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
    let_end_pos_idx: PosIdx,
    _rec_flag: RecFlag,
    outer_attrs: Attributes,
    unwrap: bool,
) -> (Vec<ValueBinding>, Option<LocIdx>) {
    let attrs = add_let_unwrap_attr(p, unwrap, start_pos_idx, let_end_pos_idx, outer_attrs);
    let first = parse_let_binding_body(p, start_pos_idx, attrs);
    let first_binding_loc = first.pvb_loc;
    let mut bindings = vec![first];
    loop {
        let binding_start_idx = p.start_pos_idx();
        let binding_end_idx = p.end_pos_idx();
        let attrs = parse_attributes_and_binding(p);
        let attrs = add_let_unwrap_attr(p, unwrap, binding_start_idx, binding_end_idx, attrs);
        if p.token != Token::And {
            break;
        }
        p.next();
        // Over-parse `and let` for fault tolerance.
        p.optional(&Token::Let { unwrap: false });
        bindings.push(parse_let_binding_body(p, binding_start_idx, attrs));
    }

    // Return bindings and optionally the LocIdx for sharing with structure_item.
    // Only share when there's exactly one binding - for multiple bindings, the structure_item
    // should span all bindings which is different from the first binding's location.
    if bindings.len() == 1 {
        (bindings, Some(first_binding_loc))
    } else {
        (bindings, None)
    }
}

/// OCaml `add_unwrap_attr` in `parse_let_bindings`: `let?` prepends
/// `@let.unwrap` located at `start_pos..end_pos`.
fn add_let_unwrap_attr(
    p: &mut Parser<'_>,
    unwrap: bool,
    start_idx: PosIdx,
    end_idx: PosIdx,
    attrs: Attributes,
) -> Attributes {
    if !unwrap {
        return attrs;
    }
    let loc = p.mk_loc_idx(start_idx, end_idx);
    let name = p.arena_mut().intern("let.unwrap");
    let unwrap_attr: Attribute = (with_loc(name, loc), Payload::PStr(Box::new(vec![])));
    Attributes::from_vec(vec![unwrap_attr]).concat(attrs)
}

/// OCaml `parse_let_binding_body` (compiler/syntax/src/res_core.ml:2690-2731).
fn parse_let_binding_body(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
    attrs: Attributes,
) -> ValueBinding {
    p.begin_region();
    p.leave_breadcrumb(Grammar::LetBinding);
    // OCaml sets Pattern breadcrumb before parsing the pattern
    p.leave_breadcrumb(Grammar::Pattern);
    let pat = pattern::parse_pattern(p);
    p.eat_breadcrumb();

    // Parse an ordinary pattern constraint or the current-Parsetree
    // value constraint used by `let x: type a. t = expr`.
    let (pat, value_constraint) = if p.token == Token::Colon {
        p.next();
        if p.token == Token::Typ {
            p.next();
            let pvc_newtypes = expr::parse_lident_list(p);
            p.expect(Token::Dot);
            let pvc_type = typ::parse_typ_expr(p);
            let pvc_type = p.arena_mut().push_core_type(pvc_type);
            (
                pat,
                Some(crate::parser::ast::ValueConstraint {
                    pvc_newtypes,
                    pvc_type,
                    pvc_pattern: None,
                    pvc_expression: None,
                }),
            )
        } else {
            let poly_type = typ::parse_poly_type_expr(p);
            let loc = p.mk_loc_spanning(pat.ppat_loc, poly_type.ptyp_loc);
            let pat_idx = p.arena_mut().push_pat(pat);
            let typ_idx = p.arena_mut().push_core_type(poly_type);
            (
                Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
                        pat_idx, typ_idx,
                    )))),
                    ppat_loc: loc,
                    ppat_attributes: Attributes::new(),
                },
                None,
            )
        }
    } else {
        (pat, None)
    };

    p.expect(Token::Equal);
    let mut expr = expr::parse_expr(p);
    // The locally abstract branch follows `parse_expr` directly; ordinary
    // bindings retain the parser's constrained/arrow over-parse.
    if value_constraint.is_none() {
        expr = expr::over_parse_constrained_or_coerced_or_arrow_expression(p, expr);
    }

    let vb_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    let pat_idx = p.arena_mut().push_pat(pat);
    let expr_idx = p.arena_mut().push_expr(expr);
    if let Some(value_constraint) = value_constraint
        && let Err(loc) =
            p.arena_mut()
                .set_value_constraint(pat_idx, value_constraint, expr_idx, vb_loc)
    {
        p.err_at(
            p.loc_start(loc),
            p.loc_end(loc),
            DiagnosticCategory::FatalSyntaxerr,
        );
    }
    let binding = ValueBinding {
        pvb_pat: pat_idx,
        pvb_expr: expr_idx,
        pvb_attributes: attrs,
        pvb_loc: vb_loc,
    };
    p.eat_breadcrumb();
    p.end_region();
    binding
}



/// The part of a type declaration after its name and parameters: OCaml
/// `parse_type_equation_and_representation` plus `parse_type_constraints`
/// (compiler/syntax/src/res_core.ml:6402-6421, 6459-6470). Only the first
/// declaration of a `type` item gets an inline-types context; `and`
/// declarations are parsed without one.
fn parse_type_declaration_body(
    p: &mut Parser<'_>,
    attrs: Attributes,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    decl_start_idx: crate::parse_arena::PosIdx,
    name: Located<String>,
    params: Vec<(CoreTypeIdx, Variance)>,
) -> Option<TypeDeclaration> {
    // Store params and outer name location in context for inline type declarations
    if let Some(inline_ctx) = inline_ctx {
        let mut ctx = inline_ctx.borrow_mut();
        ctx.params = params.clone();
        ctx.outer_name_loc = name.loc.clone();
    }

    // Convert name from Located<String> to Located<StrIdx> for ptype_name
    let name_str_idx = p.arena_mut().push_interned_string(&name.txt);
    let name: Located<StrIdx> = with_loc(name_str_idx, name.loc);

    // The type name path for inline record desugaring (using StrIdx)
    let current_type_name_path: Vec<StrIdx> = vec![name.txt];

    // Parse optional manifest and/or kind (and ReScript's `type t = T = ...` equation form).
    // OCaml: if token is Bar, call expect Equal to generate "Did you forget a `=` here?" error
    let (manifest, kind, private) = if p.token == Token::Equal || p.token == Token::Bar {
        if p.token == Token::Bar {
            // Generate error about missing `=` before variant constructors
            p.expect(Token::Equal);
        }
        // Heuristic: `{...}` after `=` can be a record type *or* a bs-object/object type.
        // Disambiguate by looking at the first significant token inside the braces.
        let looks_like_object_type_after_lbrace = |p: &mut Parser<'_>| -> bool {
            p.lookahead(|state| {
                // Current token is `{`
                state.next();

                // Skip leading attributes: @attr ...
                while state.token == Token::At {
                    state.next();
                    // Skip attribute id segments (possibly dotted)
                    if matches!(state.token, Token::Lident(_) | Token::Uident(_))
                        || state.token.is_keyword()
                    {
                        state.next();
                        while state.token == Token::Dot {
                            state.next();
                            if matches!(state.token, Token::Lident(_) | Token::Uident(_))
                                || state.token.is_keyword()
                            {
                                state.next();
                            } else {
                                break;
                            }
                        }
                    }
                    // Skip optional payload in parentheses
                    if state.token == Token::Lparen {
                        let mut depth = 1;
                        state.next();
                        while depth > 0 && state.token != Token::Eof {
                            match state.token {
                                Token::Lparen => depth += 1,
                                Token::Rparen => depth -= 1,
                                _ => {}
                            }
                            state.next();
                        }
                    }
                }

                // It's an object type if we see a string field name (like {"x": int})
                // Spread (...) alone doesn't make it an object - records can have spread too
                if matches!(state.token, Token::String(_)) {
                    return true;
                }

                // If we see spread, look for a string field anywhere after it
                // If all fields are spreads or idents, it's a record
                if state.token == Token::DotDotDot {
                    // Scan through the rest to see if there's any string field
                    let mut depth = 0;
                    loop {
                        match state.token {
                            Token::String(_) if depth == 0 => return true, // Found a string field - it's an object
                            Token::Rbrace if depth == 0 => return false, // End of braces, no string found - it's a record
                            Token::Eof => return false,
                            Token::Lparen | Token::Lbrace | Token::Lbracket => depth += 1,
                            Token::Rparen | Token::Rbracket => {
                                if depth > 0 {
                                    depth -= 1;
                                }
                            }
                            Token::Rbrace => {
                                if depth > 0 {
                                    depth -= 1;
                                } else {
                                    return false;
                                }
                            }
                            _ => {}
                        }
                        state.next();
                    }
                }

                // Dot or DotDot at start also indicates object type
                matches!(state.token, Token::Dot | Token::DotDot)
            })
        };

        // Better variant-vs-manifest disambiguation: a leading Uident without a following `.`
        // is a constructor in a variant type.
        // OCaml parser logic: if Uident is followed by `.`, it's a type path (Module.Type),
        // otherwise it's a constructor declaration.
        let is_variant_type_starting_with_uident = |p: &mut Parser<'_>| -> bool {
            p.lookahead(|state| {
                state.next(); // consume Uident

                // `Foo.bar` is a type path, not a constructor.
                // Anything else means it's a constructor.
                state.token != Token::Dot
            })
        };

        p.next(); // consume first '='
        let mut private = if p.token == Token::Private {
            p.next();
            PrivateFlag::Private
        } else {
            PrivateFlag::Public
        };

        let mut manifest = None;
        let mut kind = TypeKind::Ptype_abstract;

        match &p.token {
            // OCaml `parse_private_eq_or_repr` (compiler/syntax/src/res_core.ml): after
            // `private`, a token that starts a type expression (including `@`) is a
            // manifest, not an attributed variant.
            Token::At if private == PrivateFlag::Private => {
                let typ = typ::parse_typ_expr(p);
                manifest = Some(p.arena_mut().push_core_type(typ));
            }
            Token::Bar => {
                // Variant type starting with | (e.g., type t = | A | B)
                kind = parse_type_kind(p, None, None);
            }
            Token::Lbrace => {
                // Record type OR object type ({"x": int})
                if looks_like_object_type_after_lbrace(p) {
                    let typ = typ::parse_object_decl(p);
                    manifest = Some(p.arena_mut().push_core_type(typ));
                } else {
                    kind = parse_type_kind(p, inline_ctx, inline_ctx.map(|_| &current_type_name_path));
                }
            }
            Token::Uident(_) => {
                if is_variant_type_starting_with_uident(p) {
                    let constructors = parse_constructors_without_leading_bar(p);
                    kind = TypeKind::Ptype_variant(constructors);
                } else {
                    let typ = typ::parse_typ_expr(p);
                    manifest = Some(p.arena_mut().push_core_type(typ));
                }
            }
            Token::At | Token::DocComment { .. } => {
                // Check if this is a variant constructor with attribute: @attr Constr
                // vs a manifest type with attribute: @attr Type.t
                // vs an open type with attribute: @attr ..
                // vs a record type with attribute: @attr {x: int}
                // Lookahead to see if there's a Uident after the attribute that's NOT followed by `.`
                let what_follows = p.lookahead(|state| {
                    // Skip attributes and doc comments
                    while matches!(state.token, Token::At | Token::DocComment { .. }) {
                        if matches!(state.token, Token::DocComment { .. }) {
                            state.next();
                        } else {
                            state.next(); // @
                            // Skip attribute name (may be dotted like res.doc)
                            while matches!(state.token, Token::Lident(_) | Token::Uident(_))
                                || state.token.is_keyword()
                            {
                                state.next();
                                if state.token == Token::Dot {
                                    state.next();
                                } else {
                                    break;
                                }
                            }
                            if state.token == Token::Lparen {
                                let mut depth = 1;
                                state.next();
                                while depth > 0 && state.token != Token::Eof {
                                    if state.token == Token::Lparen {
                                        depth += 1;
                                    } else if state.token == Token::Rparen {
                                        depth -= 1;
                                    }
                                    state.next();
                                }
                            }
                        }
                    }
                    // Check what comes after attributes
                    if state.token == Token::Bar {
                        "variant"
                    } else if state.token == Token::DotDot {
                        "open"
                    } else if state.token == Token::Lbrace {
                        "record_or_object"
                    } else if matches!(state.token, Token::Uident(_)) {
                        state.next();
                        if state.token != Token::Dot {
                            "variant"
                        } else {
                            "manifest"
                        }
                    } else {
                        "manifest"
                    }
                });
                match what_follows {
                    "variant" => {
                        kind = TypeKind::Ptype_variant(parse_constructors(p));
                    }
                    "open" => {
                        // Parse attributes and then ..
                        let _attrs = parse_attributes(p);
                        if p.token == Token::DotDot {
                            p.next();
                            kind = TypeKind::Ptype_open;
                        }
                    }
                    "record_or_object" => {
                        // Parse attributes then check if record or object
                        let attrs = parse_attributes(p);
                        if p.token == Token::Lbrace {
                            if looks_like_object_type_after_lbrace(p) {
                                let mut typ = typ::parse_typ_expr(p);
                                typ.ptyp_attributes = attrs;
                                manifest = Some(p.arena_mut().push_core_type(typ));
                            } else {
                                kind = parse_type_kind(
                                    p,
                                    inline_ctx,
                                    inline_ctx.map(|_| &current_type_name_path),
                                );
                            }
                        }
                    }
                    _ => {
                        let typ = typ::parse_typ_expr(p);
                        manifest = Some(p.arena_mut().push_core_type(typ));
                    }
                }
            }
            Token::DotDot => {
                // Extensible variant: type t = ..
                p.next();
                kind = TypeKind::Ptype_open;
            }
            _ => {
                // Manifest type
                let typ = typ::parse_typ_expr(p);
                manifest = Some(p.arena_mut().push_core_type(typ));
            }
        }

        // ReScript type equation: `type t = T = ...`
        if manifest.is_some() && p.token == Token::Equal {
            p.next(); // consume second '='
            private = if p.token == Token::Private {
                p.next();
                PrivateFlag::Private
            } else {
                PrivateFlag::Public
            };

            kind = match &p.token {
                Token::Bar => parse_type_kind(p, None, None),
                Token::Lbrace => {
                    parse_type_kind(p, inline_ctx, inline_ctx.map(|_| &current_type_name_path))
                }
                Token::Uident(_) => {
                    TypeKind::Ptype_variant(parse_constructors_without_leading_bar(p))
                }
                Token::DotDot => {
                    p.next();
                    TypeKind::Ptype_open
                }
                _ => {
                    p.err(DiagnosticCategory::Message(
                        "Expected variant or record type after '='".to_string(),
                    ));
                    TypeKind::Ptype_abstract
                }
            };
        }

        (manifest, kind, private)
    } else {
        (None, TypeKind::Ptype_abstract, PrivateFlag::Public)
    };

    let cstrs = parse_type_constraints(p);

    // In type declarations with qualified type constructors (Ldot),
    // OCaml creates a NEW location with the same positions as the longident.
    // IMPORTANT: We must create a fresh LocIdx, NOT reuse lid.loc, because OCaml
    // creates fresh Location objects (though positions inside may be shared).
    // For unqualified (Lident), the CoreType uses full extent.
    let manifest = manifest.map(|t| fix_type_manifest_location(p, t));

    // Use decl_start_idx for the start position to enable sharing with structure_item
    let loc = p.mk_loc_idx_to_prev_end(decl_start_idx);
    Some(TypeDeclaration {
        ptype_name: name,
        ptype_params: params,
        ptype_cstrs: cstrs,
        ptype_kind: kind,
        ptype_private: private,
        ptype_manifest: manifest,
        ptype_attributes: attrs,
        ptype_loc: loc,
    })
}

/// Fix the location of a Ptyp_constr in a type manifest context.
/// For qualified identifiers (Ldot), OCaml creates a NEW location with the same
/// position values as the longident (but a separate Location object).
/// IMPORTANT: We must NOT reuse lid.loc (same LocIdx) because that would cause
/// sharing during marshal - OCaml writes a fresh Location block with shared
/// positions INSIDE, but the Location itself is not shared.
/// For unqualified (Lident), it uses full extent.
/// EXCEPTION: When the type has attributes, OCaml keeps the full extent including
/// type arguments (this allows the location to cover the entire attributed type).
fn fix_type_manifest_location(p: &mut Parser<'_>, typ_idx: CoreTypeIdx) -> CoreTypeIdx {
    let typ = p.arena().get_core_type(typ_idx).clone();
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, _) = **inner;
            // Only adjust for qualified identifiers (Ldot) WITHOUT attributes
            // When there are attributes, OCaml keeps the full extent including type args
            if p.arena().is_ldot(lid.txt) && typ.ptyp_attributes.is_empty() {
                // Create a NEW LocIdx with the same positions as lid.loc
                // This matches OCaml's behavior: fresh Location object, shared positions
                let lid_loc = p.arena().get_location(lid.loc).clone();
                let new_loc =
                    p.arena_mut()
                        .push_loc(lid_loc.loc_start, lid_loc.loc_end, lid_loc.loc_ghost);
                let fixed = CoreType {
                    ptyp_loc: new_loc,
                    ..typ
                };
                p.arena_mut().push_core_type(fixed)
            } else {
                typ_idx
            }
        }
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (ref arg, ret_idx, arity) = **inner;
            let args = p.arena().nary_arrow_args(arg, arity).into_owned();
            // Also adjust Ldot types in every arrow parameter position, but not
            // in the return type: OCaml keeps type arguments in return locations.
            let fixed_args = args
                .into_iter()
                .map(|arg| TypeArg {
                    typ: fix_type_manifest_location(p, arg.typ),
                    ..arg
                })
                .collect::<Vec<_>>();
            let first = fixed_args[0].clone();
            if fixed_args.len() > 1 {
                p.arena_mut().set_nary_arrow_args(arity, fixed_args.clone());
            }
            let fixed = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
                    Box::new(first),
                    ret_idx,
                    arity,
                )))),
                ..typ
            };
            p.arena_mut().push_core_type(fixed)
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (ref alias_ct_idx, ref alias_name) = **inner;
            // Recurse into the aliased type (e.g., `Color.t<...> as 'rgb`)
            let fixed_inner_idx = fix_type_manifest_location(p, *alias_ct_idx);
            let fixed = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_alias(Box::new((
                    fixed_inner_idx,
                    alias_name.clone(),
                )))),
                ..typ
            };
            p.arena_mut().push_core_type(fixed)
        }
        _ => typ_idx,
    }
}


/// OCaml `parse_type_param` (compiler/syntax/src/res_core.ml).
fn parse_type_param(p: &mut Parser<'_>) -> Option<(CoreTypeIdx, Variance)> {
    const TYPE_PARAM: &str =
        "A type param consists of a singlequote followed by a name like `'a` or `'A`";
    let variance = match p.token {
        Token::Plus => {
            p.next();
            Variance::Covariant
        }
        Token::Minus => {
            p.next();
            Variance::Contravariant
        }
        _ => Variance::Invariant,
    };
    let (desc, loc) = match &p.token {
        Token::SingleQuote => {
            p.next();
            let start_pos_idx = p.start_pos_idx();
            let (ident, loc) = if p.token == Token::Eof {
                p.err_unexpected();
                (String::new(), p.mk_loc_idx_to_prev_end(start_pos_idx))
            } else {
                super::core::parse_ident(p, TYPE_PARAM, start_pos_idx)
            };
            (CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(ident))), loc)
        }
        Token::Underscore => {
            let loc = p.mk_loc_current();
            p.next();
            (CoreTypeDesc::Ptyp_any, loc)
        }
        Token::Uident(name) | Token::Lident(name) => {
            let name = name.to_string();
            p.err(DiagnosticCategory::Message(format!(
                "Type params start with a singlequote: '{name}"
            )));
            let start_pos_idx = p.start_pos_idx();
            let (ident, loc) = super::core::parse_ident(p, TYPE_PARAM, start_pos_idx);
            (CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(ident))), loc)
        }
        _ => return None,
    };
    let typ = CoreType {
        ptyp_desc: Box::new(desc),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    };
    Some((p.arena_mut().push_core_type(typ), variance))
}


/// Format a type with angle bracket syntax for error suggestions.
fn format_type_with_angle_brackets(
    p: &Parser<'_>,
    name: &str,
    params: &[(CoreTypeIdx, Variance)],
) -> String {
    if params.is_empty() {
        name.to_string()
    } else {
        let param_strs: Vec<String> = params
            .iter()
            .map(|(t, variance)| {
                // `Res_printer.print_type_params`: variance, then the type.
                let variance = match variance {
                    Variance::Covariant => "+",
                    Variance::Contravariant => "-",
                    Variance::Invariant => "",
                };
                match &*p.arena().get_core_type(*t).ptyp_desc {
                    CoreTypeDesc::Ptyp_var(v) => format!("{variance}'{v}"),
                    _ => format!("{variance}_"),
                }
            })
            .collect();
        format!("{}<{}>", name, param_strs.join(", "))
    }
}

/// Parse type kind (variant or record).
fn parse_type_kind(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: Option<&Vec<StrIdx>>,
) -> TypeKind {
    match &p.token {
        Token::Bar => {
            // Variant type
            let constructors = parse_constructors(p);
            TypeKind::Ptype_variant(constructors)
        }
        Token::Lbrace => {
            // Record type - capture { position for first field's location (OCaml extends first spread field's loc to {)
            let lbrace_pos_idx = p.start_pos_idx();
            p.next();
            // OCaml parse_record_or_object_decl parses leading attrs once and, when present,
            // attaches them to the first field while forcing first-field loc_start to the
            // first attribute's loc_start.
            let leading_attrs = parse_attributes(p);
            // OCaml `parse_record_or_object_decl` (res_core.ml:6041).
            p.leave_breadcrumb(grammar::Grammar::RecordDecl);
            let labels = if leading_attrs.is_empty() {
                parse_label_declarations(
                    p,
                    inline_ctx,
                    current_type_name_path,
                    Some(lbrace_pos_idx),
                )
            } else {
                parse_label_declarations_with_leading_attrs(
                    p,
                    inline_ctx,
                    current_type_name_path,
                    leading_attrs,
                )
            };
            p.expect(Token::Rbrace);
            p.eat_breadcrumb();
            TypeKind::Ptype_record(labels)
        }
        _ => TypeKind::Ptype_abstract,
    }
}

/// Parse variant constructors (starting with |).
fn parse_constructors(p: &mut Parser<'_>) -> Vec<ConstructorDeclaration> {
    // OCaml parse_type_constructor_declarations:
    // - First constructor: optional leading doc comment + optional leading `|`
    // - Remaining constructors: only if token is `|` or doc-comment-then-`|`
    let mut constructors = vec![];

    // First constructor: optional leading doc comment attribute.
    let first_doc_attrs = if let Token::DocComment { loc, content } = &p.token {
        let loc = loc.clone();
        let content = content.clone();
        p.next();
        let loc = p.from_location(&loc);
        vec![super::core::doc_comment_to_attribute(
            p.arena_mut(),
            loc,
            content,
        )]
    } else {
        vec![]
    };

    // First constructor (optional leading bar).
    let first_start_idx = p.start_pos_idx();
    p.optional(&Token::Bar);
    if let Some(mut c) = parse_constructor_with_start(p, first_start_idx) {
        if !first_doc_attrs.is_empty() {
            let mut attrs = Attributes::from_vec(first_doc_attrs);
            attrs.extend(c.pcd_attributes.into_vec());
            c.pcd_attributes = attrs;
        }
        constructors.push(c);
    }

    // Remaining constructors must be introduced by `|` (or doc comment followed by `|`).
    loop {
        if !is_bar_or_doc_comment_then_bar(p) {
            break;
        }

        let doc_attrs = if let Token::DocComment { loc, content } = &p.token {
            let loc = loc.clone();
            let content = content.clone();
            p.next();
            let loc = p.from_location(&loc);
            vec![super::core::doc_comment_to_attribute(
                p.arena_mut(),
                loc,
                content,
            )]
        } else {
            vec![]
        };

        let bar_start_idx = p.start_pos_idx();
        p.next(); // consume `|`

        if let Some(mut c) = parse_constructor_with_start(p, bar_start_idx) {
            if !doc_attrs.is_empty() {
                let mut attrs = Attributes::from_vec(doc_attrs);
                attrs.extend(c.pcd_attributes.into_vec());
                c.pcd_attributes = attrs;
            }
            constructors.push(c);
        }
    }

    constructors
}

/// Check if current token is `|` or doc-comment followed by `|`.
/// Matches OCaml's `is_bar_or_doc_comment_then_bar`.
fn is_bar_or_doc_comment_then_bar(p: &mut Parser<'_>) -> bool {
    match p.token {
        Token::Bar => true,
        Token::DocComment { .. } => p.lookahead(|state| {
            state.next();
            matches!(state.token, Token::Bar)
        }),
        _ => false,
    }
}

/// Parse variant constructors where the first doesn't have a leading |.
fn parse_constructors_without_leading_bar(p: &mut Parser<'_>) -> Vec<ConstructorDeclaration> {
    let mut constructors = vec![];

    // Parse the first constructor (no leading |)
    if let Some(c) = parse_constructor(p) {
        constructors.push(c);
    }

    // Parse remaining constructors (with leading |)
    while p.token == Token::Bar {
        // Capture start position BEFORE consuming the bar (like OCaml)
        let bar_start_idx = p.start_pos_idx();
        p.next();
        if let Some(c) = parse_constructor_with_start(p, bar_start_idx) {
            constructors.push(c);
        }
    }

    constructors
}

/// Parse a single constructor with optional explicit start position.
fn parse_constructor_with_start(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
) -> Option<ConstructorDeclaration> {
    parse_constructor_impl(p, start_pos_idx)
}

/// Parse a single constructor.
fn parse_constructor(p: &mut Parser<'_>) -> Option<ConstructorDeclaration> {
    let start_pos_idx = p.start_pos_idx();
    parse_constructor_impl(p, start_pos_idx)
}

/// Implementation of constructor parsing with a given start position.
fn parse_constructor_impl(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
) -> Option<ConstructorDeclaration> {
    let attrs = parse_attributes(p);

    // Check for spread syntax: ...typeName
    if p.token == Token::DotDotDot {
        p.next();
        // OCaml uses start_pos (which may include |) for name location as well
        let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let spread_type = typ::parse_typ_expr(p);
        let spread_type_idx = p.arena_mut().push_core_type(spread_type);
        // Declaration location includes type
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let ellipsis_idx = p.arena_mut().intern("...");
        return Some(ConstructorDeclaration {
            pcd_name: with_loc(ellipsis_idx, name_loc),
            pcd_args: ConstructorArguments::Pcstr_tuple(vec![spread_type_idx]),
            pcd_res: None,
            pcd_loc: loc,
            pcd_attributes: attrs,
        });
    }

    let name = match &p.token {
        Token::Uident(n) => {
            let n = n.clone();
            let loc = p.mk_loc_current();
            p.next();
            let n_idx = p.arena_mut().push_interned_string(&n);
            with_loc(n_idx, loc)
        }
        _ => {
            p.err(DiagnosticCategory::Uident(p.token.clone().into_owned()));
            let error_idx = p.arena_mut().intern("_");
            return Some(ConstructorDeclaration {
                pcd_name: mknoloc(error_idx),
                pcd_args: ConstructorArguments::Pcstr_tuple(vec![]),
                pcd_res: None,
                pcd_loc: p.none_loc(),
                pcd_attributes: Attributes::new(),
            });
        }
    };

    // Parse constructor arguments
    let args = if p.token == Token::Lparen {
        p.next();
        // Check for inline record: Foo({...}) with braces inside parens
        // But NOT object types which use string keys or . markers
        let is_inline_record = p.token == Token::Lbrace
            && p.lookahead(|state| {
                state.next(); // consume {
                // Skip any leading attributes
                while state.token == Token::At {
                    state.next();
                    // Skip attribute id and any payload
                    if matches!(
                        state.token,
                        Token::Lident(_) | Token::Uident(_) | Token::Module
                    ) {
                        state.next();
                    }
                    // Skip attribute payload if present
                    if state.token == Token::Lparen {
                        let mut depth = 1;
                        state.next();
                        while depth > 0 && state.token != Token::Eof {
                            match state.token {
                                Token::Lparen => depth += 1,
                                Token::Rparen => depth -= 1,
                                _ => {}
                            }
                            state.next();
                        }
                    }
                }
                // If we see string, ".", or ".." it's an object type, not inline record
                // Note: {} (empty) is an inline record, NOT an object type
                // DotDotDot (spread) could be either - scan past it looking for string fields
                if matches!(state.token, Token::String(_) | Token::Dot | Token::DotDot) {
                    return false; // Object type, not inline record
                }
                if state.token == Token::DotDotDot {
                    // Scan past spread to check if subsequent fields have string keys
                    // If all fields are identifiers, it's an inline record
                    let mut depth = 0;
                    loop {
                        match state.token {
                            Token::String(_) if depth == 0 => return false, // String field = object type
                            Token::Rbrace if depth == 0 => return true, // End without string = record
                            Token::Eof => return true,
                            Token::Lparen | Token::Lbrace | Token::Lbracket => depth += 1,
                            Token::Rparen | Token::Rbracket => {
                                if depth > 0 {
                                    depth -= 1;
                                }
                            }
                            Token::Rbrace => {
                                if depth > 0 {
                                    depth -= 1;
                                } else {
                                    return true;
                                }
                            }
                            _ => {}
                        }
                        state.next();
                    }
                }
                true // Not object type → inline record
            });
        if is_inline_record {
            let lbrace_pos_idx = p.start_pos_idx();
            p.next(); // consume {
            let labels = parse_constructor_record_labels(p, Some(lbrace_pos_idx));
            p.expect(Token::Rbrace);
            // Allow trailing comma after inline record: Foo({...},)
            p.optional(&Token::Comma);
            p.expect(Token::Rparen);
            ConstructorArguments::Pcstr_record(labels)
        } else {
            // OCaml `parse_constr_decl_args` (compiler/syntax/src/res_core.ml:5369-5520):
            // a leading object type is parsed first (its location starts after `{`),
            // followed by an optional comma; the remaining arguments use
            // `parse_comma_delimited_region ~grammar:TypExprList ~closing:Rparen`.
            let mut args = vec![];
            if p.token == Token::Lbrace {
                let is_object = p.lookahead(|state| {
                    state.next(); // consume {
                    // Skip any leading attributes
                    while state.token == Token::At {
                        state.next();
                        if matches!(
                            state.token,
                            Token::Lident(_) | Token::Uident(_) | Token::Module
                        ) {
                            state.next();
                        }
                        if state.token == Token::Lparen {
                            let mut depth = 1;
                            state.next();
                            while depth > 0 && state.token != Token::Eof {
                                match state.token {
                                    Token::Lparen => depth += 1,
                                    Token::Rparen => depth -= 1,
                                    _ => {}
                                }
                                state.next();
                            }
                        }
                    }
                    // String, ".", or ".." indicate object type (NOT empty record)
                    // DotDotDot (spread) needs further scanning to check for string fields
                    if matches!(state.token, Token::String(_) | Token::Dot | Token::DotDot) {
                        return true;
                    }
                    if state.token == Token::DotDotDot {
                        // Scan past spread to check for string fields
                        let mut depth = 0;
                        loop {
                            match state.token {
                                Token::String(_) if depth == 0 => return true,
                                Token::Rbrace if depth == 0 => return false,
                                Token::Eof => return false,
                                Token::Lparen | Token::Lbrace | Token::Lbracket => depth += 1,
                                Token::Rparen | Token::Rbracket => {
                                    if depth > 0 {
                                        depth -= 1;
                                    }
                                }
                                Token::Rbrace => {
                                    if depth > 0 {
                                        depth -= 1;
                                    } else {
                                        return false;
                                    }
                                }
                                _ => {}
                            }
                            state.next();
                        }
                    }
                    false
                });
                if is_object {
                    p.next();
                    let start_pos_idx = p.start_pos_idx();
                    let obj = typ::parse_object_type_body(p, start_pos_idx);
                    let obj_idx = p.arena_mut().push_core_type(obj);
                    args.push(obj_idx);
                    p.optional(&Token::Comma);
                }
            }
            let rest = super::core::parse_comma_delimited_region(
                p,
                Grammar::TypExprList,
                Token::Rparen,
                |p| {
                    if super::grammar::is_typ_expr_start(&p.token) {
                        let arg = typ::parse_typ_expr(p);
                        Some(p.arena_mut().push_core_type(arg))
                    } else {
                        None
                    }
                },
            );
            args.extend(rest);
            p.expect(Token::Rparen);
            ConstructorArguments::Pcstr_tuple(args)
        }
    } else if p.token == Token::Lbrace {
        let lbrace_pos_idx = p.start_pos_idx();
        p.next();
        let labels = parse_constructor_record_labels(p, Some(lbrace_pos_idx));
        p.expect(Token::Rbrace);
        ConstructorArguments::Pcstr_record(labels)
    } else {
        ConstructorArguments::Pcstr_tuple(vec![])
    };

    // Optional GADT result type: Constructor: type
    let res = if p.token == Token::Colon {
        p.next();
        let res_typ = typ::parse_typ_expr(p);
        Some(p.arena_mut().push_core_type(res_typ))
    } else {
        None
    };

    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    Some(ConstructorDeclaration {
        pcd_name: name,
        pcd_args: args,
        pcd_res: res,
        pcd_loc: loc,
        pcd_attributes: attrs,
    })
}

/// Parse record label declarations.
/// Handles both regular fields and spread syntax (...typ).
/// `lbrace_pos` is the position of the opening `{` - OCaml extends the first spread field's
/// location back to this position.
fn parse_label_declarations(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: Option<&Vec<StrIdx>>,
    lbrace_pos_idx: Option<PosIdx>,
) -> Vec<LabelDeclaration> {
    parse_label_declarations_with_first_state(
        p,
        inline_ctx,
        current_type_name_path,
        lbrace_pos_idx,
        true,
    )
}

fn parse_label_declarations_with_first_state(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: Option<&Vec<StrIdx>>,
    lbrace_pos_idx: Option<PosIdx>,
    mut is_first: bool,
) -> Vec<LabelDeclaration> {
    p.leave_breadcrumb(grammar::Grammar::FieldDeclarations);
    let mut labels = vec![];

    while p.token != Token::Rbrace && p.token != Token::Eof {
        // Handle spread: ...typ - represented as a label with name "..."
        if p.token == Token::DotDotDot {
            let start_pos_idx = p.start_pos_idx();
            p.next();
            // Name location is just the "..." part
            let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let spread_type = typ::parse_typ_expr(p);
            // OCaml extends the first spread field's location back to the { position
            let loc_start_idx = if is_first {
                lbrace_pos_idx.unwrap_or(start_pos_idx)
            } else {
                start_pos_idx
            };
            // OCaml has different end position handling for first vs non-first spread fields:
            // - First spread field: location extends to p.end_pos (includes comma/brace)
            // - Non-first spread fields: location uses typ.ptyp_loc.loc_end
            let loc = if is_first {
                p.mk_loc_idx_to_end(loc_start_idx)
            } else {
                p.mk_loc_idx_to_end_of(loc_start_idx, spread_type.ptyp_loc)
            };
            let spread_type_idx = p.arena_mut().push_core_type(spread_type);
            let ellipsis_idx = p.arena_mut().intern("...");
            labels.push(LabelDeclaration {
                pld_name: with_loc(ellipsis_idx, name_loc),
                pld_mutable: MutableFlag::Immutable,
                pld_type: spread_type_idx,
                pld_loc: loc,
                pld_attributes: Attributes::new(),
                pld_optional: false,
            });
            is_first = false;
            if !p.optional(&Token::Comma) {
                break;
            }
            continue;
        }

        match parse_label_declaration(p, inline_ctx, current_type_name_path, None, true) {
            Some(l) => labels.push(l),
            None => {
                // OCaml `parse_comma_delimited_region`'s `None` branch
                // (compiler/syntax/src/res_core.ml:1096-1102): stop on a
                // closing token or abort point, otherwise report the token,
                // skip it, and keep parsing the region.
                if p.token == Token::Eof
                    || p.token == Token::Rbrace
                    || super::core::recover::should_abort_list_parse(p)
                {
                    break;
                }
                p.err_unexpected();
                p.next();
                continue;
            }
        }
        is_first = false;
        if !p.optional(&Token::Comma) {
            let implicit_comma = matches!(p.token, Token::At | Token::DocComment { .. });
            if implicit_comma {
                continue;
            }
            if grammar::is_list_element(&grammar::Grammar::FieldDeclarations, &p.token) {
                // Missing comma but next token looks like another field declaration.
                // Emit "Did you forget a `,` here?" and continue parsing.
                p.expect(Token::Comma);
            } else if p.token != Token::Eof
                && p.token != Token::Rbrace
                && !super::core::recover::should_abort_list_parse(p)
            {
                p.expect(Token::Comma);
                if p.token == Token::Semicolon {
                    p.next();
                }
            } else {
                break;
            }
        }
    }

    p.eat_breadcrumb();
    labels
}

/// Parse record label declarations when attrs were parsed once before the first field.
///
/// Mirrors OCaml parse_record_or_object_decl's `attr :: _ as attrs` branch:
/// - attach pre-parsed attrs to the first field
/// - force first-field `pld_loc.loc_start` to first attr `loc_start`
/// - then parse the remaining fields normally
fn parse_label_declarations_with_leading_attrs(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: Option<&Vec<StrIdx>>,
    leading_attrs: Attributes,
) -> Vec<LabelDeclaration> {
    let mut labels = Vec::new();
    let first_attr_start_idx = leading_attrs
        .iter()
        .next()
        .map(|(name, _)| p.loc_start_idx(name.loc))
        .expect("leading attrs must be non-empty");

    let parsed_first = if let Some(first) = parse_first_label_with_preparsed_attrs(
        p,
        inline_ctx,
        current_type_name_path,
        leading_attrs,
        first_attr_start_idx,
    ) {
        labels.push(first);
        true
    } else {
        false
    };

    // OCaml uses `Parser.optional p Comma |> ignore` before parsing the rest.
    p.optional(&Token::Comma);
    labels.extend(parse_label_declarations_with_first_state(
        p,
        inline_ctx,
        current_type_name_path,
        None,
        !parsed_first,
    ));

    labels
}

/// Parse the first label declaration with already-parsed attrs and an overridden loc start.
///
/// Supports both regular fields and spread (`...typ`) fields.
fn parse_first_label_with_preparsed_attrs(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: Option<&Vec<StrIdx>>,
    attrs: Attributes,
    first_attr_start_idx: PosIdx,
) -> Option<LabelDeclaration> {
    if p.token == Token::DotDotDot {
        let spread_start_idx = p.start_pos_idx();
        p.next();
        let name_loc = p.mk_loc_idx_to_prev_end(spread_start_idx);
        let spread_type = typ::parse_typ_expr(p);
        let spread_type_end_idx = p.loc_end_idx(spread_type.ptyp_loc);
        let spread_type_idx = p.arena_mut().push_core_type(spread_type);
        let ellipsis_idx = p.arena_mut().intern("...");
        let loc = p.mk_loc_idx_full(first_attr_start_idx, spread_type_end_idx);
        return Some(LabelDeclaration {
            pld_name: with_loc(ellipsis_idx, name_loc),
            pld_mutable: MutableFlag::Immutable,
            pld_type: spread_type_idx,
            pld_loc: loc,
            pld_attributes: attrs,
            pld_optional: false,
        });
    }

    if let Some(mut first) =
        parse_label_declaration(p, inline_ctx, current_type_name_path, Some(attrs), false)
    {
        let first_loc = p.arena().get_location(first.pld_loc).clone();
        first.pld_loc =
            p.arena_mut()
                .push_loc(first_attr_start_idx, first_loc.loc_end, first_loc.loc_ghost);
        Some(first)
    } else {
        None
    }
}

/// Parse record labels in constructor inline records (`Pcstr_record`).
///
/// OCaml `parse_constr_decl_args` parses leading field attributes once at `{...}` entry.
/// When present, those attrs are attached to the first field but the first field location
/// starts at the field name token (not at the leading attrs).
fn parse_constructor_record_labels(
    p: &mut Parser<'_>,
    lbrace_pos_idx: Option<PosIdx>,
) -> Vec<LabelDeclaration> {
    let leading_attrs = parse_attributes(p);
    if leading_attrs.is_empty() {
        return parse_label_declarations(p, None, None, lbrace_pos_idx);
    }

    let mut labels = Vec::new();
    let parsed_first =
        if let Some(first) = parse_label_declaration(p, None, None, Some(leading_attrs), false) {
            labels.push(first);
            true
        } else {
            false
        };

    if p.token == Token::Rbrace || p.token == Token::Eof {
        return labels;
    }

    p.expect(Token::Comma);
    labels.extend(parse_label_declarations_with_first_state(
        p,
        None,
        None,
        None,
        !parsed_first,
    ));
    labels
}

/// Parse a single label declaration.
fn parse_label_declaration(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: Option<&Vec<StrIdx>>,
    preparsed_attrs: Option<Attributes>,
    include_preparsed_attrs_in_loc: bool,
) -> Option<LabelDeclaration> {
    // OCaml usually captures label declaration start before parsing field attrs.
    // Constructor records with pre-parsed leading attrs are the exception: first field
    // location starts at the field name token.
    let start_pos_before_attrs = p.start_pos.clone();
    let start_pos_before_attrs_idx = p.start_pos_idx();
    let attrs = match preparsed_attrs {
        Some(attrs) => attrs,
        None => parse_attributes(p),
    };
    let start_pos = if include_preparsed_attrs_in_loc {
        start_pos_before_attrs
    } else {
        p.start_pos.clone()
    };
    let start_pos_idx = if include_preparsed_attrs_in_loc {
        start_pos_before_attrs_idx
    } else {
        p.start_pos_idx()
    };

    let mutable = if p.token == Token::Mutable {
        p.next();
        MutableFlag::Mutable
    } else {
        MutableFlag::Immutable
    };

    let name = match &p.token {
        Token::Lident(n) => {
            let n = n.clone();
            let loc = p.mk_loc_current();
            p.next();
            let n_idx = p.arena_mut().push_interned_string(&n);
            with_loc(n_idx, loc)
        }
        _ if p.token.is_keyword() => {
            // OCaml: Token.is_keyword p.token
            // Check if the keyword is followed by a colon - if so, recover by renaming
            if let Some((recovered_name, loc)) =
                super::core::recover_keyword_field_name_if_probably_field(
                    p,
                    error_messages::keyword_field_in_type,
                )
            {
                let name_idx = p.arena_mut().push_string(recovered_name);
                with_loc(name_idx, loc)
            } else {
                // Just emit the error without recovery
                super::core::emit_keyword_field_error(p, error_messages::keyword_field_in_type);
                return None;
            }
        }
        _ => {
            // Match OCaml's error handling: give specific messages for dangling attrs/mutable
            // OCaml uses p.end_pos as the end position (not p.start_pos)
            if !attrs.is_empty() {
                p.err_at(start_pos.clone(), p.end_pos.clone(), DiagnosticCategory::Message(
                    "Attributes and doc comments can only be used at the beginning of a field declaration".to_string(),
                ));
            }
            if mutable == MutableFlag::Mutable {
                p.err_at(start_pos.clone(), p.end_pos.clone(), DiagnosticCategory::Message(
                    "The `mutable` qualifier can only be used at the beginning of a field declaration".to_string(),
                ));
            }
            // OCaml `parse_field_declaration_region` (res_core.ml) returns
            // `None` without a diagnostic here; the enclosing comma-delimited
            // region reports the unexpected token.
            return None;
        }
    };

    // Extend current type name path with this field name for nested inline records
    let extended_path = current_type_name_path.map(|path| {
        let mut new_path = path.clone();
        new_path.push(name.txt.clone());
        new_path
    });

    // Check for optional field marker
    let is_optional = p.optional(&Token::Question);

    // Check for colon, equal (error recovery), or field punning
    // OCaml: if Equal instead of Colon, emit specific error and continue
    let is_punning = match &p.token {
        Token::Colon => {
            p.next();
            false
        }
        Token::Equal => {
            // Common mistake: using = instead of : in record type declarations
            p.err(DiagnosticCategory::Message(
                "Record fields in type declarations use `:`. Example: `{field: string}`"
                    .to_string(),
            ));
            p.next();
            false
        }
        _ => {
            // Field punning: {form} is shorthand for {form: form}
            true
        }
    };

    // Check if the field type is an inline record
    let typ = if is_punning {
        // Field punning: {form} becomes {form: form}
        // The type is a simple type constructor with the field name
        let lid_idx = p.push_lident_from_idx(name.txt);
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                with_loc(lid_idx, name.loc.clone()),
                vec![],
            )))),
            ptyp_loc: name.loc.clone(),
            ptyp_attributes: Attributes::new(),
        }
    } else if p.token == Token::Lbrace && inline_ctx.is_some() && extended_path.is_some() {
        // Check if this looks like a record (starts with Lident, Mutable, At, or DotDotDot)
        let looks_like_record = p.lookahead(|state| {
            state.next(); // Skip {
            // Skip leading attributes
            while state.token == Token::At {
                state.next();
                // Skip attribute identifier
                if matches!(state.token, Token::Lident(_) | Token::Uident(_))
                    || state.token.is_keyword()
                {
                    state.next();
                    while state.token == Token::Dot {
                        state.next();
                        if matches!(state.token, Token::Lident(_) | Token::Uident(_))
                            || state.token.is_keyword()
                        {
                            state.next();
                        } else {
                            break;
                        }
                    }
                }
                // Skip optional payload
                if state.token == Token::Lparen {
                    let mut depth = 1;
                    state.next();
                    while depth > 0 && state.token != Token::Eof {
                        match state.token {
                            Token::Lparen => depth += 1,
                            Token::Rparen => depth -= 1,
                            _ => {}
                        }
                        state.next();
                    }
                }
            }
            // Check if first significant token indicates a record declaration
            matches!(
                state.token,
                Token::Lident(_) | Token::Mutable | Token::At | Token::DotDotDot
            )
        });

        if looks_like_record {
            // Parse as inline record and register it
            let type_start_pos_idx = p.start_pos_idx();
            p.next(); // consume {
            let inline_ctx = inline_ctx.unwrap();
            let extended_path = extended_path.as_ref().unwrap();
            let labels = parse_label_declarations(
                p,
                Some(inline_ctx),
                Some(extended_path),
                Some(type_start_pos_idx),
            );
            p.expect(Token::Rbrace);
            let type_loc = p.mk_loc_idx_to_prev_end(type_start_pos_idx);

            // Create the inline type name (e.g., "options.permissions.all")
            let inline_type_name: String = extended_path
                .iter()
                .map(|idx| p.arena().get_string(*idx))
                .collect::<Vec<_>>()
                .join(".");
            let inline_type_idx = p.arena_mut().push_string(inline_type_name.to_string());

            let params = inline_ctx.borrow().params.clone();
            // Register this inline type (insert at front for correct order)
            inline_ctx.borrow_mut().found_inline_types.insert(
                0,
                (
                    inline_type_idx,
                    type_loc.clone(),
                    TypeKind::Ptype_record(labels),
                    params.clone(),
                ),
            );

            // Return a Ptyp_constr pointing to the inline type
            let type_args: Vec<CoreTypeIdx> = params.into_iter().map(|(t, _)| t).collect();
            let lid_idx = p.push_lident_from_idx(inline_type_idx);
            CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                    with_loc(lid_idx, type_loc.clone()),
                    type_args,
                )))),
                ptyp_loc: type_loc,
                ptyp_attributes: Attributes::new(),
            }
        } else {
            // Not a record - parse as regular type (object type)
            // But still thread inline context through parser fields for nested extraction
            parse_poly_type_with_inline_context(p, inline_ctx, extended_path.as_ref())
        }
    } else {
        // Thread inline context through parser fields if available
        parse_poly_type_with_inline_context(p, inline_ctx, extended_path.as_ref())
    };

    // OCaml uses typ.ptyp_loc.loc_end for label declaration's end, not p.prev_end_pos
    let loc = p.mk_loc_idx_to_end_of(start_pos_idx, typ.ptyp_loc);
    let typ_idx = p.arena_mut().push_core_type(typ);
    Some(LabelDeclaration {
        pld_name: name,
        pld_mutable: mutable,
        pld_type: typ_idx,
        pld_loc: loc,
        pld_attributes: attrs,
        pld_optional: is_optional,
    })
}

/// Parse a poly type expression, threading inline context through parser fields
/// so that nested `{...}` in type constructor args can be extracted as inline records.
fn parse_poly_type_with_inline_context(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    extended_path: Option<&Vec<StrIdx>>,
) -> CoreType {
    if let (Some(ctx), Some(path)) = (inline_ctx, extended_path) {
        // Save old parser fields
        let old_path = p.current_type_name_path.take();
        let old_found = p.inline_types_found.take();
        let old_params = std::mem::take(&mut p.inline_types_params);

        // Set parser fields for inline record extraction
        // Convert StrIdx path to String path for parser state
        let string_path: Vec<String> = path
            .iter()
            .map(|idx| p.arena().get_string(*idx).to_string())
            .collect();
        p.current_type_name_path = Some(string_path);
        p.inline_types_found = Some(ctx.borrow().found_inline_types.clone());
        p.inline_types_params = ctx.borrow().params.clone();

        let typ = typ::parse_poly_type_expr(p);

        if let Some(found) = p.inline_types_found.take() {
            let mut ctx = ctx.borrow_mut();
            ctx.found_inline_types = found;
            ctx.params = p.inline_types_params.clone();
        }

        // Restore old parser fields
        p.current_type_name_path = old_path;
        p.inline_types_found = old_found;
        p.inline_types_params = old_params;

        typ
    } else {
        typ::parse_poly_type_expr(p)
    }
}

fn parse_external_value_description(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    loc_start_idx: PosIdx,
) -> (ValueDescription, Vec<TypeDeclaration>) {
    // OCaml `parse_external_def` (compiler/syntax/src/res_core.ml): attributes
    // only precede `external`; the name is a plain `parse_lident`.
    p.leave_breadcrumb(Grammar::External);
    let attrs = outer_attrs;
    let (name_text, name_loc) = super::core::parse_lident(p);
    let n_idx = p.arena_mut().push_interned_string(&name_text);
    let name = with_loc(n_idx, name_loc);

    p.expect_with_grammar(Token::Colon, Some(Grammar::TypeExpression));

    let was_in_external = p.in_external;
    let old_path = p.current_type_name_path.take();
    let old_found = p.inline_types_found.take();
    let old_params = std::mem::take(&mut p.inline_types_params);
    let old_collect = p.inline_types_collect_free_type_vars;

    // OCaml compiler/syntax/src/res_core.ml:6584-6624 parses externals with
    // InExternal enabled and an inline-types context rooted at the external name.
    p.in_external = true;
    p.current_type_name_path = Some(vec![name_text.clone()]);
    p.inline_types_found = Some(vec![]);
    p.inline_types_params = vec![];
    p.inline_types_collect_free_type_vars = true;

    let typ_ct = typ::parse_external_type_expr(p);
    let inline_types_found = p.inline_types_found.take().unwrap_or_default();

    p.in_external = was_in_external;
    p.current_type_name_path = old_path;
    p.inline_types_found = old_found;
    p.inline_types_params = old_params;
    p.inline_types_collect_free_type_vars = old_collect;

    let typ = p.arena_mut().push_core_type(typ_ct);

    // OCaml res_core.ml: `Parser.expect Equal` recovers when `=` is missing,
    // and the primitive string is read either way.
    let equal_start = p.start_pos.clone();
    let equal_end = p.end_pos.clone();
    p.expect(Token::Equal);
    let prim = match &p.token {
        Token::String(s) => {
            let s = s.clone();
            p.next();
            vec![p.arena_mut().push_interned_string(&s)]
        }
        _ => {
            let msg = format!(
                "An external requires the name of the JS value you're referring to, like \"{}\".",
                name_text
            );
            p.err_at(equal_start, equal_end, DiagnosticCategory::Message(msg));
            vec![]
        }
    };

    let loc = p.mk_loc_idx_to_prev_end(loc_start_idx);
    let vd = ValueDescription {
        pval_name: name.clone(),
        pval_type: typ,
        pval_prim: prim,
        pval_attributes: attrs,
        pval_loc: loc,
    };

    let inline_attr_name = p.arena_mut().intern("res.inlineRecordDefinition");
    let inline_attr: Attribute = (mknoloc(inline_attr_name), Payload::PStr(Box::new(vec![])));
    let inline_types = inline_types_found
        .into_iter()
        .map(|(inline_name_idx, loc, kind, params)| TypeDeclaration {
            ptype_name: with_loc(inline_name_idx, name.loc.clone()),
            ptype_params: params,
            ptype_cstrs: vec![],
            ptype_kind: kind,
            ptype_private: PrivateFlag::Public,
            ptype_manifest: None,
            ptype_attributes: Attributes::from_vec(vec![inline_attr.clone()]),
            ptype_loc: loc,
        })
        .collect();

    p.eat_breadcrumb();
    (vd, inline_types)
}

/// Parse a value description (for external).
/// `loc_start_idx` should be a PosIdx for the position before any outer attributes
/// (to match OCaml's location and enable sharing).
fn parse_value_description(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    loc_start_idx: PosIdx,
    use_poly_type: bool,
) -> ValueDescription {
    let inner_attrs = parse_attributes(p);
    // Merge outer (structure-level) attrs with inner (name-level) attrs
    let attrs = outer_attrs.concat(inner_attrs);

    let name = match &p.token {
        Token::Lident(n) => {
            let n = n.clone();
            let loc = p.mk_loc_current();
            p.next();
            let n_idx = p.arena_mut().push_interned_string(&n);
            with_loc(n_idx, loc)
        }
        Token::String(s) => {
            // Escaped identifier like "export" - store with quotes for printer to recognize
            let n = format!("\"{}\"", s);
            let loc = p.mk_loc_current();
            p.next();
            let n_idx = p.arena_mut().push_string(n);
            with_loc(n_idx, loc)
        }
        _ => {
            p.err(DiagnosticCategory::Lident(p.token.clone().into_owned()));
            let err_idx = p.arena_mut().intern("error");
            mknoloc(err_idx)
        }
    };

    p.expect(Token::Colon);
    // OCaml: InExternal.status := true before parsing type
    let was_in_external = p.in_external;
    p.in_external = true;
    // OCaml's parse_sign_let_desc uses parse_poly_type_expr for signature `let`,
    // while parse_external_def uses parse_typ_expr for `external`.
    // The difference matters for `'a => T` where parse_poly_type_expr uses the
    // type var's location (excluding ') for the arrow start, matching OCaml.
    let typ_ct = if use_poly_type {
        typ::parse_poly_type_expr(p)
    } else {
        typ::parse_typ_expr(p)
    };
    let typ = p.arena_mut().push_core_type(typ_ct);
    p.in_external = was_in_external;

    // Parse primitive. Externals require `= "..."`; signature `let`
    // declarations share this helper and leave the primitive empty.
    let prim = if p.token == Token::Equal {
        let equal_start = p.start_pos.clone();
        let equal_end = p.end_pos.clone();
        p.next();
        match &p.token {
            Token::String(s) => {
                let s = s.clone();
                p.next();
                // OCaml only parses a single string here
                vec![p.arena_mut().push_interned_string(&s)]
            }
            _ => {
                // OCaml: emit error when = is not followed by a string
                let name_str = p.arena().get_string(name.txt).to_string();
                let msg = format!(
                    "An external requires the name of the JS value you're referring to, like \"{}\".",
                    name_str
                );
                p.err_at(equal_start, equal_end, DiagnosticCategory::Message(msg));
                vec![]
            }
        }
    } else {
        if !use_poly_type {
            p.expect(Token::Equal);
        }
        vec![]
    };

    // Use the PosIdx directly for sharing with structure_item/signature_item location
    let loc = p.mk_loc_idx_to_prev_end(loc_start_idx);
    ValueDescription {
        pval_name: name,
        pval_type: typ,
        pval_prim: prim,
        pval_attributes: attrs,
        pval_loc: loc,
    }
}

/// Parse a value description for signature `let` declarations.
///
/// This mirrors OCaml `parse_sign_let_desc` in `res_core.ml`:
/// - parse lowercase identifier name
/// - expect `:`
/// - parse with `parse_poly_type_expr` (not `parse_typ_expr`)
/// - no inner attributes and no primitive (`= "..."`) parsing
fn parse_signature_let_description(
    p: &mut Parser<'_>,
    attrs: Attributes,
    loc_start_idx: PosIdx,
) -> ValueDescription {
    let name = match &p.token {
        Token::Lident(n) => {
            let n = n.clone();
            let loc = p.mk_loc_current();
            p.next();
            let n_idx = p.arena_mut().push_interned_string(&n);
            with_loc(n_idx, loc)
        }
        Token::Eof => {
            p.err_unexpected();
            let loc = p.mk_loc_idx_to_prev_end(loc_start_idx);
            with_loc(p.arena_mut().intern("_"), loc)
        }
        _ => {
            p.err(DiagnosticCategory::Lident(p.token.clone().into_owned()));
            // OCaml parse_lident recovery: if keyword on same line, skip it.
            if p.token.is_keyword() && p.prev_end_pos.line == p.start_pos.line {
                p.next();
            }
            let loc = p.mk_loc_idx_to_prev_end(loc_start_idx);
            with_loc(p.arena_mut().intern("_"), loc)
        }
    };

    p.expect(Token::Colon);
    let typ_ct = typ::parse_poly_type_expr(p);
    let typ = p.arena_mut().push_core_type(typ_ct);

    let loc = p.mk_loc_idx_to_prev_end(loc_start_idx);
    ValueDescription {
        pval_name: name,
        pval_type: typ,
        pval_prim: vec![],
        pval_attributes: attrs,
        pval_loc: loc,
    }
}

/// Parse an extension constructor (for exception).
/// `exception_start` should be the position BEFORE 'exception' was consumed (if applicable).
pub fn parse_extension_constructor(
    p: &mut Parser<'_>,
    attrs: Attributes,
    exception_start: Option<PosIdx>,
) -> ExtensionConstructor {
    // Use provided start position (before 'exception') or current position
    let start_pos_idx = exception_start.unwrap_or_else(|| p.start_pos_idx());
    let error_idx = p.arena_mut().intern("Error");
    let constructor = parse_constructor(p).unwrap_or_else(|| ConstructorDeclaration {
        pcd_name: mknoloc(error_idx),
        pcd_args: ConstructorArguments::Pcstr_tuple(vec![]),
        pcd_res: None,
        pcd_loc: p.mk_loc_idx_to_prev_end(start_pos_idx),
        pcd_attributes: Attributes::new(),
    });

    let mut kind = ExtensionConstructorKind::Pext_decl(constructor.pcd_args, constructor.pcd_res);

    // Rebind: Constructor = Other
    if p.token == Token::Equal {
        p.next();
        let lid = parse_module_long_ident(p);
        kind = ExtensionConstructorKind::Pext_rebind(lid);
    }

    // Combine outer attributes with constructor attributes
    let mut all_attrs = attrs;
    all_attrs.extend(constructor.pcd_attributes);

    ExtensionConstructor {
        pext_name: constructor.pcd_name,
        pext_kind: kind,
        pext_loc: p.mk_loc_idx_to_prev_end(start_pos_idx),
        pext_attributes: all_attrs,
    }
}

/// Constructors of a type extension, after `+=` and the optional `private`.
/// OCaml `parse_type_extension` (compiler/syntax/src/res_core.ml:6429-6456): the
/// first constructor is parsed unconditionally, after at most two leading `|`.
fn parse_type_extension_constructors(p: &mut Parser<'_>) -> Vec<ExtensionConstructor> {
    let constr_start_idx = p.start_pos_idx();
    p.optional(&Token::Bar);
    if p.token == Token::Bar {
        p.next();
    }
    let mut constructors = vec![parse_extension_constructor(
        p,
        Attributes::new(),
        Some(constr_start_idx),
    )];
    while p.token == Token::Bar {
        let start_idx = p.start_pos_idx();
        p.next();
        constructors.push(parse_extension_constructor(
            p,
            Attributes::new(),
            Some(start_idx),
        ));
    }
    constructors
}

/// Parse a module definition.
/// `module_start_idx` should be the position BEFORE 'module' was consumed.
fn parse_module_definition(
    p: &mut Parser<'_>,
    module_start_idx: PosIdx,
    attrs: Attributes,
) -> Option<StructureItemDesc> {
    // Check for module type
    if p.token == Token::Typ {
        p.next();
        let mtd = parse_module_type_declaration(p, attrs, true);
        return Some(StructureItemDesc::Pstr_modtype(Box::new(mtd)));
    }

    // Check for rec
    let rec_flag = if p.token == Token::Rec {
        p.next();
        RecFlag::Recursive
    } else {
        RecFlag::Nonrecursive
    };

    // For recursive modules (module rec X = ...), use position before 'module'.
    // For non-recursive modules (module X = ...), use current position (after 'module').
    // This matches OCaml's parse_maybe_rec_module_binding behavior.
    let start_pos_idx = if rec_flag == RecFlag::Recursive {
        module_start_idx
    } else {
        p.start_pos_idx()
    };

    let mut bindings = vec![];

    let parse_binding = |p: &mut Parser<'_>,
                         binding_start_idx: PosIdx,
                         attrs: Attributes|
     -> Option<ModuleBinding> {
        let name = match &p.token {
            Token::Uident(n) => {
                let n = n.clone();
                let loc = p.mk_loc_current();
                p.next();
                let n_idx = p.arena_mut().push_interned_string(&n);
                with_loc(n_idx, loc)
            }
            _ => {
                p.err(DiagnosticCategory::Uident(p.token.clone().into_owned()));
                let error_idx = p.arena_mut().intern("_");
                mknoloc(error_idx)
            }
        };

        // Optional module type annotation (constraint)
        let mod_type = if p.token == Token::Colon {
            p.next();
            Some(parse_module_type(p))
        } else {
            None
        };

        p.expect(Token::Equal);
        let mut mod_expr = parse_module_expr(p);

        if let Some(mod_type) = mod_type {
            // Location spans from module type start to module expr end
            let loc = p.mk_loc_spanning(mod_type.pmty_loc, mod_expr.pmod_loc);
            let mod_expr_idx = p.arena_mut().push_mod_expr(mod_expr);
            let mod_type_idx = p.arena_mut().push_mod_type(mod_type);
            mod_expr = ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_constraint(mod_expr_idx, mod_type_idx)),
                pmod_loc: loc,
                pmod_attributes: Attributes::new(),
            };
        }

        let mod_expr_idx = p.arena_mut().push_mod_expr(mod_expr);
        Some(ModuleBinding {
            pmb_name: name,
            pmb_expr: mod_expr_idx,
            pmb_attributes: attrs,
            pmb_loc: p.mk_loc_idx_to_prev_end(binding_start_idx),
        })
    };

    if let Some(binding) = parse_binding(p, start_pos_idx, attrs) {
        bindings.push(binding);
    } else {
        return None;
    }

    // Parse additional module bindings with `and`
    // Also handle attributes/doc comments before `and`: `@attr and M = ...` or `/** doc */ and M = ...`
    // OCaml `parse_module_definition` only reads `and` bindings for `module rec`.
    while rec_flag == RecFlag::Recursive {
        if p.token == Token::And {
            // Capture start position BEFORE consuming `and`
            let binding_start_idx = p.start_pos_idx();
            p.next();
            let binding_attrs = parse_attributes(p);
            if let Some(binding) = parse_binding(p, binding_start_idx, binding_attrs) {
                bindings.push(binding);
            }
        } else if matches!(p.token, Token::At | Token::AtAt | Token::DocComment { .. }) {
            // Look ahead to see if attributes/doc comments are followed by And
            let has_and_after = p.lookahead(|state| {
                // Skip attributes and doc comments
                while matches!(
                    state.token,
                    Token::At | Token::AtAt | Token::DocComment { .. }
                ) {
                    if matches!(state.token, Token::DocComment { .. }) {
                        state.next();
                    } else {
                        state.next(); // @
                        // Skip the attribute identifier and any payload
                        while !matches!(
                            state.token,
                            Token::At
                                | Token::AtAt
                                | Token::DocComment { .. }
                                | Token::And
                                | Token::Eof
                                | Token::Let { .. }
                                | Token::Typ
                                | Token::Module
                                | Token::External
                                | Token::Open
                                | Token::Include
                        ) {
                            state.next();
                        }
                    }
                }
                state.token == Token::And
            });
            if !has_and_after {
                break;
            }
            // Parse the attributes, then the `and` keyword
            let binding_start_idx = p.start_pos_idx();
            let binding_attrs = parse_attributes(p);
            if p.token == Token::And {
                p.next();
            }
            if let Some(binding) = parse_binding(p, binding_start_idx, binding_attrs) {
                bindings.push(binding);
            }
        } else {
            break;
        }
    }

    if rec_flag == RecFlag::Recursive {
        Some(StructureItemDesc::Pstr_recmodule(Box::new(bindings)))
    } else if bindings.len() == 1 {
        Some(StructureItemDesc::Pstr_module(Box::new(bindings.remove(0))))
    } else {
        Some(StructureItemDesc::Pstr_recmodule(Box::new(bindings)))
    }
}

/// Parse a module declaration (for signature).
/// Parse a module declaration.
/// If `start_pos_idx` is Some, use it for the location (for recursive modules where it includes 'module rec' or 'and').
/// If `start_pos_idx` is None, capture it at the current position (for non-recursive modules where loc starts at name).
fn parse_module_declaration(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    start_pos_idx: Option<PosIdx>,
) -> ModuleDeclaration {
    let start_pos_idx = start_pos_idx.unwrap_or_else(|| p.start_pos_idx());
    let inner_attrs = parse_attributes(p);
    // Merge outer (signature item level) attrs with inner (name level) attrs
    let attrs = outer_attrs.concat(inner_attrs);

    let name = match &p.token {
        Token::Uident(n) => {
            let n_clone = n.clone();
            let n_idx = p.arena_mut().push_interned_string(&n_clone);
            let loc = p.mk_loc_current();
            p.next();
            with_loc(n_idx, loc)
        }
        _ => {
            p.err(DiagnosticCategory::Uident(p.token.clone().into_owned()));
            let error_idx = p.arena_mut().intern("_");
            mknoloc(error_idx)
        }
    };

    // Handle both `module X: T` (type annotation) and `module X = M` (alias)
    // In signatures, `=` can be followed by a module type or a module alias
    let mod_type = if p.token == Token::Equal {
        p.next();
        // Check if this is `= { ... }` (module type) or `= ModuleName` (alias)
        if p.token == Token::Lbrace {
            // Module type: module X = { ... }
            parse_module_type(p)
        } else {
            // Module alias: module X = M
            // OCaml uses a ghost location for Pmty_alias in module declarations
            let lid = parse_module_long_ident(p);
            ModuleType {
                pmty_desc: Box::new(ModuleTypeDesc::Pmty_alias(lid)),
                pmty_loc: Location::none(),
                pmty_attributes: Attributes::new(),
            }
        }
    } else {
        p.expect(Token::Colon);
        parse_module_type(p)
    };

    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let mod_type_idx = p.arena_mut().push_mod_type(mod_type);
    ModuleDeclaration {
        pmd_name: name,
        pmd_type: mod_type_idx,
        pmd_attributes: attrs,
        pmd_loc: loc,
    }
}

/// Parse attributes only if followed by `and` keyword.
/// This uses speculative parsing with backtracking like OCaml's parse_attributes_and_binding.
/// If attrs are present but not followed by `and`, parser state is restored and empty attrs returned.
fn parse_attributes_and_binding(p: &mut Parser<'_>) -> Attributes {
    match &p.token {
        Token::At | Token::DocComment { .. } => {
            // Save parser state for potential backtrack
            let snapshot = p.snapshot();

            // Parse attributes
            let attrs = parse_attributes(p);

            // Check if `and` follows
            if p.token == Token::And {
                // Keep the attrs - they're for the `and` clause
                attrs
            } else {
                // Restore parser state - attrs belong to next item
                p.restore(snapshot);
                Attributes::new()
            }
        }
        _ => Attributes::new(),
    }
}

/// Parse recursive module declarations (for signature).
/// Parse recursive module declarations (for signature).
/// `start_pos_idx` is the position before `module rec`, captured by the caller.
fn parse_rec_module_declarations(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    start_pos_idx: PosIdx,
) -> Vec<ModuleDeclaration> {
    let mut decls = vec![];

    // Parse first declaration (gets the outer attrs and start_pos from caller)
    // For recursive modules, location includes 'module rec'
    decls.push(parse_module_declaration(
        p,
        outer_attrs,
        Some(start_pos_idx),
    ));

    // Parse additional declarations with `and`
    // Uses parse_attributes_and_binding which backtracks if attrs aren't followed by `and`
    loop {
        // Capture start_pos BEFORE consuming `and` (like OCaml)
        let and_start_pos_idx = p.start_pos_idx();
        let attrs = parse_attributes_and_binding(p);
        if p.token == Token::And {
            p.next();
            // For 'and' declarations, location includes 'and'
            decls.push(parse_module_declaration(p, attrs, Some(and_start_pos_idx)));
        } else {
            break;
        }
    }

    decls
}

/// Parse a module type declaration.
/// `in_structure` indicates whether this is in a structure (.res) or signature (.resi).
/// In structure context, OCaml passes ~loc, in signature context it doesn't (uses Location.none).
fn parse_module_type_declaration(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    in_structure: bool,
) -> ModuleTypeDeclaration {
    let name_start_idx = p.start_pos_idx();
    let inner_attrs = parse_attributes(p);
    // Merge outer (signature item level) attrs with inner (name level) attrs
    let attrs = outer_attrs.concat(inner_attrs);

    let name = match &p.token {
        Token::Uident(n) | Token::Lident(n) => {
            let n_clone = n.clone();
            let n_idx = p.arena_mut().push_interned_string(&n_clone);
            let loc = p.mk_loc_current();
            p.next();
            with_loc(n_idx, loc)
        }
        _ => {
            p.err(DiagnosticCategory::Uident(p.token.clone().into_owned()));
            let error_idx = p.arena_mut().intern("_");
            mknoloc(error_idx)
        }
    };

    let typ = if in_structure {
        if p.token == Token::Equal {
            p.next();
            let mt = parse_module_type(p);
            Some(p.arena_mut().push_mod_type(mt))
        } else {
            p.expect(Token::Equal);
            Some(p.arena_mut().push_mod_type(recover::default_module_type()))
        }
    } else if p.token == Token::Equal {
        p.next();
        let mt = parse_module_type(p);
        Some(p.arena_mut().push_mod_type(mt))
    } else {
        None
    };

    // In structure context (parse_module_type_impl), OCaml passes ~loc:(mk_loc name_start p.prev_end_pos)
    // In signature context (parse_module_type_declaration), OCaml doesn't pass ~loc, uses Location.none
    let loc = if in_structure {
        p.mk_loc_idx_to_prev_end(name_start_idx)
    } else {
        Location::none()
    };

    ModuleTypeDeclaration {
        pmtd_name: name,
        pmtd_type: typ,
        pmtd_attributes: attrs,
        pmtd_loc: loc,
    }
}

/// Parse attributes (including doc comments which become res.doc attributes).
fn parse_attributes(p: &mut Parser<'_>) -> Attributes {
    // OCaml `parse_attributes` = `parse_region ~grammar:Grammar.Attribute`
    // (compiler/syntax/src/res_core.ml:7635-7636, 1177-1192).
    p.leave_breadcrumb(super::grammar::Grammar::Attribute);
    let mut attrs = vec![];
    loop {
        match &p.token {
            Token::At => {
                // Capture start_pos before consuming @ so attribute location includes it
                let attr_start_idx = p.start_pos_idx();
                p.next();
                attrs.push(parse_attribute_body(p, attr_start_idx));
            }
            Token::DocComment { loc, content } => {
                let loc_cloned = loc.clone();
                let content = content.clone();
                p.next();
                let loc = p.from_location(&loc_cloned);
                attrs.push(super::core::doc_comment_to_attribute(
                    p.arena_mut(),
                    loc,
                    content,
                ));
            }
            _ => break,
        }
    }
    p.eat_breadcrumb();
    Attributes::from_vec(attrs)
}

/// Parse an attribute body.
/// `start_pos_idx` should be the position BEFORE the `@` or `@@` token was consumed.
fn parse_attribute_body(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Attribute {
    // OCaml `parse_attribute_id` (compiler/syntax/src/res_core.ml:7531-7556).
    let attr_name = parse_extension_id(p, start_pos_idx);

    // Parse optional payload
    let is_adjacent = p.start_pos.cnum == p.prev_end_pos.cnum;
    let payload = if p.token == Token::Lparen && is_adjacent {
        p.next();
        let payload = parse_payload(p);
        p.expect(Token::Rparen);
        payload
    } else {
        Payload::PStr(Box::new(vec![]))
    };

    (attr_name, payload)
}

/// Parse an attribute payload.
/// Payloads can be:
/// - Structure items: `(expr1 expr2 ...)` - the default
/// - Type: `(: type)` - indicated by leading colon followed by type
/// - Signature: `(: signature_items)` - indicated by leading colon followed by signature items
/// - Pattern: `(? pattern)` or `(? pattern when guard)` - indicated by leading question mark
pub fn parse_payload(p: &mut Parser<'_>) -> Payload {
    // OCaml `parse_payload` (compiler/syntax/src/res_core.ml:7568-7610), after the
    // opening `(` has been consumed by the caller.
    match p.token {
        Token::Colon => {
            p.next();
            if super::grammar::is_signature_item_start(&p.token) {
                Payload::PSig(Box::new(parse_signature_delimited(p)))
            } else {
                let typ = super::typ::parse_typ_expr(p);
                let typ_idx = p.arena_mut().push_core_type(typ);
                Payload::PTyp(typ_idx)
            }
        }
        Token::Question => {
            p.next();
            let pat = super::pattern::parse_pattern(p);
            let pat_idx = p.arena_mut().push_pat(pat);
            let guard = if matches!(p.token, Token::When | Token::If) {
                p.next();
                let guard_expr = super::expr::parse_expr(p);
                Some(p.arena_mut().push_expr(guard_expr))
            } else {
                None
            };
            Payload::PPat(Box::new((pat_idx, guard)))
        }
        _ => Payload::PStr(Box::new(parse_structure_delimited(p, Token::Rparen))),
    }
}

/// OCaml `parse_delimited_region ~grammar:Grammar.Signature ~closing:Rparen
/// ~f:(parse_signature_item_region pending_signature_items)`.
fn parse_signature_delimited(p: &mut Parser<'_>) -> Vec<SignatureItem> {
    use super::core::recover::should_abort_list_parse;

    let outer_pending = std::mem::take(&mut p.pending_signature_items);
    p.leave_breadcrumb(Grammar::Signature);
    let mut items = vec![];
    loop {
        if let Some(item) = p.pending_signature_items.pop() {
            items.push(item);
            continue;
        }
        if p.token == Token::Rparen || p.token == Token::Eof {
            break;
        }
        match parse_signature_item(p) {
            Some(item) => items.push(item),
            None => {
                if p.token == Token::Rparen || p.token == Token::Eof || should_abort_list_parse(p) {
                    break;
                }
                p.err_unexpected();
                p.next();
            }
        }
    }
    p.eat_breadcrumb();
    p.pending_signature_items = outer_pending;
    items
}

/// Parse an extension/attribute identifier, matching OCaml's `parse_attribute_id`.
pub fn parse_extension_id(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Located<StrIdx> {
    let mut id = String::new();

    loop {
        let name = match &p.token {
            Token::Lident(name) | Token::Uident(name) => Some(name.to_string()),
            token if token.is_keyword() => Some(token.to_string()),
            _ => None,
        };

        match name {
            Some(name) => {
                id.push_str(&name);
                p.next();
                if p.token == Token::Dot {
                    p.next();
                    id.push('.');
                    continue;
                }
                break;
            }
            None => {
                p.err_unexpected();
                break;
            }
        }
    }

    let id_idx = p.arena_mut().push_string(id);
    with_loc(id_idx, p.mk_loc_idx_to_prev_end(start_pos_idx))
}

/// Parse an extension.
fn parse_extension(p: &mut Parser<'_>) -> Extension {
    // Capture start position BEFORE consuming % or %% so extension location includes it
    let id_start_idx = p.start_pos_idx();

    // Handle both %ext and %%ext (single and double percent)
    if p.token == Token::PercentPercent {
        p.next();
    } else {
        p.expect(Token::Percent);
    }
    let id = parse_extension_id(p, id_start_idx);

    // Parse optional payload only if it's immediately adjacent.
    let is_adjacent = p.start_pos.cnum == p.prev_end_pos.cnum;
    let payload = if p.token == Token::Lparen && is_adjacent {
        p.next();
        let payload = parse_payload(p);
        p.expect(Token::Rparen);
        payload
    } else {
        Payload::PStr(Box::new(vec![]))
    };

    (id, payload)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse source code into a structure with a timeout.
    fn parse_with_timeout(source: &str) -> Structure {
        crate::parser::test_utils::parse_with_timeout(source, parse_structure)
    }

    #[test]
    fn test_parse_empty_structure() {
        let structure = parse_with_timeout("");
        assert!(structure.is_empty());
    }

    #[test]
    fn test_parse_let_binding() {
        let structure = parse_with_timeout("let x = 42");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            *structure[0].pstr_desc,
            StructureItemDesc::Pstr_value(_)
        ));
    }

    #[test]
    fn test_parse_open() {
        let structure = parse_with_timeout("open Belt");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            *structure[0].pstr_desc,
            StructureItemDesc::Pstr_open(_)
        ));
    }

    #[test]
    fn test_parse_type_declaration() {
        let structure = parse_with_timeout("type t = int");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            *structure[0].pstr_desc,
            StructureItemDesc::Pstr_type(_)
        ));
    }

    #[test]
    fn test_parse_variant_type() {
        let structure = parse_with_timeout("type color = | Red | Green | Blue");
        assert_eq!(structure.len(), 1);
        if let StructureItemDesc::Pstr_type(inner) = &*structure[0].pstr_desc {
            let (_, ref type_decls) = **inner;
            assert_eq!(type_decls.len(), 1);
            if let TypeKind::Ptype_variant(constructors) = &type_decls[0].ptype_kind {
                assert_eq!(constructors.len(), 3);
            } else {
                panic!("Expected variant type");
            }
        } else {
            panic!("Expected type declaration");
        }
    }

    #[test]
    fn test_parse_record_type() {
        let structure = parse_with_timeout("type person = { name: string, age: int }");
        assert_eq!(structure.len(), 1);
        if let StructureItemDesc::Pstr_type(inner) = &*structure[0].pstr_desc {
            let (_, ref type_decls) = **inner;
            assert_eq!(type_decls.len(), 1);
            if let TypeKind::Ptype_record(labels) = &type_decls[0].ptype_kind {
                assert_eq!(labels.len(), 2);
            } else {
                panic!("Expected record type");
            }
        } else {
            panic!("Expected type declaration");
        }
    }

    #[test]
    fn test_parse_module_definition() {
        let structure = parse_with_timeout("module M = { let x = 1 }");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            *structure[0].pstr_desc,
            StructureItemDesc::Pstr_module(_)
        ));
    }

    #[test]
    fn test_parse_external() {
        let structure = parse_with_timeout("external log: string => unit = \"console.log\"");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            *structure[0].pstr_desc,
            StructureItemDesc::Pstr_primitive(_)
        ));
    }

    #[test]
    fn test_parse_exception() {
        let structure = parse_with_timeout("exception MyError(string)");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            *structure[0].pstr_desc,
            StructureItemDesc::Pstr_exception(_)
        ));
    }

    #[test]
    fn test_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Structure>();
        assert_send_sync::<Signature>();
    }
}
