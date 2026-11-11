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
                p.prev_end_pos,
                p.end_pos,
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
                p.prev_end_pos,
                p.end_pos,
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
                popen_attributes: attrs,
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
                    start_pos,
                    p.start_pos,
                    DiagnosticCategory::Message(
                        "let? is not allowed to be recursive. Use a regular `let` or remove `rec`."
                            .to_string(),
                    ),
                );
            }
            // Pass start_pos_idx to enable position sharing with structure_item
            let (bindings, _binding_loc_idx) =
                parse_let_bindings(p, start_pos_idx, let_end_pos_idx, rec_flag, attrs, unwrap);
            parse_newline_or_semicolon_structure(p);
            // Don't share LocIdx - OCaml creates separate Location objects for pstr_loc and pvb_loc.
            // The internal positions (PosIdx) are shared, but the Location records themselves are separate.
            Some(StructureItemDesc::Pstr_value((
                rec_flag,
                p.arena_mut().push_vb_list(&bindings),
            )))
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
            let (vd, inline_types) = parse_external_value_description(p, attrs, item_start_idx);
            parse_newline_or_semicolon_structure(p);
            if inline_types.is_empty() {
                Some(StructureItemDesc::Pstr_primitive(Box::new(vd)))
            } else {
                // OCaml compiler/syntax/src/res_core.ml:6729-6741 emits the
                // generated inline type item first, then queues the primitive.
                let loc = p.mk_loc_idx_to_prev_end(item_start_idx);
                item_loc_idx = Some(loc);
                p.pending_structure_items.push(StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(vd)),
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
            let ext = parse_extension_constructor(p, attrs, Some(exception_start_idx), false);
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
                Some(StructureItemDesc::Pstr_eval(Box::new((expr_idx, attrs))))
            } else {
                let def = parse_module_definition(p, module_start_idx, attrs);
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
                    pincl_attributes: attrs,
                },
            )))
        }
        Token::At | Token::AtAt => {
            // Floating attribute or extension
            // Capture start_pos before consuming @ or @@ so attribute location includes it
            let attr_start_idx = p.start_pos_idx();
            p.next();
            let attr = parse_attribute_body(p, attr_start_idx);
            parse_newline_or_semicolon_structure(p);
            Some(StructureItemDesc::Pstr_attribute(Box::new(attr)))
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
            let payload = match parse_macro_arguments(p, &id) {
                Some(payload) => payload,
                None => {
                    let payload = parse_payload_region(p);
                    raw_source_extension_payload(p, &id, payload)
                }
            };
            parse_newline_or_semicolon_structure(p);
            Some(StructureItemDesc::Pstr_extension(Box::new((
                (id, payload),
                attrs,
            ))))
        }
        _ => {
            // Could be an expression
            if grammar::is_expr_start(&p.token) {
                let expr = expr::parse_expr(p);
                parse_newline_or_semicolon_structure(p);
                let expr_idx = p.arena_mut().push_expr(expr);
                Some(StructureItemDesc::Pstr_eval(Box::new((expr_idx, attrs))))
            } else if let Some(attr) = attrs.first() {
                // OCaml: when attrs are present but no valid item follows,
                // report the "Did you forget to attach" error and produce exprhole
                let attr_name_str = p.arena().get_string(attr.0.txt).to_string();
                let attr_loc = p.to_location(attr.0.loc);
                p.err_at(
                    attr_loc.loc_start,
                    attr_loc.loc_end,
                    DiagnosticCategory::message(error_messages::attribute_without_node(
                        &attr_name_str,
                    )),
                );
                let expr = expr::parse_expr(p);
                parse_newline_or_semicolon_structure(p);
                let expr_idx = p.arena_mut().push_expr(expr);
                Some(StructureItemDesc::Pstr_eval(Box::new((expr_idx, attrs))))
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
        pstr_desc: d,
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
    let params = parse_type_params(p, |_| path.join("."));
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
/// `parent` renders the dotted parent path; it is only needed for the
/// angle-bracket error message.
fn parse_type_params(
    p: &mut Parser<'_>,
    parent: impl FnOnce(&crate::parse_arena::ParseArena) -> String,
) -> Vec<(CoreTypeIdx, Variance)> {
    let opening = p.token.clone().into_owned();
    if !matches!(opening, Token::LessThan | Token::Lparen)
        || p.start_pos.line != p.prev_end_pos.line
    {
        return vec![];
    }
    let opening_start = p.start_pos;
    p.leave_breadcrumb(Grammar::TypeParams);
    p.next();
    let params = super::core::parse_comma_delimited_region(
        p,
        Grammar::TypeParams,
        Token::GreaterThan,
        parse_type_param,
    );
    if p.token == Token::Rparen && opening == Token::Lparen {
        // OCaml `parse_type_params` (res_core.ml:5762-5781): the message
        // reprints the parent longident and `print_type_params`.
        let parent_doc = super::doc::Doc::text(parent(p.arena()));
        let params_doc = super::printer::print_type_params(
            &super::printer::PrinterState::init(),
            &params,
            &mut super::comment_table::CommentTable::new(),
            p.arena(),
        );
        let msg = super::doc::Doc::breakable_group(
            super::doc::Doc::concat(vec![
                super::doc::Doc::text("Type parameters require angle brackets:"),
                super::doc::Doc::indent(super::doc::Doc::concat(vec![
                    super::doc::Doc::line(),
                    super::doc::Doc::concat(vec![parent_doc, params_doc]),
                ])),
            ]),
            true,
        )
        .to_string(80);
        let end = p.end_pos;
        p.err_at(opening_start, end, DiagnosticCategory::Message(msg));
        p.next();
    } else {
        p.expect(Token::GreaterThan);
    }
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
    let first = parse_type_declaration_body(p, attrs, Some(&inline_ctx), start_idx, name, params);
    let mut decls = vec![];
    let ctx = inline_ctx.into_inner();
    let has_inline_types = !ctx.found_inline_types.is_empty();
    if has_inline_types {
        for (inline_name_idx, loc, type_kind, params) in ctx.found_inline_types.iter() {
            decls.push(TypeDeclaration {
                ptype_name: with_loc(*inline_name_idx, ctx.outer_name_loc),
                ptype_params: params.clone(),
                ptype_cstrs: vec![],
                ptype_kind: type_kind.clone(),
                ptype_private: PrivateFlag::Public,
                ptype_manifest: None,
                ptype_origin: TypeDeclarationOrigin::Inline_record_definition,
                ptype_attributes: Attributes::new(),
                ptype_loc: *loc,
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
    let params = parse_type_params(p, |_| name.clone());
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
                popen_attributes: attrs,
            })))
        }
        Token::Let { unwrap } => {
            // OCaml parse_signature_item_region (res_core.ml:7308-7318).
            if *unwrap {
                p.err_at(
                    *p.arena().get_position(start_pos_idx),
                    p.end_pos,
                    DiagnosticCategory::Message(
                        "let? is not allowed in signatures. Use a regular `let` instead."
                            .to_string(),
                    ),
                );
                p.next();
            }
            p.begin_region();
            let vd = parse_sign_let_desc(p, attrs);
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
            let (vd, inline_types) = parse_external_value_description(p, attrs, start_pos_idx);
            parse_newline_or_semicolon_signature(p);
            if inline_types.is_empty() {
                Some(SignatureItemDesc::Psig_value(Box::new(vd)))
            } else {
                // OCaml compiler/syntax/src/res_core.ml:7383-7395 emits the
                // generated inline type item first, then queues the value item.
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                item_loc_idx = Some(loc);
                p.pending_signature_items.push(SignatureItem {
                    psig_desc: SignatureItemDesc::Psig_value(Box::new(vd)),
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
            let ext = parse_extension_constructor(p, attrs, Some(exception_start_idx), false);
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
                let mtd = parse_module_type_declaration(p, attrs, false);
                // No parse_newline_or_semicolon_signature for module type - matches OCaml
                Some(SignatureItemDesc::Psig_modtype(Box::new(mtd)))
            } else if p.token == Token::Rec {
                p.next();
                // For recursive modules, OCaml's pmd_loc includes attributes BEFORE 'module rec'
                // OCaml passes start_pos (captured BEFORE attributes) to parse_rec_module_spec
                let mds = parse_rec_module_declarations(p, attrs, start_pos_idx);
                parse_newline_or_semicolon_signature(p);
                Some(SignatureItemDesc::Psig_recmodule(Box::new(mds)))
            } else {
                // For non-recursive modules, location starts at name (not 'module')
                let md = parse_module_declaration(p, attrs);
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
                    pincl_attributes: attrs,
                },
            )))
        }
        Token::At | Token::AtAt => {
            // Capture start_pos before consuming @ or @@ so attribute location includes it
            let attr_start_idx = p.start_pos_idx();
            p.next();
            let attr = parse_attribute_body(p, attr_start_idx);
            parse_newline_or_semicolon_signature(p);
            Some(SignatureItemDesc::Psig_attribute(Box::new(attr)))
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
        // OCaml res_core.ml:7407-7411: only `%%` starts a signature extension.
        Token::PercentPercent => {
            let ext = parse_extension(p, true);
            parse_newline_or_semicolon_signature(p);
            Some(SignatureItemDesc::Psig_extension(Box::new((ext, attrs))))
        }
        _ => {
            // OCaml: when attrs are present but no valid item follows, report the error
            // and return a sigitemhole placeholder
            if let Some(attr) = attrs.first() {
                let attr_name_str = p.arena().get_string(attr.0.txt).to_string();
                let attr_loc = p.to_location(attr.0.loc);
                p.err_at(
                    attr_loc.loc_start,
                    attr_loc.loc_end,
                    DiagnosticCategory::message(error_messages::attribute_without_node(
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
            psig_desc: d,
            psig_loc,
        }
    })
}

// ============================================================================
// Module Expression Parsing
// ============================================================================

/// Parse a module expression.
pub fn parse_module_expr(p: &mut Parser<'_>) -> ModuleExpr {
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
                Payload::PStr(Box::default()),
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

/// OCaml `parse_constrained_mod_expr` (res_core.ml:6955-6963).
fn parse_constrained_mod_expr(p: &mut Parser<'_>) -> ModuleExpr {
    let mod_expr = parse_module_expr(p);
    if p.token != Token::Colon {
        return mod_expr;
    }
    p.next();
    let mod_type = parse_module_type(p);
    let loc = p.mk_loc_spanning(mod_expr.pmod_loc, mod_type.pmty_loc);
    let expr_idx = p.arena_mut().push_mod_expr(mod_expr);
    let mod_type_idx = p.arena_mut().push_mod_type(mod_type);
    ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_constraint(expr_idx, mod_type_idx),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    }
}

/// OCaml `parse_constrained_mod_expr_region` (res_core.ml:6965-6968).
fn parse_constrained_mod_expr_region(p: &mut Parser<'_>) -> Option<ModuleExpr> {
    if grammar::is_mod_expr_start(&p.token) {
        Some(parse_constrained_mod_expr(p))
    } else {
        None
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
                Payload::PStr(Box::default()),
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
                pmod_desc: ModuleExprDesc::Pmod_ident(lid),
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
                pmod_desc: ModuleExprDesc::Pmod_structure(Box::new(items)),
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
                    // Unit module expression: (). OCaml res_core.ml:6782-6786 builds
                    // the location before `Parser.expect Rparen`.
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    p.next();
                    ModuleExpr {
                        pmod_desc: ModuleExprDesc::Pmod_structure(Box::default()),
                        pmod_loc: loc,
                        pmod_attributes: Attributes::new(),
                    }
                } else {
                    let inner = parse_constrained_mod_expr(p);
                    p.expect(Token::Rparen);
                    // OCaml: parse_atomic_module_expr does NOT update the location to include parens.
                    // It just returns mod_expr as-is, keeping the inner expression's original location.
                    inner
                }
            }
        }
        Token::Percent => {
            // Module extension
            let ext = parse_extension(p, false);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_extension(Box::new(ext)),
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
                    // OCaml `parse_module_expr` unpack branch (res_core.ml:6793-6798).
                    let colon_pos_idx = p.start_pos_idx();
                    p.next();
                    let attrs = parse_attributes(p);
                    let pkg_type = super::typ::parse_package_type(p, colon_pos_idx, attrs);
                    let pkg_type_idx = p.arena_mut().push_core_type(pkg_type);
                    // OCaml: expect Rparen first, then create constraint with loc including Rparen
                    p.expect(Token::Rparen);
                    let constraint_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let expr_idx = p.arena_mut().push_expr(expr);
                    Expression {
                        pexp_desc: ExpressionDesc::Pexp_constraint(Box::new((
                            expr_idx,
                            pkg_type_idx,
                        ))),
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
                    pmod_desc: ModuleExprDesc::Pmod_unpack(final_expr_idx),
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
        // OCaml `parse_module_application` (res_core.ml:6970-6993).
        let lparen_pos_idx = p.start_pos_idx();
        p.expect(Token::Lparen);
        let args = super::core::parse_comma_delimited_region(
            p,
            Grammar::ModExprList,
            Token::Rparen,
            parse_constrained_mod_expr_region,
        );
        p.expect(Token::Rparen);
        let args = if args.is_empty() {
            let loc = p.mk_loc_idx_to_prev_end(lparen_pos_idx);
            vec![ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_structure(Box::default()),
                pmod_loc: loc,
                pmod_attributes: Attributes::new(),
            }]
        } else {
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
            let loc = p.mk_loc_idx(start_idx, end_idx);
            let result_idx = p.arena_mut().push_mod_expr(result);
            let arg_idx = p.arena_mut().push_mod_expr(arg);
            result = ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_apply(result_idx, arg_idx),
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
                    // `parse_module_long_ident_tail ~lowercase:false`
                    // (res_core.ml:806-826) after the first `.`.
                    p.next();
                    loop {
                        match &p.token {
                            Token::Uident(name) => {
                                let name_clone = name.clone();
                                let name_str_idx = p.arena_mut().push_interned_string(&name_clone);
                                lid = Longident::Ldot(Box::new(lid), name_str_idx);
                                p.next();
                                if p.token == Token::Dot {
                                    p.next();
                                    continue;
                                }
                                break;
                            }
                            _ => {
                                p.err(DiagnosticCategory::Uident(p.token.clone().into_owned()));
                                let hole = p.arena_mut().intern("_");
                                lid = Longident::Ldot(Box::new(lid), hole);
                                break;
                            }
                        }
                    }
                    let lid_idx = p.push_longident(lid);
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let mod_type = ModuleType {
                        pmty_desc: ModuleTypeDesc::Pmty_ident(with_loc(lid_idx, loc)),
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
                    let lid_idx = p.push_lident(&ident);
                    let mod_ident = with_loc(lid_idx, loc);
                    let mod_type = ModuleType {
                        pmty_desc: ModuleTypeDesc::Pmty_ident(mod_ident),
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
        _ => None,
    }
}

/// Parse functor arguments: ( arg1, arg2, ... )
/// OCaml `parse_functor_args` (res_core.ml:6880-6893).
fn parse_functor_args(p: &mut Parser<'_>) -> Vec<FunctorArg> {
    let paren_start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lparen);
    let mut args = super::core::parse_comma_delimited_region(
        p,
        Grammar::FunctorArgs,
        Token::Rparen,
        parse_functor_arg,
    );
    p.expect(Token::Rparen);

    if args.is_empty() {
        let star_idx = p.arena_mut().intern("*");
        return vec![FunctorArg {
            attrs: Attributes::new(),
            name: with_loc(star_idx, p.mk_loc_idx_to_prev_end(paren_start_pos_idx)),
            mod_type: None,
            start_pos_idx: paren_start_pos_idx,
        }];
    }
    // The outermost functor built from these arguments is located from the
    // opening parenthesis (`{mod_expr with pmod_loc = mk_loc start_pos
    // end_pos}` in parse_functor_module_expr/parse_functor_module_type).
    args[0].start_pos_idx = paren_start_pos_idx;
    args
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
            let loc = p.mk_loc_idx(start_idx, end_idx);
            let expr_idx = p.arena_mut().push_mod_expr(rhs_module_expr);
            let mod_type_idx = p.arena_mut().push_mod_type(mod_type);
            ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_constraint(expr_idx, mod_type_idx),
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
            pmod_desc: ModuleExprDesc::Pmod_functor(Box::new((arg.name, mod_type_idx, acc_idx))),
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
    // OCaml `parse_module_type` (res_core.ml:7174-7192).
    let attrs = parse_attributes(p);

    let typ = if es6_arrow && is_es6_arrow_functor(p) {
        parse_functor_module_type(p)
    } else {
        let modty = parse_primary_module_type(p);
        if es6_arrow && p.token == Token::EqualGreater {
            // `S => MT`: an unnamed functor parameter.
            p.next();
            let rhs = parse_module_type_no_with(p);
            let start_idx = p.loc_start_idx(modty.pmty_loc);
            let end_idx = p.prev_end_pos_idx();
            let loc = p.mk_loc_idx(start_idx, end_idx);
            let param_type_idx = p.arena_mut().push_mod_type(modty);
            let rhs_idx = p.arena_mut().push_mod_type(rhs);
            ModuleType {
                pmty_desc: ModuleTypeDesc::Pmty_functor(Box::new((
                    mknoloc(p.arena_mut().intern("_")),
                    Some(param_type_idx),
                    rhs_idx,
                ))),
                pmty_loc: loc,
                pmty_attributes: Attributes::new(),
            }
        } else {
            modty
        }
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
        // `mk_loc module_type.pmty_loc.loc_start p.prev_end_pos`.
        let typ_start_idx = p.loc_start_idx(typ.pmty_loc);
        let loc = p.mk_loc_idx_to_prev_end(typ_start_idx);
        let typ_idx = p.arena_mut().push_mod_type(typ);
        ModuleType {
            pmty_desc: ModuleTypeDesc::Pmty_with(Box::new((typ_idx, constraints))),
            pmty_loc: loc,
            pmty_attributes: Attributes::new(),
        }
    } else {
        typ
    }
}

/// OCaml `parse_functor_module_type` (res_core.ml:7144-7157).
fn parse_functor_module_type(p: &mut Parser<'_>) -> ModuleType {
    let start_pos_idx = p.start_pos_idx();
    let args = parse_functor_args(p);
    p.expect(Token::EqualGreater);
    let rhs = parse_module_type(p);
    let end_pos_idx = p.prev_end_pos_idx();
    let mut mod_type = args.into_iter().rev().fold(rhs, |acc, arg| {
        let loc = p.mk_loc_idx(arg.start_pos_idx, end_pos_idx);
        let acc_idx = p.arena_mut().push_mod_type(acc);
        let mod_type_idx = arg.mod_type.map(|mt| p.arena_mut().push_mod_type(mt));
        ModuleType {
            pmty_desc: ModuleTypeDesc::Pmty_functor(Box::new((arg.name, mod_type_idx, acc_idx))),
            pmty_loc: loc,
            pmty_attributes: arg.attrs,
        }
    });
    mod_type.pmty_loc = p.mk_loc_idx(start_pos_idx, end_pos_idx);
    mod_type
}

/// Parse a primary module type.
fn parse_primary_module_type(p: &mut Parser<'_>) -> ModuleType {
    let start_pos_idx = p.start_pos_idx();

    match &p.token {
        Token::Uident(_) | Token::Lident(_) => {
            // Module type path
            let lid = parse_module_type_long_ident(p);
            ModuleType {
                pmty_desc: ModuleTypeDesc::Pmty_ident(lid),
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
                pmty_desc: ModuleTypeDesc::Pmty_signature(Box::new(items)),
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
                pmty_desc: ModuleTypeDesc::Pmty_typeof(mod_expr_idx),
                pmty_loc: loc,
                pmty_attributes: Attributes::new(),
            }
        }
        Token::Percent => {
            // Module type extension
            let ext = parse_extension(p, false);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            ModuleType {
                pmty_desc: ModuleTypeDesc::Pmty_extension(Box::new(ext)),
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
/// OCaml `parse_type_constraints` (res_core.ml:5819-5820):
/// `parse_region ~grammar:Grammar.TypeConstraint ~f:parse_type_constraint`.
fn parse_type_constraints(p: &mut Parser<'_>) -> Vec<(CoreTypeIdx, CoreTypeIdx, Location)> {
    super::core::parse_region(p, Grammar::TypeConstraint, parse_type_constraint)
}

/// OCaml `parse_type_constraint` (res_core.ml:5793-5811). The location of
/// the type variable and of the constraint include the `constraint` keyword.
fn parse_type_constraint(p: &mut Parser<'_>) -> Option<(CoreTypeIdx, CoreTypeIdx, Location)> {
    if p.token != Token::Constraint {
        return None;
    }
    let cstr_start_idx = p.start_pos_idx();
    p.next();
    p.expect(Token::SingleQuote);
    match &p.token {
        Token::Lident(name) | Token::Uident(name) => {
            let name = extend_cow_lifetime(name.clone());
            let var_end_idx = p.end_pos_idx();
            p.next();
            let var = CoreType {
                ptyp_desc: CoreTypeDesc::Ptyp_var(p.arena_mut().intern(&name)),
                ptyp_loc: p.mk_loc_idx(cstr_start_idx, var_end_idx),
                ptyp_attributes: Attributes::new(),
            };
            p.expect(Token::Equal);
            let typ = typ::parse_typ_expr(p);
            let loc = p.mk_loc_idx_to_prev_end(cstr_start_idx);
            let var_idx = p.arena_mut().push_core_type(var);
            let typ_idx = p.arena_mut().push_core_type(typ);
            Some((var_idx, typ_idx, loc))
        }
        token => {
            p.err(DiagnosticCategory::Lident(token.clone().into_owned()));
            let loc = p.mk_loc_idx_to_prev_end(cstr_start_idx);
            let any = CoreType {
                ptyp_desc: CoreTypeDesc::Ptyp_any,
                ptyp_loc: LocIdx::none(),
                ptyp_attributes: Attributes::new(),
            };
            let typ = typ::parse_typ_expr(p);
            let any_idx = p.arena_mut().push_core_type(any);
            let typ_idx = p.arena_mut().push_core_type(typ);
            Some((any_idx, typ_idx, loc))
        }
    }
}

/// Parse a single with constraint.
fn parse_with_constraint(p: &mut Parser<'_>) -> Option<WithConstraint> {
    match &p.token {
        Token::Typ => {
            p.next();
            // OCaml res_core.ml:7238: `parse_value_path`.
            let lid = parse_value_path_lid(p);
            // Use the StrIdx directly from the longident to enable sharing
            let type_name_idx = p.arena().get_longident(lid.txt).last_idx();
            let type_loc = lid.loc;

            // OCaml `parse_type_params ~parent:type_constr` (res_core.ml:7239).
            let params = parse_type_params(p, |arena| {
                let parts: Vec<&str> = arena
                    .get_longident(lid.txt)
                    .flatten_idx()
                    .into_iter()
                    .map(|part| arena.get_string(part))
                    .collect();
                parts.join(".")
            });

            // res_core.ml:7240-7270.
            let (is_substitution, private, typ, type_constraints) = match p.token {
                Token::ColonEqual => {
                    p.next();
                    let typ = typ::parse_typ_expr(p);
                    (true, PrivateFlag::Public, typ, vec![])
                }
                Token::Equal => {
                    p.next();
                    let private = if p.token == Token::Private {
                        p.next();
                        PrivateFlag::Private
                    } else {
                        PrivateFlag::Public
                    };
                    let typ = typ::parse_typ_expr(p);
                    let cstrs = parse_type_constraints(p);
                    (false, private, typ, cstrs)
                }
                _ => {
                    // TODO in OCaml: revisit.
                    p.err_unexpected();
                    let typ = typ::parse_typ_expr(p);
                    let cstrs = parse_type_constraints(p);
                    (false, PrivateFlag::Public, typ, cstrs)
                }
            };

            let typ_idx = p.arena_mut().push_core_type(typ);
            let decl = TypeDeclaration {
                // OCaml uses the full longident location for the type name location
                ptype_name: with_loc(type_name_idx, type_loc),
                ptype_params: params,
                ptype_cstrs: type_constraints,
                ptype_kind: TypeKind::Ptype_abstract,
                ptype_private: private,
                ptype_manifest: Some(typ_idx),
                ptype_origin: TypeDeclarationOrigin::Declared,
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
            // res_core.ml:7219-7235.
            p.next();
            let lid = parse_module_long_ident(p);
            match p.token {
                Token::ColonEqual => {
                    p.next();
                    let lid2 = parse_module_long_ident(p);
                    Some(WithConstraint::Pwith_modsubst(lid, lid2))
                }
                Token::Equal => {
                    p.next();
                    let lid2 = parse_module_long_ident(p);
                    Some(WithConstraint::Pwith_module(lid, lid2))
                }
                _ => {
                    p.err_unexpected();
                    let lid2 = parse_module_long_ident(p);
                    Some(WithConstraint::Pwith_modsubst(lid, lid2))
                }
            }
        }
        _ => {
            // res_core.ml:7271-7276.
            p.err_unexpected();
            let lid_idx = p.push_lident("");
            let name_idx = p.arena_mut().intern("");
            let typ = super::core::recover::default_type(p.arena_mut());
            let typ_idx = p.arena_mut().push_core_type(typ);
            let decl = TypeDeclaration {
                ptype_name: with_loc(name_idx, LocIdx::none()),
                ptype_params: vec![],
                ptype_cstrs: vec![],
                ptype_kind: TypeKind::Ptype_abstract,
                ptype_private: PrivateFlag::Public,
                ptype_manifest: Some(typ_idx),
                ptype_origin: TypeDeclarationOrigin::Declared,
                ptype_attributes: Attributes::new(),
                ptype_loc: LocIdx::none(),
            };
            Some(WithConstraint::Pwith_type(
                with_loc(lid_idx, LocIdx::none()),
                decl,
            ))
        }
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Parse a module long identifier.
/// Handles both module paths (Foo.Bar.Baz) and module type paths (Foo.Bar.t).
/// Module type names are typically lowercase (e.g., RGLEvents.t).
pub(super) fn parse_module_long_ident(p: &mut Parser<'_>) -> Loc<LidentIdx> {
    parse_module_long_ident_with_lowercase(p, false)
}

pub(super) fn parse_module_type_long_ident(p: &mut Parser<'_>) -> Loc<LidentIdx> {
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
    let name_start = p.start_pos;

    // Recursive aux function that mirrors OCaml's aux in parse_value_path
    fn aux(p: &mut Parser<'_>, path_parts: &mut Vec<String>) {
        // Save current token info BEFORE advancing (like OCaml)
        let saved_token = p.token.clone();
        let saved_start = p.start_pos;
        let saved_end = p.end_pos;

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
        }
    }

    let mut path_parts = Vec::new();
    aux(p, &mut path_parts);

    // OCaml: Parser.next_unsafe p - consume one more token
    let name_end = p.prev_end_pos;
    p.next_unsafe();

    (path_parts, name_start, name_end)
}

/// OCaml `parse_value_path` (res_core.ml:742-776) as a located longident.
pub(super) fn parse_value_path_lid(p: &mut Parser<'_>) -> Loc<LidentIdx> {
    let (parts, loc) = parse_value_path(p);
    let lid_idx = super::core::build_longident_idx(p, &parts);
    with_loc(lid_idx, loc)
}

/// OCaml `parse_let_bindings` (compiler/syntax/src/res_core.ml:2790-2824), after
/// the `let`/`rec` tokens: the first binding, then one binding per `and`. The
/// attributes before each `and` are read by `parse_attributes_and_binding` in the
/// enclosing region, so a failed lookahead there silences that region.
/// OCaml `parse_let_bindings ~unwrap ~attrs ~start_pos`
/// (compiler/syntax/src/res_core.ml:2790-2830), including the optional `let`
/// and `rec` tokens.
pub(super) fn parse_let_bindings_item(
    p: &mut Parser<'_>,
    unwrap: bool,
    attrs: Attributes,
    start_pos_idx: PosIdx,
) -> (RecFlag, Vec<ValueBinding>) {
    p.optional(&Token::Let { unwrap });
    let rec_flag = if p.optional(&Token::Rec) {
        RecFlag::Recursive
    } else {
        RecFlag::Nonrecursive
    };
    let end_pos_idx = p.start_pos_idx();
    if rec_flag == RecFlag::Recursive && unwrap {
        let start = *p.arena().get_position(start_pos_idx);
        p.err_at(
            start,
            p.start_pos,
            DiagnosticCategory::Message(
                "let? is not allowed to be recursive. Use a regular `let` or remove `rec`."
                    .to_string(),
            ),
        );
    }
    let (bindings, _) = parse_let_bindings(p, start_pos_idx, end_pos_idx, rec_flag, attrs, unwrap);
    (rec_flag, bindings)
}

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
    let unwrap_attr: Attribute = (with_loc(name, loc), Payload::PStr(Box::default()));
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
                    ppat_desc: PatternDesc::Ppat_constraint(Box::new((pat_idx, typ_idx))),
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
    if let Some(value_constraint) = value_constraint {
        p.arena_mut()
            .set_value_constraint(pat_idx, value_constraint, expr_idx, vb_loc);
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
        ctx.outer_name_loc = name.loc;
    }

    // Convert name from Located<String> to Located<StrIdx> for ptype_name
    let name_str_idx = p.arena_mut().push_interned_string(&name.txt);
    let name: Located<StrIdx> = with_loc(name_str_idx, name.loc);

    // The type name path for inline record desugaring (using StrIdx)
    let current_type_name_path: Vec<StrIdx> = vec![name.txt];

    // Parse optional manifest and/or kind (and ReScript's `type t = T = ...` equation form).
    // OCaml: if token is Bar, call expect Equal to generate "Did you forget a `=` here?" error
    let (manifest, kind, private) =
        parse_type_equation_and_representation(p, inline_ctx, &current_type_name_path);

    let cstrs = parse_type_constraints(p);

    // Use decl_start_idx for the start position to enable sharing with structure_item
    let loc = p.mk_loc_idx_to_prev_end(decl_start_idx);
    Some(TypeDeclaration {
        ptype_name: name,
        ptype_params: params,
        ptype_cstrs: cstrs,
        ptype_kind: kind,
        ptype_private: private,
        ptype_manifest: manifest,
        ptype_origin: TypeDeclarationOrigin::Declared,
        ptype_attributes: attrs,
        ptype_loc: loc,
    })
}

type TypeEquation = (Option<CoreTypeIdx>, TypeKind, PrivateFlag);

/// OCaml `parse_type_equation_and_representation`
/// (compiler/syntax/src/res_core.ml:6320-6395).
fn parse_type_equation_and_representation(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: &Vec<StrIdx>,
) -> TypeEquation {
    if !matches!(p.token, Token::Equal | Token::Bar) {
        return (None, TypeKind::Ptype_abstract, PrivateFlag::Public);
    }
    if p.token == Token::Bar {
        p.expect(Token::Equal);
    }
    p.next();
    match p.token {
        Token::Uident(_) => parse_type_equation_or_constr_decl(p),
        Token::Lbrace => {
            parse_record_or_object_decl(p, inline_ctx, inline_ctx.map(|_| current_type_name_path))
        }
        Token::Private => parse_private_eq_or_repr(p),
        Token::Bar | Token::DotDot | Token::DocComment { .. } => {
            let (private, kind) = parse_type_representation(p, None, None);
            (None, kind, private)
        }
        Token::At => {
            // Look past the attributes (and doc comments): a representation-like
            // token means a representation, anything else a manifest.
            let is_representation_after_attrs = p.lookahead(|state| {
                parse_attributes(state);
                super::core::skip_doc_comments(state);
                match state.token {
                    Token::Lbrace => {
                        state.next();
                        parse_attributes(state);
                        super::core::skip_doc_comments(state);
                        !matches!(
                            state.token,
                            Token::String(_) | Token::Dot | Token::DotDot | Token::DotDotDot
                        )
                    }
                    Token::Bar | Token::DotDot | Token::DocComment { .. } => true,
                    Token::Uident(_) => {
                        state.next();
                        state.token != Token::Dot
                    }
                    _ => false,
                }
            });
            if is_representation_after_attrs {
                let (private, kind) = parse_type_representation(p, None, None);
                (None, kind, private)
            } else {
                parse_manifest_and_representation(p, inline_ctx, current_type_name_path)
            }
        }
        _ => parse_manifest_and_representation(p, inline_ctx, current_type_name_path),
    }
}

/// The manifest fallback of `parse_type_equation_and_representation`: a type
/// expression, optionally followed by `= representation`.
fn parse_manifest_and_representation(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: &Vec<StrIdx>,
) -> TypeEquation {
    let typ = typ::parse_typ_expr(p);
    let manifest = Some(p.arena_mut().push_core_type(typ));
    if p.token == Token::Equal {
        p.next();
        let (private, kind) =
            parse_type_representation(p, inline_ctx, Some(current_type_name_path));
        (manifest, kind, private)
    } else {
        (manifest, TypeKind::Ptype_abstract, PrivateFlag::Public)
    }
}

/// OCaml `parse_type_equation_or_constr_decl` (res_core.ml:5822-5874).
fn parse_type_equation_or_constr_decl(p: &mut Parser<'_>) -> TypeEquation {
    let is_type_path = p.lookahead(|state| {
        state.next();
        state.token == Token::Dot
    });
    if !is_type_path {
        return (
            None,
            TypeKind::Ptype_variant(parse_constructors_without_leading_bar(p)),
            PrivateFlag::Public,
        );
    }
    let uident_start_pos_idx = p.start_pos_idx();
    let Token::Uident(uident) = &p.token else {
        unreachable!("parse_type_equation_or_constr_decl: expected Uident");
    };
    let uident = uident.to_string();
    p.next();
    p.next();
    let typ = typ::parse_type_equation_constr(p, uident_start_pos_idx, uident);
    match p.token {
        Token::Equal => {
            p.next();
            let (private, kind) = parse_type_representation(p, None, None);
            (Some(p.arena_mut().push_core_type(typ)), kind, private)
        }
        Token::EqualGreater => {
            p.next();
            let return_type = typ::parse_typ_expr_no_alias(p);
            let loc = p.mk_loc_idx_to_prev_end(uident_start_pos_idx);
            let param_idx = p.arena_mut().push_core_type(typ);
            let ret_idx = p.arena_mut().push_core_type(return_type);
            let arrow = CoreType {
                ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((
                    Box::new(TypeArg {
                        attrs: Attributes::new(),
                        lbl: ArgLabel::Nolabel,
                        typ: param_idx,
                    }),
                    ret_idx,
                    p.static_arity_1(),
                ))),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            };
            let typ = typ::parse_type_alias(p, arrow);
            (
                Some(p.arena_mut().push_core_type(typ)),
                TypeKind::Ptype_abstract,
                PrivateFlag::Public,
            )
        }
        _ => (
            Some(p.arena_mut().push_core_type(typ)),
            TypeKind::Ptype_abstract,
            PrivateFlag::Public,
        ),
    }
}

/// OCaml `parse_private_eq_or_repr` (res_core.ml:6081-6097).
fn parse_private_eq_or_repr(p: &mut Parser<'_>) -> TypeEquation {
    p.expect(Token::Private);
    match p.token {
        Token::Lbrace => {
            let (manifest, kind, _) = parse_record_or_object_decl(p, None, None);
            (manifest, kind, PrivateFlag::Private)
        }
        Token::Uident(_) => {
            let (manifest, kind, _) = parse_type_equation_or_constr_decl(p);
            (manifest, kind, PrivateFlag::Private)
        }
        Token::Bar | Token::DotDot => {
            let (_, kind) = parse_type_representation(p, None, None);
            (None, kind, PrivateFlag::Private)
        }
        ref t if grammar::is_typ_expr_start(t) => {
            let typ = typ::parse_typ_expr(p);
            (
                Some(p.arena_mut().push_core_type(typ)),
                TypeKind::Ptype_abstract,
                PrivateFlag::Private,
            )
        }
        _ => {
            let (_, kind) = parse_type_representation(p, None, None);
            (None, kind, PrivateFlag::Private)
        }
    }
}

/// OCaml `parse_type_representation` (res_core.ml:5640-5692).
fn parse_type_representation(
    p: &mut Parser<'_>,
    inline_ctx: Option<&RefCell<InlineTypesContext>>,
    current_type_name_path: Option<&Vec<StrIdx>>,
) -> (PrivateFlag, TypeKind) {
    p.leave_breadcrumb(grammar::Grammar::TypeRepresentation);
    let private = if p.optional(&Token::Private) {
        PrivateFlag::Private
    } else {
        PrivateFlag::Public
    };
    let kind = match p.token {
        Token::Bar | Token::Uident(_) | Token::DocComment { .. } => {
            TypeKind::Ptype_variant(parse_constructors(p))
        }
        Token::At => {
            let after_attrs = p.lookahead(|state| {
                parse_attributes(state);
                super::core::skip_doc_comments(state);
                match state.token {
                    Token::Lbrace => 0u8,
                    Token::DotDot => 1,
                    _ => 2,
                }
            });
            match after_attrs {
                0 => {
                    parse_attributes(p);
                    super::core::skip_doc_comments(p);
                    TypeKind::Ptype_record(parse_record_declaration(
                        p,
                        inline_ctx,
                        current_type_name_path,
                    ))
                }
                1 => {
                    parse_attributes(p);
                    super::core::skip_doc_comments(p);
                    p.next();
                    TypeKind::Ptype_open
                }
                _ => TypeKind::Ptype_variant(parse_constructors(p)),
            }
        }
        Token::Lbrace => TypeKind::Ptype_record(parse_record_declaration(
            p,
            inline_ctx,
            current_type_name_path,
        )),
        Token::DotDot => {
            p.next();
            TypeKind::Ptype_open
        }
        _ => {
            p.err_unexpected();
            TypeKind::Ptype_variant(vec![])
        }
    };
    p.eat_breadcrumb();
    (private, kind)
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
            (CoreTypeDesc::Ptyp_var(p.arena_mut().intern(&ident)), loc)
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
            (CoreTypeDesc::Ptyp_var(p.arena_mut().intern(&ident)), loc)
        }
        _ => return None,
    };
    let typ = CoreType {
        ptyp_desc: desc,
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    };
    Some((p.arena_mut().push_core_type(typ), variance))
}

/// Parse variant constructors (starting with |).
fn parse_constructors(p: &mut Parser<'_>) -> Vec<ConstructorDeclaration> {
    // OCaml parse_type_constructor_declarations:
    // - First constructor: optional leading doc comment + optional leading `|`
    // - Remaining constructors: only if token is `|` or doc-comment-then-`|`
    let mut constructors = vec![];

    // First constructor: optional leading doc comment attribute.
    let first_doc_attrs = if let Token::DocComment { loc, content } = &p.token {
        let loc = *loc;
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

    parse_constructor_declarations_with_bar(p, &mut constructors);
    constructors
}

/// `parse_region ~grammar:Grammar.ConstructorDeclaration
/// ~f:parse_type_constructor_declaration_with_bar` (res_core.ml:5566-5627).
/// A `None` row always aborts the region: every non-`|` token terminates
/// `ConstructorDeclaration` lists.
fn parse_constructor_declarations_with_bar(
    p: &mut Parser<'_>,
    constructors: &mut Vec<ConstructorDeclaration>,
) {
    p.leave_breadcrumb(Grammar::ConstructorDeclaration);
    loop {
        if !is_bar_or_doc_comment_then_bar(p) {
            break;
        }

        let doc_attrs = if let Token::DocComment { loc, content } = &p.token {
            let loc = *loc;
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
    p.eat_breadcrumb();
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

/// The `Uident` constructor branch of OCaml `parse_type_equation_or_constr_decl`
/// (res_core.ml:5855-5871): the first constructor has no attributes and no
/// breadcrumb, then `parse_type_constructor_declarations ?first`.
fn parse_constructors_without_leading_bar(p: &mut Parser<'_>) -> Vec<ConstructorDeclaration> {
    let start_pos_idx = p.start_pos_idx();
    let Token::Uident(n) = &p.token else {
        unreachable!("parse_constructors_without_leading_bar: expected Uident");
    };
    let n = n.clone();
    let name_loc = p.mk_loc_current();
    p.next();
    let n_idx = p.arena_mut().push_interned_string(&n);
    let (args, res) = parse_constr_decl_args(p);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let first = crate::ast_helper_type::constructor(
        p.arena_mut(),
        loc,
        Attributes::new(),
        args,
        res,
        None,
        with_loc(n_idx, name_loc),
    );
    let mut constructors = vec![first];
    parse_constructor_declarations_with_bar(p, &mut constructors);
    constructors
}

/// Parse a single constructor with optional explicit start position.
fn parse_constructor_with_start(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
) -> Option<ConstructorDeclaration> {
    parse_constructor_impl(p, start_pos_idx)
}

/// OCaml `parse_type_constructor_declaration ~start_pos`
/// (compiler/syntax/src/res_core.ml:5586-5605). Like OCaml, the
/// `ConstructorDeclaration` breadcrumb is only eaten on the `Uident` path.
fn parse_constructor_impl(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
) -> Option<ConstructorDeclaration> {
    p.leave_breadcrumb(Grammar::ConstructorDeclaration);
    let attrs = parse_attributes(p);

    if p.token == Token::DotDotDot {
        p.next();
        let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let spread_type = typ::parse_poly_type_expr(p);
        let loc = p.mk_loc_idx_to_end_of(start_pos_idx, spread_type.ptyp_loc);
        let spread_type_idx = p.arena_mut().push_core_type(spread_type);
        let ellipsis_idx = p.arena_mut().intern("...");
        return Some(crate::ast_helper_type::constructor(
            p.arena_mut(),
            loc,
            attrs,
            ConstructorArguments::Pcstr_tuple(vec![spread_type_idx]),
            None,
            None,
            with_loc(ellipsis_idx, name_loc),
        ));
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
            let loc = p.none_loc();
            return Some(crate::ast_helper_type::constructor(
                p.arena_mut(),
                loc,
                Attributes::new(),
                ConstructorArguments::Pcstr_tuple(vec![]),
                None,
                None,
                mknoloc(error_idx),
            ));
        }
    };

    let (args, res) = parse_constr_decl_args(p);
    p.eat_breadcrumb();
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    Some(crate::ast_helper_type::constructor(
        p.arena_mut(),
        loc,
        attrs,
        args,
        res,
        None,
        name,
    ))
}

// ============================================================================
// Record declarations (OCaml res_core.ml:5186-5358, 5369-5558, 5876-6078)
// ============================================================================

type InlineCtx<'c> = Option<&'c RefCell<InlineTypesContext>>;

/// OCaml `extend_current_type_name_path`.
fn extend_type_name_path(path: Option<&Vec<StrIdx>>, name: StrIdx) -> Option<Vec<StrIdx>> {
    path.map(|path| {
        let mut extended = path.clone();
        extended.push(name);
        extended
    })
}

fn label_declaration(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
    name: Located<StrIdx>,
    mutable: MutableFlag,
    optional: bool,
    typ: CoreType,
    attrs: Attributes,
) -> LabelDeclaration {
    let loc = p.mk_loc_idx_to_end_of(start_pos_idx, typ.ptyp_loc);
    let typ_idx = p.arena_mut().push_core_type(typ);
    crate::ast_helper_type::field(
        p.arena_mut(),
        loc,
        attrs,
        mutable,
        optional,
        None,
        name,
        typ_idx,
    )
}

/// `Ast_helper.Typ.constr ~loc:name.loc ?attrs {name with txt = Lident name.txt} []`.
fn punned_field_type(p: &mut Parser<'_>, name: &Located<StrIdx>, attrs: Attributes) -> CoreType {
    let lid_idx = p.push_lident_from_idx(name.txt);
    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr((
            with_loc(lid_idx, name.loc),
            crate::parse_arena::ArenaList::EMPTY,
        )),
        ptyp_loc: name.loc,
        ptyp_attributes: attrs,
    }
}

fn mutable_flag(p: &mut Parser<'_>) -> MutableFlag {
    if p.optional(&Token::Mutable) {
        MutableFlag::Mutable
    } else {
        MutableFlag::Immutable
    }
}

/// OCaml `parse_field_declaration ?extra_attrs` (res_core.ml:5223-5260).
/// `extra_attrs` are the attributes of the first field, already consumed by
/// the caller.
fn parse_field_declaration(
    p: &mut Parser<'_>,
    ctx: InlineCtx<'_>,
    path: Option<&Vec<StrIdx>>,
    extra_attrs: Attributes,
) -> LabelDeclaration {
    let start_pos_idx = p.start_pos_idx();
    let mut attrs = extra_attrs;
    attrs.extend(parse_attributes(p).into_vec());
    let mutable = mutable_flag(p);
    let (lident, lident_loc) = super::core::parse_lident(p);
    let optional = p.optional(&Token::Question);
    let name_idx = p.arena_mut().push_interned_string(&lident);
    let name = with_loc(name_idx, lident_loc);
    let typ = match p.token {
        Token::Colon => {
            p.next();
            let path = extend_type_name_path(path, name_idx);
            parse_poly_type_with_inline_context(p, ctx, path.as_ref())
        }
        Token::Equal => {
            p.err(DiagnosticCategory::Message(
                error_messages::RECORD_TYPE_FIELD_MISSING_COLON.to_string(),
            ));
            p.next();
            let path = extend_type_name_path(path, name_idx);
            parse_poly_type_with_inline_context(p, ctx, path.as_ref())
        }
        _ => punned_field_type(p, &name, Attributes::new()),
    };
    label_declaration(p, start_pos_idx, name, mutable, optional, typ, attrs)
}

/// OCaml `parse_field_declaration_region ?found_object_field`
/// (res_core.ml:5262-5344).
fn parse_field_declaration_region(
    p: &mut Parser<'_>,
    ctx: InlineCtx<'_>,
    path: Option<&Vec<StrIdx>>,
    found_object_field: Option<&mut bool>,
) -> Option<LabelDeclaration> {
    let start_pos_idx = p.start_pos_idx();
    let start_pos = p.start_pos;
    let attrs = parse_attributes(p);
    let mutable = mutable_flag(p);
    match p.token {
        Token::DotDotDot => {
            p.next();
            let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let name_idx = p.arena_mut().intern("...");
            let typ = parse_poly_type_with_inline_context(p, None, None);
            Some(label_declaration(
                p,
                start_pos_idx,
                with_loc(name_idx, name_loc),
                mutable,
                false,
                typ,
                attrs,
            ))
        }
        Token::String(ref s) if found_object_field.is_some() => {
            let s = s.to_string();
            if let Some(found) = found_object_field {
                *found = true;
            }
            p.next();
            let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let name_idx = p.arena_mut().push_interned_string(&s);
            p.expect(Token::Colon);
            let typ = parse_poly_type_with_inline_context(p, None, None);
            Some(label_declaration(
                p,
                start_pos_idx,
                with_loc(name_idx, name_loc),
                mutable,
                false,
                typ,
                attrs,
            ))
        }
        Token::Lident(_) => {
            let (lident, lident_loc) = super::core::parse_lident(p);
            let name_idx = p.arena_mut().push_interned_string(&lident);
            let name = with_loc(name_idx, lident_loc);
            let path = extend_type_name_path(path, name_idx);
            let optional = p.optional(&Token::Question);
            let typ = match p.token {
                Token::Colon => {
                    p.next();
                    parse_poly_type_with_inline_context(p, ctx, path.as_ref())
                }
                Token::Equal => {
                    p.err(DiagnosticCategory::Message(
                        error_messages::RECORD_TYPE_FIELD_MISSING_COLON.to_string(),
                    ));
                    p.next();
                    parse_poly_type_with_inline_context(p, ctx, path.as_ref())
                }
                _ => punned_field_type(p, &name, attrs.clone()),
            };
            Some(label_declaration(
                p,
                start_pos_idx,
                name,
                mutable,
                optional,
                typ,
                attrs,
            ))
        }
        _ => {
            if p.token.is_keyword() {
                match super::core::recover_keyword_field_name_if_probably_field(
                    p,
                    error_messages::keyword_field_in_type,
                ) {
                    Some((recovered_field_name, name_loc)) => {
                        let optional = p.optional(&Token::Question);
                        p.expect(Token::Colon);
                        let typ = parse_poly_type_with_inline_context(p, ctx, path);
                        let name_idx = p.arena_mut().push_string(recovered_field_name);
                        Some(label_declaration(
                            p,
                            start_pos_idx,
                            with_loc(name_idx, name_loc),
                            mutable,
                            optional,
                            typ,
                            attrs,
                        ))
                    }
                    None => {
                        super::core::emit_keyword_field_error(
                            p,
                            error_messages::keyword_field_in_type,
                        );
                        None
                    }
                }
            } else {
                if !attrs.is_empty() {
                    p.err_at(
                        start_pos,
                        p.end_pos,
                        DiagnosticCategory::Message(
                            "Attributes and doc comments can only be used at the beginning of a field declaration".to_string(),
                        ),
                    );
                }
                if mutable == MutableFlag::Mutable {
                    p.err_at(
                        start_pos,
                        p.end_pos,
                        DiagnosticCategory::Message(
                            "The `mutable` qualifier can only be used at the beginning of a field declaration".to_string(),
                        ),
                    );
                }
                None
            }
        }
    }
}

/// OCaml `parse_record_declaration` (res_core.ml:5346-5358).
fn parse_record_declaration(
    p: &mut Parser<'_>,
    ctx: InlineCtx<'_>,
    path: Option<&Vec<StrIdx>>,
) -> Vec<LabelDeclaration> {
    p.leave_breadcrumb(grammar::Grammar::RecordDecl);
    p.expect(Token::Lbrace);
    let rows = super::core::parse_comma_delimited_region(
        p,
        grammar::Grammar::RecordDecl,
        Token::Rbrace,
        |p| parse_field_declaration_region(p, ctx, path, None),
    );
    p.expect(Token::Rbrace);
    p.eat_breadcrumb();
    rows
}

/// Parse the rows after `{` with OCaml `parse_field_declaration_region` in a
/// comma delimited region of `grammar`, reporting whether an object (string)
/// field was found.
fn parse_field_declarations_tracking_objects(
    p: &mut Parser<'_>,
    ctx: InlineCtx<'_>,
    path: Option<&Vec<StrIdx>>,
    grammar: grammar::Grammar,
) -> (Vec<LabelDeclaration>, bool) {
    let mut found_object_field = false;
    let fields = super::core::parse_comma_delimited_region(p, grammar, Token::Rbrace, |p| {
        parse_field_declaration_region(p, ctx, path, Some(&mut found_object_field))
    });
    (fields, found_object_field)
}

/// OCaml's conversion of spread-record fields into object fields when a string
/// field was found (res_core.ml:5896-5906, 5981-5986).
fn object_fields_of_labels(fields: Vec<LabelDeclaration>, p: &mut Parser<'_>) -> Vec<ObjectField> {
    fields
        .into_iter()
        .map(|ld| {
            if p.arena().get_string(ld.pld_name.txt) == "..." {
                ObjectField::Oinherit(ld.pld_type)
            } else {
                let attrs = crate::ast_helper_type::field_attributes_owned(p.arena_mut(), &ld);
                ObjectField::Otag(ld.pld_name, attrs, ld.pld_type)
            }
        })
        .collect()
}

fn object_type(fields: Vec<ObjectField>, closed: ClosedFlag, loc: LocIdx) -> CoreType {
    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_object(Box::new((fields, closed))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// `Ast_helper.Type.field ~loc {txt = "..."; loc = mk_loc dd_start dd_end} typ`.
fn spread_field(
    p: &mut Parser<'_>,
    loc: LocIdx,
    name_loc: LocIdx,
    typ: CoreTypeIdx,
) -> LabelDeclaration {
    let name_idx = p.arena_mut().intern("...");
    crate::ast_helper_type::field(
        p.arena_mut(),
        loc,
        Attributes::new(),
        MutableFlag::Immutable,
        false,
        None,
        with_loc(name_idx, name_loc),
        typ,
    )
}

/// Object fields after `{` and optional leading attributes on the first
/// field (res_core.ml:6000-6031, 5431-5460).
fn parse_string_field_declarations_with_attrs(
    p: &mut Parser<'_>,
    attrs: Attributes,
) -> Vec<ObjectField> {
    if attrs.is_empty() {
        return super::core::parse_comma_delimited_region(
            p,
            grammar::Grammar::StringFieldDeclarations,
            Token::Rbrace,
            typ::parse_string_field_declaration,
        );
    }
    p.leave_breadcrumb(grammar::Grammar::StringFieldDeclarations);
    let field = typ::parse_string_field_declaration(p)
        .expect("a string field declaration after attributes");
    match p.token {
        Token::Rbrace | Token::Eof => {}
        Token::Comma => p.next(),
        _ => p.expect(Token::Comma),
    }
    p.eat_breadcrumb();
    let first = match field {
        ObjectField::Otag(label, _, ct) => ObjectField::Otag(label, attrs, ct),
        ObjectField::Oinherit(ct) => ObjectField::Oinherit(ct),
    };
    let mut fields = vec![first];
    fields.extend(super::core::parse_comma_delimited_region(
        p,
        grammar::Grammar::StringFieldDeclarations,
        Token::Rbrace,
        typ::parse_string_field_declaration,
    ));
    fields
}

fn closed_flag_after_lbrace(p: &mut Parser<'_>) -> ClosedFlag {
    match p.token {
        Token::DotDot => {
            p.next();
            ClosedFlag::Open
        }
        Token::Dot => {
            p.next();
            ClosedFlag::Closed
        }
        _ => ClosedFlag::Closed,
    }
}

/// OCaml `parse_record_or_object_decl` (res_core.ml:5917-6078).
fn parse_record_or_object_decl(
    p: &mut Parser<'_>,
    ctx: InlineCtx<'_>,
    path: Option<&Vec<StrIdx>>,
) -> TypeEquation {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lbrace);
    match p.token {
        Token::DotDot | Token::Dot => {
            let closed = closed_flag_after_lbrace(p);
            let fields = super::core::parse_comma_delimited_region(
                p,
                grammar::Grammar::StringFieldDeclarations,
                Token::Rbrace,
                typ::parse_string_field_declaration,
            );
            p.expect(Token::Rbrace);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let typ = typ::parse_type_alias(p, object_type(fields, closed, loc));
            let typ = typ::parse_arrow_type_rest(p, typ, start_pos_idx);
            (
                Some(p.arena_mut().push_core_type(typ)),
                TypeKind::Ptype_abstract,
                PrivateFlag::Public,
            )
        }
        Token::DotDotDot => {
            let dotdotdot_start = p.start_pos_idx();
            let dotdotdot_end = p.end_pos_idx();
            p.next();
            let typ = typ::parse_typ_expr(p);
            let dot_name_loc = p.mk_loc_idx(dotdotdot_start, dotdotdot_end);
            if p.token == Token::Rbrace {
                p.next();
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let typ_idx = p.arena_mut().push_core_type(typ);
                let dot_field = spread_field(p, loc, dot_name_loc, typ_idx);
                return (
                    None,
                    TypeKind::Ptype_record(vec![dot_field]),
                    PrivateFlag::Public,
                );
            }
            p.expect(Token::Comma);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let typ_idx = p.arena_mut().push_core_type(typ);
            let dot_field = spread_field(p, loc, dot_name_loc, typ_idx);
            let (fields, found_object_field) = parse_field_declarations_tracking_objects(
                p,
                ctx,
                path,
                grammar::Grammar::RecordDecl,
            );
            p.expect(Token::Rbrace);
            if found_object_field {
                let mut obj_fields = vec![ObjectField::Oinherit(typ_idx)];
                obj_fields.extend(object_fields_of_labels(fields, p));
                let typ_obj = object_type(obj_fields, ClosedFlag::Closed, LocIdx::none());
                let typ_obj = typ::parse_type_alias(p, typ_obj);
                let typ_obj = typ::parse_arrow_type_rest(p, typ_obj, start_pos_idx);
                (
                    Some(p.arena_mut().push_core_type(typ_obj)),
                    TypeKind::Ptype_abstract,
                    PrivateFlag::Public,
                )
            } else {
                let mut all = vec![dot_field];
                all.extend(fields);
                (None, TypeKind::Ptype_record(all), PrivateFlag::Public)
            }
        }
        _ => {
            let attrs = parse_attributes(p);
            if matches!(p.token, Token::String(_)) {
                let fields = parse_string_field_declarations_with_attrs(p, attrs);
                p.expect(Token::Rbrace);
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let typ = typ::parse_type_alias(p, object_type(fields, ClosedFlag::Closed, loc));
                let typ = typ::parse_arrow_type_rest(p, typ, start_pos_idx);
                return (
                    Some(p.arena_mut().push_core_type(typ)),
                    TypeKind::Ptype_abstract,
                    PrivateFlag::Public,
                );
            }
            p.leave_breadcrumb(grammar::Grammar::RecordDecl);
            let fields = if attrs.is_empty() {
                super::core::parse_comma_delimited_region(
                    p,
                    grammar::Grammar::FieldDeclarations,
                    Token::Rbrace,
                    |p| parse_field_declaration_region(p, ctx, path, None),
                )
            } else {
                let first_attr_start = p.loc_start_idx(attrs.as_slice()[0].0.loc);
                let mut first = parse_field_declaration(p, ctx, path, attrs);
                p.optional(&Token::Comma);
                let field_loc_end = p.loc_end_idx(first.pld_loc);
                let field_loc_ghost = p.loc_ghost(first.pld_loc);
                first.pld_loc =
                    p.arena_mut()
                        .push_loc(first_attr_start, field_loc_end, field_loc_ghost);
                let mut fields = vec![first];
                fields.extend(super::core::parse_comma_delimited_region(
                    p,
                    grammar::Grammar::FieldDeclarations,
                    Token::Rbrace,
                    |p| parse_field_declaration_region(p, ctx, path, None),
                ));
                fields
            };
            p.expect(Token::Rbrace);
            p.eat_breadcrumb();
            (None, TypeKind::Ptype_record(fields), PrivateFlag::Public)
        }
    }
}

/// OCaml `parse_spread_tail_classified` (res_core.ml:5876-5915).
enum SpreadTail {
    Record(Vec<LabelDeclaration>),
    Object(CoreType),
}

fn parse_spread_tail_classified(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
    spread_typ: CoreTypeIdx,
    grammar: grammar::Grammar,
) -> SpreadTail {
    if p.token == Token::Rbrace {
        p.next();
        return SpreadTail::Record(vec![]);
    }
    p.expect(Token::Comma);
    let (fields, found_object_field) =
        parse_field_declarations_tracking_objects(p, None, None, grammar);
    p.expect(Token::Rbrace);
    if found_object_field {
        let mut obj_fields = vec![ObjectField::Oinherit(spread_typ)];
        obj_fields.extend(object_fields_of_labels(fields, p));
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let typ = typ::parse_type_alias(p, object_type(obj_fields, ClosedFlag::Closed, loc));
        SpreadTail::Object(typ::parse_arrow_type_rest(p, typ, start_pos_idx))
    } else {
        SpreadTail::Record(fields)
    }
}

/// The comma-delimited `TypExprList` after a constructor's first argument.
fn parse_more_constr_args(p: &mut Parser<'_>, first: CoreType) -> ConstructorArguments {
    p.optional(&Token::Comma);
    let more = super::core::parse_comma_delimited_region(
        p,
        grammar::Grammar::TypExprList,
        Token::Rparen,
        typ::parse_typ_expr_region,
    );
    p.expect(Token::Rparen);
    let mut args = vec![p.arena_mut().push_core_type(first)];
    args.extend(more.into_iter().map(|t| p.arena_mut().push_core_type(t)));
    ConstructorArguments::Pcstr_tuple(args)
}

/// OCaml `parse_constr_decl_args` (res_core.ml:5369-5545).
fn parse_constr_decl_args(p: &mut Parser<'_>) -> (ConstructorArguments, Option<CoreTypeIdx>) {
    let args = if p.token == Token::Lparen {
        p.next();
        if p.token == Token::Lbrace {
            p.next();
            let start_pos_idx = p.start_pos_idx();
            match p.token {
                Token::DotDot | Token::Dot => {
                    let closed = closed_flag_after_lbrace(p);
                    let fields = super::core::parse_comma_delimited_region(
                        p,
                        grammar::Grammar::StringFieldDeclarations,
                        Token::Rbrace,
                        typ::parse_string_field_declaration,
                    );
                    p.expect(Token::Rbrace);
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    parse_more_constr_args(p, object_type(fields, closed, loc))
                }
                Token::DotDotDot => {
                    let dotdotdot_start = p.start_pos_idx();
                    let dotdotdot_end = p.end_pos_idx();
                    p.next();
                    let spread_typ = typ::parse_typ_expr(p);
                    let spread_end = p.loc_end_idx(spread_typ.ptyp_loc);
                    let spread_typ_idx = p.arena_mut().push_core_type(spread_typ);
                    if p.token == Token::Rbrace {
                        p.next();
                        let name_loc = p.mk_loc_idx(dotdotdot_start, dotdotdot_end);
                        let loc = p.mk_loc_idx(start_pos_idx, spread_end);
                        let field = spread_field(p, loc, name_loc, spread_typ_idx);
                        p.optional(&Token::Comma);
                        p.expect(Token::Rparen);
                        ConstructorArguments::Pcstr_record(vec![field])
                    } else {
                        match parse_spread_tail_classified(
                            p,
                            start_pos_idx,
                            spread_typ_idx,
                            grammar::Grammar::FieldDeclarations,
                        ) {
                            SpreadTail::Record(fields) => {
                                let name_loc = p.mk_loc_idx(dotdotdot_start, dotdotdot_end);
                                let loc = p.mk_loc_idx(start_pos_idx, spread_end);
                                let field = spread_field(p, loc, name_loc, spread_typ_idx);
                                p.optional(&Token::Comma);
                                p.expect(Token::Rparen);
                                let mut all = vec![field];
                                all.extend(fields);
                                ConstructorArguments::Pcstr_record(all)
                            }
                            SpreadTail::Object(typ) => parse_more_constr_args(p, typ),
                        }
                    }
                }
                _ => {
                    let attrs = parse_attributes(p);
                    if matches!(p.token, Token::String(_)) {
                        let fields = parse_string_field_declarations_with_attrs(p, attrs);
                        p.expect(Token::Rbrace);
                        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                        let typ =
                            typ::parse_type_alias(p, object_type(fields, ClosedFlag::Closed, loc));
                        let typ = typ::parse_arrow_type_rest(p, typ, start_pos_idx);
                        parse_more_constr_args(p, typ)
                    } else {
                        let fields = if attrs.is_empty() {
                            super::core::parse_comma_delimited_region(
                                p,
                                grammar::Grammar::FieldDeclarations,
                                Token::Rbrace,
                                |p| parse_field_declaration_region(p, None, None, None),
                            )
                        } else {
                            let first = parse_field_declaration(p, None, None, attrs);
                            if p.token == Token::Rbrace {
                                vec![first]
                            } else {
                                p.expect(Token::Comma);
                                let mut fields = vec![first];
                                fields.extend(super::core::parse_comma_delimited_region(
                                    p,
                                    grammar::Grammar::FieldDeclarations,
                                    Token::Rbrace,
                                    |p| parse_field_declaration_region(p, None, None, None),
                                ));
                                fields
                            }
                        };
                        p.expect(Token::Rbrace);
                        p.optional(&Token::Comma);
                        p.expect(Token::Rparen);
                        ConstructorArguments::Pcstr_record(fields)
                    }
                }
            }
        } else {
            let args = super::core::parse_comma_delimited_region(
                p,
                grammar::Grammar::TypExprList,
                Token::Rparen,
                typ::parse_typ_expr_region,
            );
            p.expect(Token::Rparen);
            ConstructorArguments::Pcstr_tuple(
                args.into_iter()
                    .map(|t| p.arena_mut().push_core_type(t))
                    .collect(),
            )
        }
    } else {
        ConstructorArguments::Pcstr_tuple(vec![])
    };
    let res = if p.token == Token::Colon {
        p.next();
        let typ = typ::parse_typ_expr(p);
        Some(p.arena_mut().push_core_type(typ))
    } else {
        None
    };
    (args, res)
}

/// OCaml `parse_record_or_object_type`'s inline-record branch
/// (res_core.ml:4749-4756), called from `typ.rs` with the parser-state inline
/// context: `parse_comma_delimited_region ~grammar:RecordDecl ~closing:Rbrace
/// ~f:(parse_field_declaration_region ~current_type_name_path ~inline_types_context)`.
pub fn parse_label_declarations_for_inline(p: &mut Parser<'_>) -> Vec<LabelDeclaration> {
    let found = p.inline_types_found.take().unwrap_or_default();
    let inline_ctx = RefCell::new(InlineTypesContext {
        found_inline_types: found,
        params: p.inline_types_params.clone(),
        outer_name_loc: Location::none(),
    });
    let path_strings = p.current_type_name_path.clone();
    let path: Option<Vec<StrIdx>> =
        path_strings.map(|path| path.into_iter().map(|s| p.arena_mut().intern(&s)).collect());
    let labels = super::core::parse_comma_delimited_region(
        p,
        grammar::Grammar::RecordDecl,
        Token::Rbrace,
        |p| parse_field_declaration_region(p, Some(&inline_ctx), path.as_ref(), None),
    );
    let InlineTypesContext {
        found_inline_types,
        params,
        ..
    } = inline_ctx.into_inner();
    p.inline_types_found = Some(found_inline_types);
    p.inline_types_params = params;
    labels
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
        // Lend the context's state to the parser for the duration of the
        // call; every path that takes `inline_types_found` restores it.
        {
            let mut ctx = ctx.borrow_mut();
            p.inline_types_found = Some(std::mem::take(&mut ctx.found_inline_types));
            p.inline_types_params = std::mem::take(&mut ctx.params);
        }

        let typ = typ::parse_poly_type_expr(p);

        if let Some(found) = p.inline_types_found.take() {
            let mut ctx = ctx.borrow_mut();
            ctx.found_inline_types = found;
            ctx.params = std::mem::take(&mut p.inline_types_params);
        }

        // Restore old parser fields
        p.current_type_name_path = old_path;
        p.inline_types_found = old_found;
        p.inline_types_params = old_params;

        typ
    } else {
        // OCaml calls `parse_poly_type_expr` without `?current_type_name_path`
        // / `?inline_types_context` here, so no inline-record context applies.
        let old_path = p.current_type_name_path.take();
        let old_found = p.inline_types_found.take();
        let typ = typ::parse_poly_type_expr(p);
        p.current_type_name_path = old_path;
        p.inline_types_found = old_found;
        typ
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
    let equal_start = p.start_pos;
    let equal_end = p.end_pos;
    p.expect(Token::Equal);
    let prim = match &p.token {
        Token::String(s) => {
            let s = s.clone();
            p.next();
            Some(PrimitiveRepr::PrimName(
                p.arena_mut().push_interned_string(&s),
            ))
        }
        _ => {
            let msg = format!(
                "An external requires the name of the JS value you're referring to, like \"{}\".",
                name_text
            );
            p.err_at(equal_start, equal_end, DiagnosticCategory::Message(msg));
            None
        }
    };

    let loc = p.mk_loc_idx_to_prev_end(loc_start_idx);
    let vd = ValueDescription {
        pval_name: name,
        pval_type: typ,
        pval_prim: prim,
        pval_attributes: attrs,
        pval_loc: loc,
    };

    let inline_types = inline_types_found
        .into_iter()
        .map(|(inline_name_idx, loc, kind, params)| TypeDeclaration {
            ptype_name: with_loc(inline_name_idx, name.loc),
            ptype_params: params,
            ptype_cstrs: vec![],
            ptype_kind: kind,
            ptype_private: PrivateFlag::Public,
            ptype_manifest: None,
            ptype_origin: TypeDeclarationOrigin::Inline_record_definition,
            ptype_attributes: Attributes::new(),
            ptype_loc: loc,
        })
        .collect();

    p.eat_breadcrumb();
    (vd, inline_types)
}

/// OCaml `parse_sign_let_desc` (compiler/syntax/src/res_core.ml:7518-7526).
fn parse_sign_let_desc(p: &mut Parser<'_>, attrs: Attributes) -> ValueDescription {
    let start_pos_idx = p.start_pos_idx();
    p.optional(&Token::Let { unwrap: false });
    let (name, name_loc) = super::core::parse_lident(p);
    let name = with_loc(p.arena_mut().push_interned_string(&name), name_loc);
    p.expect(Token::Colon);
    let typ = typ::parse_poly_type_expr(p);
    let typ = p.arena_mut().push_core_type(typ);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    ValueDescription {
        pval_name: name,
        pval_type: typ,
        pval_prim: None,
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
    parse_attrs: bool,
) -> ExtensionConstructor {
    let start_pos_idx = exception_start.unwrap_or_else(|| p.start_pos_idx());
    let (def_attrs, name, kind) = parse_constr_def(p, parse_attrs);
    let mut all_attrs = attrs;
    all_attrs.extend(def_attrs);
    ExtensionConstructor {
        pext_name: name,
        pext_kind: kind,
        pext_loc: p.mk_loc_idx_to_prev_end(start_pos_idx),
        pext_attributes: all_attrs,
    }
}

/// OCaml `parse_constr_def ~parse_attrs` (compiler/syntax/src/res_core.ml:6590-6617).
fn parse_constr_def(
    p: &mut Parser<'_>,
    parse_attrs: bool,
) -> (Attributes, Located<StrIdx>, ExtensionConstructorKind) {
    let attrs = if parse_attrs {
        parse_attributes(p)
    } else {
        Attributes::new()
    };
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
            mknoloc(p.arena_mut().intern("_"))
        }
    };
    let kind = match p.token {
        Token::Lparen => {
            let (args, res) = parse_constr_decl_args(p);
            ExtensionConstructorKind::Pext_decl(args, res)
        }
        Token::Equal => {
            p.next();
            ExtensionConstructorKind::Pext_rebind(parse_module_long_ident(p))
        }
        Token::Colon => {
            p.next();
            let typ = typ::parse_typ_expr(p);
            let typ_idx = p.arena_mut().push_core_type(typ);
            ExtensionConstructorKind::Pext_decl(
                ConstructorArguments::Pcstr_tuple(vec![]),
                Some(typ_idx),
            )
        }
        _ => ExtensionConstructorKind::Pext_decl(ConstructorArguments::Pcstr_tuple(vec![]), None),
    };
    (attrs, name, kind)
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
        true,
    )];
    while p.token == Token::Bar {
        let start_idx = p.start_pos_idx();
        p.next();
        constructors.push(parse_extension_constructor(
            p,
            Attributes::new(),
            Some(start_idx),
            true,
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
        // Recursive-module initialization embeds the module's source
        // position (`Transl_recmodule.init_shape`); see `Parser::next`.
        if !p.arena().stores_locations() {
            p.arena().require_locations();
        }
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

    if rec_flag == RecFlag::Recursive {
        return Some(StructureItemDesc::Pstr_recmodule(Box::new(
            parse_module_bindings(p, attrs, start_pos_idx),
        )));
    }
    Some(StructureItemDesc::Pstr_module(Box::new(
        parse_module_binding(p, attrs, start_pos_idx),
    )))
}

/// OCaml `parse_module_binding` (compiler/syntax/src/res_core.ml:7046-7060).
fn parse_module_binding(
    p: &mut Parser<'_>,
    attrs: Attributes,
    start_pos_idx: PosIdx,
) -> ModuleBinding {
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
    let body = parse_module_binding_body(p);
    let mod_expr_idx = p.arena_mut().push_mod_expr(body);
    ModuleBinding {
        pmb_name: name,
        pmb_expr: mod_expr_idx,
        pmb_attributes: attrs,
        pmb_loc: p.mk_loc_idx_to_prev_end(start_pos_idx),
    }
}

/// OCaml `parse_module_binding_body` (compiler/syntax/src/res_core.ml:7062-7078).
pub(super) fn parse_module_binding_body(p: &mut Parser<'_>) -> ModuleExpr {
    let mod_type = if p.token == Token::Colon {
        p.next();
        Some(parse_module_type(p))
    } else {
        None
    };
    p.expect(Token::Equal);
    let mod_expr = parse_module_expr(p);
    match mod_type {
        Some(mod_type) => {
            let loc = p.mk_loc_spanning(mod_type.pmty_loc, mod_expr.pmod_loc);
            let mod_expr_idx = p.arena_mut().push_mod_expr(mod_expr);
            let mod_type_idx = p.arena_mut().push_mod_type(mod_type);
            ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_constraint(mod_expr_idx, mod_type_idx),
                pmod_loc: loc,
                pmod_attributes: Attributes::new(),
            }
        }
        None => mod_expr,
    }
}

/// OCaml `parse_module_bindings` (compiler/syntax/src/res_core.ml:7082-7103):
/// attributes (and one doc comment) are read before `and`, never after it.
fn parse_module_bindings(
    p: &mut Parser<'_>,
    attrs: Attributes,
    start_pos_idx: PosIdx,
) -> Vec<ModuleBinding> {
    let mut bindings = vec![parse_module_binding(p, attrs, start_pos_idx)];
    loop {
        let start_pos_idx = p.start_pos_idx();
        let doc_attr = if let Token::DocComment { loc, content } = &p.token {
            let loc = *loc;
            let content = content.clone();
            p.next();
            let loc = p.from_location(&loc);
            Some(super::core::doc_comment_to_attribute(
                p.arena_mut(),
                loc,
                content,
            ))
        } else {
            None
        };
        let mut attrs = Attributes::from_vec(doc_attr.into_iter().collect());
        attrs.extend(parse_attributes_and_binding(p).into_vec());
        if p.token != Token::And {
            return bindings;
        }
        p.next();
        p.optional(&Token::Module);
        bindings.push(parse_module_binding(p, attrs, start_pos_idx));
    }
}

/// OCaml `parse_module_declaration_or_alias` (compiler/syntax/src/res_core.ml:7459-7490).
fn parse_module_declaration(p: &mut Parser<'_>, attrs: Attributes) -> ModuleDeclaration {
    let start_pos_idx = p.start_pos_idx();
    let name = parse_module_declaration_name(p);
    let mod_type = match p.token {
        Token::Colon => {
            p.next();
            parse_module_type(p)
        }
        Token::Equal => {
            p.next();
            if p.token == Token::Lbrace {
                // Parse `module M = {` as `module M : {`.
                parse_module_type(p)
            } else {
                // `Ast_helper.Mty.alias` without `~loc`: the default location.
                let lid = parse_module_long_ident(p);
                ModuleType {
                    pmty_desc: ModuleTypeDesc::Pmty_alias(lid),
                    pmty_loc: Location::none(),
                    pmty_attributes: Attributes::new(),
                }
            }
        }
        _ => {
            p.err_unexpected();
            recover::default_module_type()
        }
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

fn parse_module_declaration_name(p: &mut Parser<'_>) -> Located<StrIdx> {
    match &p.token {
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
    }
}

/// OCaml `parse_rec_module_declaration` (compiler/syntax/src/res_core.ml:7444-7457).
fn parse_rec_module_declaration(
    p: &mut Parser<'_>,
    attrs: Attributes,
    start_pos_idx: PosIdx,
) -> ModuleDeclaration {
    let name = parse_module_declaration_name(p);
    p.expect(Token::Colon);
    let mod_type = parse_module_type(p);
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

/// OCaml `parse_rec_module_spec` (compiler/syntax/src/res_core.ml:7422-7441),
/// after `rec` has been consumed.
fn parse_rec_module_declarations(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    start_pos_idx: PosIdx,
) -> Vec<ModuleDeclaration> {
    let mut decls = vec![parse_rec_module_declaration(p, outer_attrs, start_pos_idx)];
    loop {
        let start_pos_idx = p.start_pos_idx();
        let attrs = parse_attributes_and_binding(p);
        if p.token != Token::And {
            return decls;
        }
        p.expect(Token::And);
        decls.push(parse_rec_module_declaration(p, attrs, start_pos_idx));
    }
}

/// Parse a module type declaration.
/// `in_structure` indicates whether this is in a structure (.res) or signature (.resi).
/// In structure context, OCaml passes ~loc, in signature context it doesn't (uses Location.none).
fn parse_module_type_declaration(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    in_structure: bool,
) -> ModuleTypeDeclaration {
    // OCaml `parse_module_type_impl` / `parse_module_type_declaration`
    // (res_core.ml:7007-7032, 7492-7516) read no attributes after `type`.
    let name_start_idx = p.start_pos_idx();
    let attrs = outer_attrs;

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
        p.expect(Token::Equal);
        let mt = parse_module_type(p);
        Some(p.arena_mut().push_mod_type(mt))
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
pub(super) fn parse_attributes(p: &mut Parser<'_>) -> Attributes {
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
                let loc_cloned = *loc;
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

    let payload = parse_payload_region(p);

    (attr_name, payload)
}

/// Parse an attribute payload.
/// Payloads can be:
/// - Structure items: `(expr1 expr2 ...)` - the default
/// - Type: `(: type)` - indicated by leading colon followed by type
/// - Signature: `(: signature_items)` - indicated by leading colon followed by signature items
/// - Pattern: `(? pattern)` or `(? pattern when guard)` - indicated by leading question mark
/// OCaml `parse_payload` (compiler/syntax/src/res_core.ml:7568-7612): an
/// adjacent `(` opens an `AttributePayload` region that ends at `)`;
/// anything else is an empty payload.
pub fn parse_payload_region(p: &mut Parser<'_>) -> Payload {
    if p.token == Token::Lparen && p.start_pos.cnum == p.prev_end_pos.cnum {
        p.leave_breadcrumb(Grammar::AttributePayload);
        p.next();
        let payload = parse_payload(p);
        p.expect(Token::Rparen);
        p.eat_breadcrumb();
        payload
    } else {
        Payload::PStr(Box::default())
    }
}

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

/// Name of the extension a macro quote hole `${expr}` is kept as.
pub const HOLE_EXTENSION: &str = "res.hole";

/// Name of the extension a splice hole `${...expr}` is kept as.
pub const SPLICE_HOLE_EXTENSION: &str = "res.hole.splice";

/// Whether the parser is at `${...`: the start of a splice hole.
pub(super) fn at_splice_hole(p: &mut Parser<'_>) -> bool {
    p.token == Token::DollarLbrace
        && p.lookahead(|p| {
            p.next();
            p.token == Token::DotDotDot
        })
}

/// `${expr}`: a hole in a macro quote (`%code(...)`, `%type(...)`,
/// `%pat(...)`). It is an extension node named [`HOLE_EXTENSION`] whose
/// payload is the expression, so no parsetree node kind is added.
///
/// `${...expr}` is a splice hole: it stands for the items of a list (the
/// arguments of a call, the fields of a record, the cases of a switch), and
/// is the extension [`SPLICE_HOLE_EXTENSION`].
pub(super) fn parse_hole_extension(p: &mut Parser<'_>) -> Extension {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::DollarLbrace);
    let splice = p.token == Token::DotDotDot;
    if splice {
        p.next();
    }
    let expr = super::expr::parse_expr(p);
    p.expect(Token::Rbrace);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let expr_loc = expr.pexp_loc;
    let expr_idx = p.arena_mut().push_expr(expr);
    let name = p.arena_mut().push_string(if splice {
        SPLICE_HOLE_EXTENSION
    } else {
        HOLE_EXTENSION
    });
    let item = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_eval(Box::new((expr_idx, Attributes::new()))),
        pstr_loc: expr_loc,
    };
    (with_loc(name, loc), Payload::PStr(Box::new(vec![item])))
}

/// The payload of the quotes `%type(...)` and `%pat(...)`, which hold a type
/// and a pattern where an extension payload is otherwise a structure.
pub(super) fn parse_quote_payload(p: &mut Parser<'_>, id: &StringLoc) -> Option<Payload> {
    if !(p.token == Token::Lparen && p.start_pos.cnum == p.prev_end_pos.cnum) {
        return None;
    }
    let quote_type = match p.arena().get_string(id.txt) {
        "type" => true,
        "pat" => false,
        _ => return None,
    };
    p.leave_breadcrumb(Grammar::AttributePayload);
    p.next();
    let payload = if quote_type {
        let typ = super::typ::parse_typ_expr(p);
        Payload::PTyp(p.arena_mut().push_core_type(typ))
    } else {
        let pat = super::pattern::parse_pattern(p);
        Payload::PPat(Box::new((p.arena_mut().push_pat(pat), None)))
    };
    p.expect(Token::Rparen);
    p.eat_breadcrumb();
    Some(payload)
}

/// The arguments of a macro where expressions are written,
/// `%Route.make("/users/:id", 3)`: the name is a module path, which no PPX
/// extension is. One argument is kept as that expression, several as a
/// tuple of them.
pub(super) fn parse_macro_arguments(p: &mut Parser<'_>, id: &StringLoc) -> Option<Payload> {
    if !(p.token == Token::Lparen && p.start_pos.cnum == p.prev_end_pos.cnum) {
        return None;
    }
    if !p
        .arena()
        .get_string(id.txt)
        .starts_with(|c: char| c.is_ascii_uppercase())
    {
        return None;
    }
    p.leave_breadcrumb(Grammar::AttributePayload);
    let start_pos_idx = p.start_pos_idx();
    p.next();
    let mut exprs = Vec::new();
    while p.token != Token::Rparen && p.token != Token::Eof {
        let expr = super::expr::parse_expr(p);
        exprs.push(expr);
        if p.token == Token::Comma {
            p.next();
        } else {
            break;
        }
    }
    p.expect(Token::Rparen);
    p.eat_breadcrumb();
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let expr = match exprs.len() {
        0 => return Some(Payload::PStr(Box::default())),
        1 => exprs.pop().expect("one argument"),
        _ => {
            let indices: Vec<_> = exprs
                .into_iter()
                .map(|expr| p.arena_mut().push_expr(expr))
                .collect();
            Expression {
                pexp_desc: ExpressionDesc::Pexp_tuple(p.arena_mut().push_expr_list(&indices)),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
    };
    let item_loc = expr.pexp_loc;
    let expr_idx = p.arena_mut().push_expr(expr);
    let item = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_eval(Box::new((expr_idx, Attributes::new()))),
        pstr_loc: item_loc,
    };
    Some(Payload::PStr(Box::new(vec![item])))
}

/// The arguments of a macro in a type position, `%Partial.t(user)`: the
/// name is a module path, which no PPX extension is, and the arguments are
/// types. One argument is kept as that type, several as a tuple of them.
pub(super) fn parse_macro_type_arguments(p: &mut Parser<'_>, id: &StringLoc) -> Option<Payload> {
    if !(p.token == Token::Lparen && p.start_pos.cnum == p.prev_end_pos.cnum) {
        return None;
    }
    if !p
        .arena()
        .get_string(id.txt)
        .starts_with(|c: char| c.is_ascii_uppercase())
    {
        return None;
    }
    p.leave_breadcrumb(Grammar::AttributePayload);
    let start_pos_idx = p.start_pos_idx();
    p.next();
    let mut types = Vec::new();
    while p.token != Token::Rparen && p.token != Token::Eof {
        let typ = super::typ::parse_typ_expr(p);
        types.push(p.arena_mut().push_core_type(typ));
        if p.token == Token::Comma {
            p.next();
        } else {
            break;
        }
    }
    p.expect(Token::Rparen);
    p.eat_breadcrumb();
    let payload = match types.as_slice() {
        [] => Payload::PStr(Box::default()),
        [single] => Payload::PTyp(*single),
        _ => {
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let tuple = CoreType {
                ptyp_desc: CoreTypeDesc::Ptyp_tuple(p.arena_mut().push_type_list(&types)),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            };
            Payload::PTyp(p.arena_mut().push_core_type(tuple))
        }
    };
    Some(payload)
}

/// OCaml `parse_extension ?(module_language = false)` (res_core.ml:7683-7689).
pub(super) fn parse_extension(p: &mut Parser<'_>, module_language: bool) -> Extension {
    // Capture start position BEFORE consuming % or %% so extension location includes it
    let id_start_idx = p.start_pos_idx();
    if module_language {
        p.expect(Token::PercentPercent);
    } else {
        p.expect(Token::Percent);
    }
    let id = parse_extension_id(p, id_start_idx);

    if let Some(payload) = parse_macro_arguments(p, &id) {
        return (id, payload);
    }
    let payload = parse_payload_region(p);
    let payload = raw_source_extension_payload(p, &id, payload);

    (id, payload)
}

/// The tail of OCaml `parse_extension` (res_core.ml): a `raw` or `ffi`
/// extension whose payload is a single string expression carries that
/// string's source spelling as JavaScript source.
pub(super) fn raw_source_extension_payload(
    p: &mut Parser<'_>,
    id: &StringLoc,
    payload: Payload,
) -> Payload {
    if p.arena().get_string(id.txt) == "re" {
        let start = p.loc_start(id.loc);
        let end = p.loc_end(id.loc);
        p.err_at(
            start,
            end,
            DiagnosticCategory::message(
                "The %re extension has been removed. Use a regexp literal such as /abc/i.",
            ),
        );
    }
    if !matches!(p.arena().get_string(id.txt), "raw" | "ffi") {
        return payload;
    }
    if let Payload::PStr(items) = &payload
        && let [item] = items.as_slice()
        && let StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc
    {
        let expr_idx = eval.0;
        if let ExpressionDesc::Pexp_constant(Constant::String(literal)) =
            p.arena().get_expr(expr_idx).pexp_desc
        {
            let source = match literal {
                StringConst::Valid { source, .. } | StringConst::InvalidSource(source) => source,
            };
            p.arena_mut().get_expr_mut(expr_idx).pexp_desc =
                ExpressionDesc::Pexp_constant(Constant::RawSource(source));
        }
    }
    payload
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
            structure[0].pstr_desc,
            StructureItemDesc::Pstr_value(_)
        ));
    }

    #[test]
    fn test_parse_open() {
        let structure = parse_with_timeout("open Belt");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            structure[0].pstr_desc,
            StructureItemDesc::Pstr_open(_)
        ));
    }

    #[test]
    fn test_parse_type_declaration() {
        let structure = parse_with_timeout("type t = int");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            structure[0].pstr_desc,
            StructureItemDesc::Pstr_type(_)
        ));
    }

    #[test]
    fn test_parse_variant_type() {
        let structure = parse_with_timeout("type color = | Red | Green | Blue");
        assert_eq!(structure.len(), 1);
        if let StructureItemDesc::Pstr_type(inner) = &structure[0].pstr_desc {
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
        if let StructureItemDesc::Pstr_type(inner) = &structure[0].pstr_desc {
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
            structure[0].pstr_desc,
            StructureItemDesc::Pstr_module(_)
        ));
    }

    #[test]
    fn test_parse_external() {
        let structure = parse_with_timeout("external log: string => unit = \"console.log\"");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            structure[0].pstr_desc,
            StructureItemDesc::Pstr_primitive(_)
        ));
    }

    #[test]
    fn test_parse_exception() {
        let structure = parse_with_timeout("exception MyError(string)");
        assert_eq!(structure.len(), 1);
        assert!(matches!(
            structure[0].pstr_desc,
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
