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
            p.expect(Token::Typ);

            // OCaml's parse_type_definition_or_extension:
            // 1. Parse rec/nonrec
            // 2. Call parse_value_path (which accepts Uident and consumes extra token)
            // 3. Parse type params
            // 4. Check for PlusEqual -> type extension or type declaration
            //
            // When the name starts with Uident, parse_value_path's next_unsafe
            // consumes an extra token (potentially = or +=), fundamentally changing
            // the parsing behavior. We replicate this for Uident names.

            // Check if name starts with Uident and the path does NOT end with
            // a lowercase ident. This detects error cases like `type T1 = D1` or
            // `type M.T2 += D2` where OCaml's parse_value_path quirk changes behavior.
            // Valid type extensions like `type Foo.Bar.t += ...` end with lident
            // and should use the normal path.
            let use_value_path_quirk = {
                let check_uident_path = |state: &mut crate::parser::state::Parser<'_>| {
                    if !matches!(state.token, Token::Uident(_)) {
                        return false;
                    }
                    // Walk the dotted path
                    loop {
                        match &state.token {
                            Token::Uident(_) => {
                                state.next();
                                if state.token == Token::Dot {
                                    state.next();
                                    continue;
                                }
                                // Path ended with Uident (no dot after) - this is the error case
                                return true;
                            }
                            Token::Lident(_) => {
                                // Path ends with lowercase - valid, use normal path
                                return false;
                            }
                            _ => {
                                // Something else - use value_path quirk
                                return true;
                            }
                        }
                    }
                };

                if p.token == Token::Rec || matches!(&p.token, Token::Lident(s) if s == "nonrec") {
                    p.lookahead(|state| {
                        state.next(); // consume rec/nonrec
                        check_uident_path(state)
                    })
                } else {
                    p.lookahead(check_uident_path)
                }
            };

            if use_value_path_quirk {
                // OCaml's parse_value_path + next_unsafe behavior for Uident names
                let rec_flag = if p.token == Token::Rec {
                    p.next();
                    RecFlag::Recursive
                } else if matches!(&p.token, Token::Lident(s) if s == "nonrec") {
                    p.next();
                    RecFlag::Nonrecursive
                } else {
                    RecFlag::Nonrecursive
                };

                let (path_parts, vp_name_start, _vp_name_end) = parse_value_path_for_type(p);
                let vp_name_start_idx = p.push_pos(vp_name_start.clone());

                // Parse type params (if any survive after parse_value_path consumed tokens)
                let params = if p.token == Token::LessThan {
                    parse_type_params_angle(p)
                } else {
                    vec![]
                };

                let result = if p.token == Token::PlusEqual {
                    // Type extension - build path and parse extension body
                    let lid_idx = super::core::build_longident_idx(p, &path_parts);
                    let path = with_loc(lid_idx, p.mk_loc_idx_to_prev_end(vp_name_start_idx));

                    p.expect(Token::PlusEqual);
                    let private = if p.token == Token::Private {
                        p.next();
                        PrivateFlag::Private
                    } else {
                        PrivateFlag::Public
                    };
                    let mut bar_start = if p.token == Token::Bar {
                        let pos_idx = p.start_pos_idx();
                        p.next();
                        Some(pos_idx)
                    } else {
                        None
                    };
                    let mut constructors = vec![];
                    while p.token != Token::Eof {
                        constructors.push(parse_extension_constructor(
                            p,
                            Attributes::new(),
                            bar_start,
                        ));
                        if p.token == Token::Bar {
                            bar_start = Some(p.start_pos_idx());
                            p.next();
                            continue;
                        }
                        break;
                    }

                    let ext = TypeExtension {
                        ptyext_path: path,
                        ptyext_params: params,
                        ptyext_constructors: constructors,
                        ptyext_private: private,
                        ptyext_attributes: attrs.clone(),
                    };
                    parse_newline_or_semicolon_structure(p);
                    Some(StructureItemDesc::Pstr_typext(Box::new(ext)))
                } else {
                    // Type declaration - check for module path errors
                    if path_parts.len() > 1 {
                        // Module path already has error from parse_value_path_for_type
                        // OCaml emits the module path error here
                        let last = path_parts.last().cloned().unwrap_or_default();
                        p.err_at(
                            vp_name_start.clone(),
                            p.prev_end_pos.clone(),
                            DiagnosticCategory::Message(format!(
                                "A type declaration's name cannot contain a module access. Did you mean `{}`?",
                                last
                            )),
                        );
                    }
                    // OCaml: parse_value_path already consumed = or +=,
                    // so parse_type_equation_and_representation sees whatever comes after.
                    // It won't match Equal or Bar, so it returns (None, Public, Ptype_abstract).
                    let last = path_parts
                        .last()
                        .cloned()
                        .unwrap_or_else(|| "_".to_string());
                    let name_loc = p.mk_loc_idx_to_prev_end(vp_name_start_idx);
                    let last_idx = p.arena_mut().push_string(last);
                    let name = with_loc(last_idx, name_loc);
                    let type_loc = p.mk_loc_idx_to_prev_end(type_start_idx);
                    let decl = TypeDeclaration {
                        ptype_name: name,
                        ptype_params: params,
                        ptype_cstrs: vec![],
                        ptype_kind: TypeKind::Ptype_abstract,
                        ptype_private: PrivateFlag::Public,
                        ptype_manifest: None,
                        ptype_attributes: attrs.clone(),
                        ptype_loc: type_loc,
                    };
                    parse_newline_or_semicolon_structure(p);
                    Some(StructureItemDesc::Pstr_type(Box::new((
                        rec_flag,
                        vec![decl],
                    ))))
                };

                p.end_region();
                result
            } else {
                // Normal case: name starts with Lident (or something else)
                // Use the original lookahead-based approach
                let is_type_extension = p.token != Token::Rec
                    && p.lookahead(|state| {
                        loop {
                            match &state.token {
                                Token::Lident(_) | Token::Uident(_) => {
                                    state.next();
                                    if state.token == Token::Dot {
                                        state.next();
                                        continue;
                                    }
                                }
                                _ => {}
                            }
                            break;
                        }
                        if state.token == Token::LessThan {
                            let mut depth = 1;
                            state.next();
                            while depth > 0 && state.token != Token::Eof {
                                match state.token {
                                    Token::LessThan => depth += 1,
                                    Token::GreaterThan => depth -= 1,
                                    _ => {}
                                }
                                state.next();
                            }
                        }
                        state.token == Token::PlusEqual
                    });

                let result = if is_type_extension {
                    let ext = parse_type_extension(p, attrs.clone());
                    parse_newline_or_semicolon_structure(p);
                    Some(StructureItemDesc::Pstr_typext(Box::new(ext)))
                } else {
                    let mut rec_flag = if p.token == Token::Rec {
                        p.next();
                        RecFlag::Recursive
                    } else if matches!(&p.token, Token::Lident(s) if s == "nonrec") {
                        p.next();
                        RecFlag::Nonrecursive
                    } else {
                        RecFlag::Nonrecursive
                    };
                    let (decls, has_inline_types) =
                        parse_type_declarations(p, attrs.clone(), type_start_idx);
                    if has_inline_types {
                        rec_flag = RecFlag::Recursive;
                    }
                    parse_newline_or_semicolon_structure(p);
                    Some(StructureItemDesc::Pstr_type(Box::new((rec_flag, decls))))
                };

                p.end_region();
                result
            }
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
            p.next();
            let is_type_extension = p.token != Token::Rec
                && p.lookahead(|state| {
                    loop {
                        match &state.token {
                            Token::Lident(_) | Token::Uident(_) => {
                                state.next();
                                if state.token == Token::Dot {
                                    state.next();
                                    continue;
                                }
                            }
                            _ => {}
                        }
                        break;
                    }

                    if state.token == Token::LessThan {
                        let mut depth = 1;
                        state.next();
                        while depth > 0 && state.token != Token::Eof {
                            match state.token {
                                Token::LessThan => depth += 1,
                                Token::GreaterThan => depth -= 1,
                                _ => {}
                            }
                            state.next();
                        }
                    }

                    state.token == Token::PlusEqual
                });

            let result = if is_type_extension {
                let ext = parse_type_extension(p, attrs.clone());
                parse_newline_or_semicolon_signature(p);
                Some(SignatureItemDesc::Psig_typext(Box::new(ext)))
            } else {
                let mut rec_flag = if p.token == Token::Rec {
                    p.next();
                    RecFlag::Recursive
                } else if matches!(&p.token, Token::Lident(s) if s == "nonrec") {
                    // Handle `type nonrec t = ...` - nonrec is a keyword in this context
                    p.next();
                    RecFlag::Nonrecursive
                } else {
                    RecFlag::Nonrecursive
                };
                let (decls, has_inline_types) =
                    parse_type_declarations(p, attrs.clone(), type_start_idx);
                // Inline record types require the type to be recursive
                if has_inline_types {
                    rec_flag = RecFlag::Recursive;
                }
                parse_newline_or_semicolon_signature(p);
                Some(SignatureItemDesc::Psig_type(Box::new((rec_flag, decls))))
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
    use super::core::recover::should_abort_list_parse;

    // OCaml uses parse_delimited_region ~grammar:Grammar.Structure ~closing:Rbrace
    // The Structure breadcrumb is needed so that error recovery (skip_tokens_and_maybe_retry)
    // knows that Rbrace is a list terminator and shouldn't be consumed
    p.leave_breadcrumb(Grammar::Structure);
    let mut items = vec![];

    while p.token != Token::Rbrace && p.token != Token::Eof {
        if let Some(item) = parse_structure_item(p) {
            items.push(item);
        } else if p.token == Token::Rbrace || p.token == Token::Eof || should_abort_list_parse(p) {
            break;
        } else {
            // OCaml compiler/syntax/src/res_core.ml:1194-1211 reports the
            // unexpected token from parse_delimited_region, then advances
            // exactly once before retrying.
            p.err_unexpected();
            p.next();
        }
    }

    p.eat_breadcrumb();
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

            // Parse type parameters if present (angle bracket syntax: <'a, 'b>)
            let params = if p.token == Token::LessThan {
                parse_type_params_angle(p)
            } else {
                vec![]
            };

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
fn parse_value_path_for_type(p: &mut Parser<'_>) -> (Vec<String>, Position, Position) {
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

/// Parse let bindings.
/// `start_pos_idx` should be the PosIdx BEFORE the `let` keyword for the first binding.
/// `let_end_pos_idx` should be the PosIdx AFTER the `let`/`let?` keyword (for let.unwrap attribute location).
/// Using PosIdx for start_pos enables position sharing with the structure_item location.
/// Returns (bindings, Option<LocIdx>) where LocIdx is Some only when there's exactly one binding
/// (to enable sharing with structure_item). For multiple bindings, returns None and the caller
/// should create a fresh location spanning all bindings.
fn parse_let_bindings(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
    let_end_pos_idx: PosIdx,
    _rec_flag: RecFlag,
    outer_attrs: Attributes,
    unwrap: bool,
) -> (Vec<ValueBinding>, Option<LocIdx>) {
    let mut bindings = vec![];
    // For the first binding, use the passed-in PosIdx to enable sharing
    let mut binding_start_idx = start_pos_idx;
    // Track the first binding's LocIdx for sharing with structure_item
    let mut first_binding_loc: Option<LocIdx> = None;
    // Track the location for let.unwrap attribute
    // For first binding: from start_pos to let_end_pos
    // For and bindings: captured at end of previous iteration when we see 'and'
    let mut unwrap_attr_start_idx = start_pos_idx;
    let mut unwrap_attr_end_idx = let_end_pos_idx;

    loop {
        // OCaml's parse_let_binding_body uses begin_region and leave_breadcrumb(LetBinding)
        // for each binding. This allows proper error messages and error de-duplication.
        p.begin_region();
        p.leave_breadcrumb(Grammar::LetBinding);

        let mut attrs = parse_attributes(p);

        // Handle `and` after attributes: `@attr and foo = ...`
        // We need to check for And here and capture its location for let.unwrap
        if p.token == Token::And {
            // Capture `and` keyword location for let.unwrap attribute
            unwrap_attr_start_idx = p.start_pos_idx();
            unwrap_attr_end_idx = p.end_pos_idx();
            p.next(); // consume `and`
        }

        // For the first binding, prepend the outer attributes
        if bindings.is_empty() {
            attrs = outer_attrs.clone().concat(attrs);
        }
        // Add let.unwrap attribute if this is let? (for all bindings, including `and` bindings)
        // OCaml uses: mk_loc start_pos end_pos (not ghost!)
        if unwrap {
            let unwrap_loc = p.mk_loc_idx(unwrap_attr_start_idx, unwrap_attr_end_idx);
            let unwrap_idx = p.arena_mut().intern("let.unwrap");
            attrs.push((
                with_loc(unwrap_idx, unwrap_loc),
                Payload::PStr(Box::new(vec![])),
            ));
        }

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

        let vb_loc = p.mk_loc_idx_to_prev_end(binding_start_idx);
        if first_binding_loc.is_none() {
            first_binding_loc = Some(vb_loc);
        }

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
        bindings.push(ValueBinding {
            pvb_pat: pat_idx,
            pvb_expr: expr_idx,
            pvb_attributes: attrs,
            pvb_loc: vb_loc,
        });

        // End the region and breadcrumb for this binding
        p.eat_breadcrumb();
        p.end_region();

        // Check for `and` to continue with more bindings.
        // Also handle attributes/doc comments before `and`: `@attr and ...` or `/** doc */ and ...`
        if p.token == Token::And {
            // Capture `and` keyword location for let.unwrap attribute in next binding
            // OCaml uses p.Parser.start_pos and p.Parser.end_pos (before consuming 'and')
            unwrap_attr_start_idx = p.start_pos_idx();
            unwrap_attr_end_idx = p.end_pos_idx();
            // Capture start position BEFORE consuming `and` for next binding
            // For `and` bindings, we push a fresh position (no sharing needed with structure_item)
            binding_start_idx = p.start_pos_idx();
            p.next();
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
            // Capture start position BEFORE the attributes for next binding
            binding_start_idx = p.start_pos_idx();
            // Continue - attributes will be parsed in the next iteration, and `and` will be consumed there
        } else {
            break;
        }
    }

    // Return bindings and optionally the LocIdx for sharing with structure_item.
    // Only share when there's exactly one binding - for multiple bindings, the structure_item
    // should span all bindings which is different from the first binding's location.
    if bindings.len() == 1 {
        (bindings, first_binding_loc)
    } else {
        (bindings, None)
    }
}

/// Parse type declarations. Returns the declarations and a flag indicating if inline types were found.
/// `type_keyword_start_idx` is the PosIdx of the `type` keyword for accurate location tracking
/// and position sharing with the structure item.
fn parse_type_declarations(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    type_keyword_start_idx: crate::parse_arena::PosIdx,
) -> (Vec<TypeDeclaration>, bool) {
    let mut decls = vec![];
    let mut next_attrs = outer_attrs;
    let mut has_inline_types = false;

    // Create shared context for inline record desugaring
    // Note: For simplicity, we create a new context for each type declaration
    // The OCaml parser shares the context across `and` chains, but the inline types
    // are processed per-declaration anyway.

    // Track start position (as PosIdx) for type declarations
    // First declaration uses type_keyword_start_idx, subsequent `and` declarations push a new PosIdx
    let mut decl_start_idx = type_keyword_start_idx;

    loop {
        // Create context for this declaration
        let inline_ctx = RefCell::new(InlineTypesContext::new(vec![], Location::none()));
        if let Some(decl) =
            parse_type_declaration_with_context(p, next_attrs, &inline_ctx, decl_start_idx)
        {
            // Collect inline types from the context
            let ctx = inline_ctx.borrow();
            if !ctx.found_inline_types.is_empty() {
                has_inline_types = true;
                // Create type declarations for inline types with @res.inlineRecordDefinition attribute
                let inline_str_idx = p.arena_mut().intern("res.inlineRecordDefinition");
                let inline_attr: Attribute =
                    (mknoloc(inline_str_idx), Payload::PStr(Box::new(vec![])));
                for (inline_name_idx, loc, type_kind, params) in ctx.found_inline_types.iter() {
                    // OCaml uses the outer type's name location for inline type ptype_name,
                    // not the inline type's location
                    let inline_decl = TypeDeclaration {
                        ptype_name: with_loc(*inline_name_idx, ctx.outer_name_loc.clone()),
                        ptype_params: params.clone(),
                        ptype_cstrs: vec![],
                        ptype_kind: type_kind.clone(),
                        ptype_private: PrivateFlag::Public,
                        ptype_manifest: None,
                        ptype_attributes: Attributes::from_vec(vec![inline_attr.clone()]),
                        ptype_loc: loc.clone(),
                    };
                    decls.push(inline_decl);
                }
            }
            decls.push(decl);
        }
        next_attrs = Attributes::new();

        // Check for `and` to continue with more type declarations.
        // Also handle attributes/doc comments before `and`: `/** doc */ and type t = ...`
        if p.token == Token::And {
            decl_start_idx = p.start_pos_idx(); // Capture 'and' position as PosIdx
            p.next();
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
            // Capture start position BEFORE parsing attributes/doc comments as PosIdx
            // OCaml does: let start_pos = p.Parser.start_pos in let attrs = parse_attributes_and_binding p in
            // So the location should include the doc comment
            decl_start_idx = p.start_pos_idx();
            // Parse the attributes/doc comments, then consume `and`
            next_attrs = parse_attributes(p);
            if p.token == Token::And {
                p.next();
            }
        } else {
            break;
        }
    }

    (decls, has_inline_types)
}

/// Parse a type extension: `type t += ...`.
fn parse_type_extension(p: &mut Parser<'_>, attrs: Attributes) -> TypeExtension {
    let start_pos_idx = p.start_pos_idx();

    // Parse the extended type path (e.g. t or M.t).
    // OCaml's parse_value_path expects the last segment to be lowercase.
    // If an Uident is seen without a following dot, emit Lident diagnostic.
    let mut parts: Vec<String> = vec![];
    let mut last_was_uident = false;
    let mut last_uident_name = String::new();
    let mut last_uident_start = p.start_pos.clone();
    let mut last_uident_end = p.end_pos.clone();
    loop {
        match &p.token {
            Token::Lident(name) => {
                parts.push(name.to_string());
                last_was_uident = false;
                p.next();
            }
            Token::Uident(name) => {
                last_uident_name = name.to_string();
                last_uident_start = p.start_pos.clone();
                last_uident_end = p.end_pos.clone();
                parts.push(name.to_string());
                last_was_uident = true;
                p.next();
            }
            _ => break,
        }
        if p.token == Token::Dot {
            last_was_uident = false; // After a dot, the Uident is fine (it's a module)
            p.next();
            continue;
        }
        break;
    }

    // If the last segment was an Uident (not followed by a dot), emit error
    if last_was_uident && !parts.is_empty() {
        p.err_at(
            last_uident_start,
            last_uident_end,
            DiagnosticCategory::Lident(Token::Uident(last_uident_name.into())),
        );
    }

    if parts.is_empty() {
        p.err(DiagnosticCategory::Message(
            "Expected type name for type extension".to_string(),
        ));
        parts.push("Error".to_string());
    }

    let lid_idx = super::core::build_longident_idx(p, &parts);
    let path = with_loc(lid_idx, p.mk_loc_idx_to_prev_end(start_pos_idx));

    // Optional type params: <'a, +'b, -'c>
    let params = if p.token == Token::LessThan {
        parse_type_params_angle(p)
    } else {
        vec![]
    };

    p.expect(Token::PlusEqual);

    let private = if p.token == Token::Private {
        p.next();
        PrivateFlag::Private
    } else {
        PrivateFlag::Public
    };

    // Constructors (with optional leading `|`).
    // OCaml includes the `|` in the constructor location
    let mut bar_start_idx = if p.token == Token::Bar {
        let pos_idx = p.start_pos_idx();
        p.next();
        Some(pos_idx)
    } else {
        None
    };

    let mut constructors = vec![];
    while p.token != Token::Eof {
        constructors.push(parse_extension_constructor(
            p,
            Attributes::new(),
            bar_start_idx,
        ));
        if p.token == Token::Bar {
            bar_start_idx = Some(p.start_pos_idx());
            p.next();
            continue;
        }
        break;
    }

    TypeExtension {
        ptyext_path: path,
        ptyext_params: params,
        ptyext_constructors: constructors,
        ptyext_private: private,
        ptyext_attributes: attrs,
    }
}

/// Parse a single type declaration with inline record desugaring context.
/// `decl_start_idx` is the PosIdx of the `type` or `and` keyword that starts this declaration,
/// enabling position sharing with the structure item.
fn parse_type_declaration_with_context(
    p: &mut Parser<'_>,
    outer_attrs: Attributes,
    inline_ctx: &RefCell<InlineTypesContext>,
    decl_start_idx: crate::parse_arena::PosIdx,
) -> Option<TypeDeclaration> {
    let inner_attrs = parse_attributes(p);
    // Prepend outer attributes to inner ones
    let attrs = outer_attrs.concat(inner_attrs);

    // Parse type name first (ReScript uses t<'a> not 'a t syntax)
    // OCaml's approach: parse a value_path first, then check if it's a simple Lident.
    // If it's a dotted path (Foo.bar), emit "A type declaration's name cannot contain a module access".
    // If it's just an Uident (T1), emit "Did you mean `t1` instead of `T1`?"
    let name = match &p.token {
        Token::Lident(n) => {
            let n = n.to_string();
            let loc = p.mk_loc_current();
            p.next();
            // Check for module path after the name (e.g., `foo.bar`)
            // Type declarations cannot have module paths - but we should parse them to give better errors
            if p.token == Token::Dot {
                // This is a dotted path like `foo.bar` - type names can't have module access
                let mut parts = vec![n.clone()];
                while p.token == Token::Dot {
                    p.next();
                    match &p.token {
                        Token::Lident(s) | Token::Uident(s) => {
                            parts.push(s.to_string());
                            p.next();
                        }
                        _ => break,
                    }
                }
                let last = parts.last().cloned().unwrap_or_default();
                p.err(DiagnosticCategory::Message(format!(
                    "A type declaration's name cannot contain a module access. Did you mean `{}`?",
                    last
                )));
                // Use the last part as the name for error recovery
                with_loc(last, loc)
            } else {
                with_loc(n, loc)
            }
        }
        Token::Uident(n) => {
            // Parse the full path to give a better error message
            let n = n.to_string();
            let name_start = p.start_pos.clone();
            let name_start_idx = p.start_pos_idx();
            p.next();
            let name_end_idx = p.prev_end_pos_idx();

            // Check for module path
            let is_dotted = p.token == Token::Dot;
            let mut last_name = n.clone();
            if is_dotted {
                while p.token == Token::Dot {
                    p.next();
                    match &p.token {
                        Token::Lident(s) | Token::Uident(s) => {
                            last_name = s.to_string();
                            p.next();
                        }
                        _ => break,
                    }
                }
            }

            let loc = p.mk_loc_idx(name_start_idx, name_end_idx);
            if is_dotted {
                // Dotted path like Foo.bar - type names can't have module access
                p.err_at(
                    name_start.clone(),
                    p.prev_end_pos.clone(),
                    DiagnosticCategory::Message(format!(
                        "A type declaration's name cannot contain a module access. Did you mean `{}`?",
                        last_name
                    )),
                );
            } else {
                // Just an uppercase name - suggest lowercase
                p.err_at(
                    name_start.clone(),
                    p.prev_end_pos.clone(),
                    DiagnosticCategory::Lident(Token::Uident(n.clone().into())),
                );
            }
            // Use lowercase version for error recovery
            let lower = last_name
                .chars()
                .next()
                .map(|c| c.to_lowercase().collect::<String>() + &last_name[1..])
                .unwrap_or(last_name);
            with_loc(lower, loc)
        }
        Token::Eof => {
            // EOF uses Unexpected diagnostic like OCaml's parse_lident
            p.err_unexpected();
            // OCaml: returns ("_", loc) for error recovery, creating a placeholder type
            let loc = p.mk_loc_idx_to_prev_end(decl_start_idx);
            with_loc("_".to_string(), loc)
        }
        _ => {
            // OCaml: parse_lident emits Lident diagnostic and returns ("_", loc)
            p.err(DiagnosticCategory::Lident(p.token.clone().into_owned()));
            // Try to recover - if there's something on the same line, skip it
            if p.token.is_keyword() && p.prev_end_pos.line == p.start_pos.line {
                p.next();
            }
            let loc = p.mk_loc_idx_to_prev_end(decl_start_idx);
            with_loc("_".to_string(), loc)
        }
    };

    // Parse type parameters after name (e.g., t<'a, 'b> or t<+'a, -'b>)
    let params = if p.token == Token::LessThan {
        parse_type_params_angle(p)
    } else if p.token == Token::Lparen {
        // Detect old OCaml-style type parameters: type t('a) = ...
        // Give a helpful error message about using angle brackets instead
        let paren_start = p.start_pos.clone();
        let params = parse_type_params_old_style(p, name.txt.clone());
        let paren_end = p.prev_end_pos.clone();

        // Emit helpful error about angle bracket syntax
        // Use err_at (not err_multiple) so the region is silenced after this error,
        // matching OCaml's behavior where only one error per region is reported.
        let suggested = format_type_with_angle_brackets(p, &name.txt, &params);
        p.err_at(
            paren_start,
            paren_end,
            DiagnosticCategory::Message(format!(
                "Type parameters require angle brackets:\n  {}",
                suggested
            )),
        );
        params
    } else {
        vec![]
    };

    // Store params and outer name location in context for inline type declarations
    {
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
            Token::Bar => {
                // Variant type starting with | (e.g., type t = | A | B)
                kind = parse_type_kind(p, None, None);
            }
            Token::Lbrace => {
                // Record type OR object type ({"x": int})
                if looks_like_object_type_after_lbrace(p) {
                    // Detect if this is a spread-first CLOSED object: `{...spread, fields}`
                    // (not `{.. ...spread}` or `{. ...spread}`)
                    // OCaml uses ghost location for this specific case
                    let is_spread_first = p.lookahead(|state| {
                        state.next(); // consume {
                        // Check if first token is DotDotDot (not Dot or DotDot)
                        state.token == Token::DotDotDot
                    });
                    let typ = typ::parse_typ_expr(p);
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    // Apply ghost location fix for spread-first closed objects
                    let typ_idx = fix_spread_first_object_manifest(p, typ_idx, is_spread_first).0;
                    manifest = Some(typ_idx);
                } else {
                    kind = parse_type_kind(p, Some(inline_ctx), Some(&current_type_name_path));
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
                                    Some(inline_ctx),
                                    Some(&current_type_name_path),
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
                    parse_type_kind(p, Some(inline_ctx), Some(&current_type_name_path))
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

/// Fix the location of a direct spread-first object type manifest.
/// ONLY applies to the outermost level when the type starts with `{...spread`
/// (not `{.. ...spread}` or `{. ...spread}` - those use real locations).
/// Also propagates ghost loc_start to alias wrappers.
///
/// Returns the fixed type and whether the fix was applied.
fn fix_spread_first_object_manifest(
    p: &mut Parser<'_>,
    typ_idx: CoreTypeIdx,
    is_spread_first: bool,
) -> (CoreTypeIdx, bool) {
    if !is_spread_first {
        return (typ_idx, false);
    }

    let typ = p.arena().get_core_type(typ_idx).clone();
    match *typ.ptyp_desc {
        CoreTypeDesc::Ptyp_object(inner) => {
            // Only for CLOSED objects where first field is Oinherit (spread)
            // Open objects (from {.. ...spread}) should NOT use ghost location
            let first_is_spread = inner
                .0
                .first()
                .map_or(false, |f| matches!(f, ObjectField::Oinherit(_)));
            if first_is_spread && inner.1 == ClosedFlag::Closed {
                let fixed = CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_object(inner)),
                    ptyp_loc: Location::none(),
                    ptyp_attributes: typ.ptyp_attributes,
                };
                (p.arena_mut().push_core_type(fixed), true)
            } else {
                let fixed = CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_object(inner)),
                    ptyp_loc: typ.ptyp_loc,
                    ptyp_attributes: typ.ptyp_attributes,
                };
                (p.arena_mut().push_core_type(fixed), false)
            }
        }
        CoreTypeDesc::Ptyp_alias(alias_inner) => {
            let (ct_idx, alias) = *alias_inner;
            // Recurse into inner type
            let (fixed_inner_idx, applied) = fix_spread_first_object_manifest(p, ct_idx, true);
            if applied {
                // OCaml uses inner type's loc_start for alias, so if inner is ghost, alias start is ghost too
                // Create a spanning location from fixed_inner start to typ end
                let fixed_inner = p.arena().get_core_type(fixed_inner_idx);
                let new_loc = p.mk_loc_spanning(fixed_inner.ptyp_loc, typ.ptyp_loc);
                let fixed = CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_alias(Box::new((
                        fixed_inner_idx,
                        alias,
                    )))),
                    ptyp_loc: new_loc,
                    ptyp_attributes: typ.ptyp_attributes,
                };
                (p.arena_mut().push_core_type(fixed), true)
            } else {
                let fixed = CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_alias(Box::new((
                        fixed_inner_idx,
                        alias,
                    )))),
                    ..typ
                };
                (p.arena_mut().push_core_type(fixed), false)
            }
        }
        CoreTypeDesc::Ptyp_arrow(arrow_inner) => {
            let (arg, ret_idx, arity) = *arrow_inner;
            let args = p.arena().nary_arrow_args(&arg, arity).into_owned();
            // Recurse into every argument when this is the direct manifest level.
            let mut fixed_args = args
                .into_iter()
                .map(|arg| {
                    let (typ, _) = fix_spread_first_object_manifest(p, arg.typ, true);
                    TypeArg { typ, ..arg }
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
            (p.arena_mut().push_core_type(fixed), false)
        }
        _ => (typ_idx, false),
    }
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

/// Parse type parameters in angle bracket syntax: <'a, +'b, -'c, _>
fn parse_type_params_angle(p: &mut Parser<'_>) -> Vec<(CoreTypeIdx, Variance)> {
    let mut params = vec![];

    if p.token != Token::LessThan {
        return params;
    }
    // Enter diamond mode to prevent >= from being tokenized as a single token
    p.set_diamond_mode();
    p.next(); // consume <

    while p.token != Token::GreaterThan && p.token != Token::Eof {
        let param_start_idx = p.start_pos_idx();

        // Parse optional variance: +, -, or nothing
        let variance = match &p.token {
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

        // Parse type variable: 'name or underscore _
        if p.token == Token::SingleQuote {
            p.next();
            match &p.token {
                Token::Lident(name) | Token::Uident(name) => {
                    let name = extend_cow_lifetime(name.clone());
                    let loc = p.mk_loc_current();
                    p.next();
                    let typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(name))),
                        ptyp_loc: loc,
                        ptyp_attributes: Attributes::new(),
                    };
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    params.push((typ_idx, variance));
                }
                t if t.is_keyword() => {
                    // Reserved keyword after singlequote: 'for, 'let, etc.
                    let keyword = format!("{}", t);
                    let keyword_start = p.start_pos;
                    let keyword_end = p.end_pos;
                    let keyword_start_idx = p.start_pos_idx();
                    let keyword_end_idx = p.end_pos_idx();
                    let loc = p.mk_loc_idx(keyword_start_idx, keyword_end_idx);
                    p.err_multiple(
                        keyword_start,
                        keyword_end,
                        DiagnosticCategory::Message(format!(
                            "`{}` is a reserved keyword. Keywords need to be escaped: \\\"{}\"",
                            keyword, keyword
                        )),
                    );
                    p.next();
                    // Still add a param for recovery
                    let typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(keyword)))),
                        ptyp_loc: loc,
                        ptyp_attributes: Attributes::new(),
                    };
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    params.push((typ_idx, variance));
                }
                Token::Underscore => {
                    // '_ is not valid - type param needs a name
                    // Report position at the underscore, not the quote
                    p.err_multiple(
                        p.start_pos.clone(),
                        p.start_pos.clone(),
                        DiagnosticCategory::Message(
                            "A type param consists of a singlequote followed by a name like `'a` or `'A`".to_string()
                        ),
                    );
                    p.next();
                    // Add placeholder for recovery - use empty string for type var
                    let typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Borrowed("")))),
                        ptyp_loc: p.mk_loc_idx_to_prev_end(param_start_idx),
                        ptyp_attributes: Attributes::new(),
                    };
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    params.push((typ_idx, variance));
                }
                _ => {
                    // Something else after singlequote (like '+ )
                    // Report position at the invalid token, not the quote
                    p.err_multiple(
                        p.start_pos.clone(),
                        p.start_pos.clone(),
                        DiagnosticCategory::Message(
                            "A type param consists of a singlequote followed by a name like `'a` or `'A`".to_string()
                        ),
                    );
                    // Skip to next comma or closing >
                    while p.token != Token::Comma
                        && p.token != Token::GreaterThan
                        && p.token != Token::Eof
                    {
                        p.next();
                    }
                    // Add placeholder for recovery - use empty string for type var
                    let typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Borrowed("")))),
                        ptyp_loc: p.mk_loc_idx_to_prev_end(param_start_idx),
                        ptyp_attributes: Attributes::new(),
                    };
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    params.push((typ_idx, variance));
                }
            }
        } else if p.token == Token::Underscore {
            // Anonymous/wildcard type parameter: _
            let loc = p.mk_loc_current();
            p.next();
            let typ = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            };
            let typ_idx = p.arena_mut().push_core_type(typ);
            params.push((typ_idx, variance));
        } else if let Token::Lident(name) | Token::Uident(name) = &p.token {
            // Missing singlequote: foo instead of 'foo
            let name = name.to_string();
            p.err(DiagnosticCategory::Message(format!(
                "Type params start with a singlequote: '{}",
                name
            )));
            let loc = p.mk_loc_current();
            p.next();
            // Add for recovery
            let typ = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(name)))),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            };
            let typ_idx = p.arena_mut().push_core_type(typ);
            params.push((typ_idx, variance));
        }

        if !p.optional(&Token::Comma) {
            break;
        }
    }

    p.expect(Token::GreaterThan);
    p.pop_diamond_mode();
    params
}

/// Parse old OCaml-style type parameters: ('a, 'b)
/// This is for error recovery - ReScript requires angle brackets.
fn parse_type_params_old_style(
    p: &mut Parser<'_>,
    _type_name: String,
) -> Vec<(CoreTypeIdx, Variance)> {
    let mut params = vec![];

    if p.token != Token::Lparen {
        return params;
    }
    p.next(); // consume (

    while p.token != Token::Rparen && p.token != Token::Eof {
        if p.token == Token::SingleQuote {
            p.next();
            match &p.token {
                Token::Lident(name) | Token::Uident(name) => {
                    let name = extend_cow_lifetime(name.clone());
                    let loc = p.mk_loc_current();
                    p.next();
                    let typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(name))),
                        ptyp_loc: loc,
                        ptyp_attributes: Attributes::new(),
                    };
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    params.push((typ_idx, Variance::Invariant));
                }
                t if t.is_keyword() => {
                    // Reserved keyword as type param (e.g., 'for)
                    let name = Cow::Owned(format!("{}", t));
                    let loc = p.mk_loc_current();
                    p.next();
                    let typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(name))),
                        ptyp_loc: loc,
                        ptyp_attributes: Attributes::new(),
                    };
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    params.push((typ_idx, Variance::Invariant));
                }
                _ => {
                    // Skip unknown token
                    p.next();
                }
            }
        } else {
            // Skip non-quote token
            p.next();
        }
        if !p.optional(&Token::Comma) {
            break;
        }
    }

    if p.token == Token::Rparen {
        p.next();
    }
    params
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
            .map(|(t, _)| match &*p.arena().get_core_type(*t).ptyp_desc {
                CoreTypeDesc::Ptyp_var(v) => format!("'{}", v),
                _ => "_".to_string(),
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
            let mut args = vec![];
            // OCaml's parse_constr_decl_args has special handling for object types
            // ONLY for the first argument: it captures start_pos AFTER consuming `{`,
            // so the object type location excludes the opening brace.
            // Subsequent arguments use parse_comma_delimited_region with normal parse_typ_expr.
            let mut is_first = true;
            while p.token != Token::Rparen && p.token != Token::Eof {
                let arg = if is_first && p.token == Token::Lbrace {
                    // Check if this is an object type (has ., .., ..., or string keys)
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
                        // Consume `{` and capture start_pos AFTER (like OCaml)
                        p.next();
                        let start_pos_idx = p.start_pos_idx();
                        typ::parse_object_type_body(p, start_pos_idx)
                    } else {
                        typ::parse_typ_expr(p)
                    }
                } else {
                    typ::parse_typ_expr(p)
                };
                let arg_idx = p.arena_mut().push_core_type(arg);
                args.push(arg_idx);
                is_first = false;
                if p.optional(&Token::Comma) {
                    continue;
                }
                if super::grammar::is_typ_expr_start(&p.token) || p.token == Token::LessThan {
                    continue;
                } else {
                    break;
                }
            }
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
    let inner_attrs = parse_attributes(p);
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
    let name_text = p.arena().get_string(name.txt).to_string();

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

    let prim = if p.token == Token::Equal {
        let equal_start = p.start_pos.clone();
        let equal_end = p.end_pos.clone();
        p.next();
        match &p.token {
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
        }
    } else {
        p.expect(Token::Equal);
        vec![]
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
    loop {
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
    Attributes::from_vec(attrs)
}

/// Parse an attribute body.
/// `start_pos_idx` should be the position BEFORE the `@` or `@@` token was consumed.
fn parse_attribute_body(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Attribute {
    let mut parts = vec![];

    // Parse attribute identifier
    loop {
        match &p.token {
            Token::Lident(name) | Token::Uident(name) => {
                parts.push(name.to_string());
                p.next();
            }
            // Attributes can use keyword-like identifiers (e.g. `@module`, `@as`).
            // Treat keywords as identifiers in this context.
            token if token.is_keyword() => {
                parts.push(token.to_string());
                p.next();
            }
            _ => break,
        }
        if p.token == Token::Dot {
            p.next();
        } else {
            break;
        }
    }

    let name = parts.join(".");
    let name_idx = p.arena_mut().push_string(name.to_string());
    let name_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

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

    (with_loc(name_idx, name_loc), payload)
}

/// Parse an attribute payload.
/// Payloads can be:
/// - Structure items: `(expr1 expr2 ...)` - the default
/// - Type: `(: type)` - indicated by leading colon followed by type
/// - Signature: `(: signature_items)` - indicated by leading colon followed by signature items
/// - Pattern: `(? pattern)` or `(? pattern when guard)` - indicated by leading question mark
pub fn parse_payload(p: &mut Parser<'_>) -> Payload {
    // Check for type or signature payload: (: ...)
    if p.token == Token::Colon {
        p.next();
        // Check if it's a signature payload (starts with let, type, etc.) or a type
        if matches!(
            p.token,
            Token::Let { .. }
                | Token::Typ
                | Token::Module
                | Token::External
                | Token::Open
                | Token::Include
                | Token::Exception
        ) {
            // Parse as signature
            let mut sig_items = vec![];
            while p.token != Token::Rparen && p.token != Token::Eof {
                if let Some(item) = parse_signature_item(p) {
                    sig_items.push(item);
                }
                p.optional(&Token::Semicolon);
            }
            return Payload::PSig(Box::new(sig_items));
        } else {
            // Parse as type
            let typ = super::typ::parse_typ_expr(p);
            let typ_idx = p.arena_mut().push_core_type(typ);
            return Payload::PTyp(typ_idx);
        }
    }

    // Check for pattern payload: (? pattern) or (? pattern when guard)
    if p.token == Token::Question {
        p.next();
        let pat = super::pattern::parse_pattern(p);
        let pat_idx = p.arena_mut().push_pat(pat);
        let guard = if p.token == Token::When {
            p.next();
            let guard_expr = super::expr::parse_expr(p);
            Some(p.arena_mut().push_expr(guard_expr))
        } else {
            None
        };
        return Payload::PPat(Box::new((pat_idx, guard)));
    }

    // Otherwise, parse as structure items
    let mut items = vec![];

    // If the payload is empty, return early
    if p.token == Token::Rparen || p.token == Token::Eof {
        return Payload::PStr(Box::new(items));
    }

    // Parse structure items
    loop {
        let start_pos_idx = p.start_pos_idx();

        // Check if this looks like a structure item (let, type, module, etc.)
        let is_structure_item = matches!(
            p.token,
            Token::Let { .. }
                | Token::Typ
                | Token::Module
                | Token::External
                | Token::Open
                | Token::Include
                | Token::Exception
                | Token::At
                | Token::AtAt
                | Token::Percent
                | Token::PercentPercent
                | Token::ModuleComment { .. }
        );

        if is_structure_item {
            // Parse as structure item
            if let Some(item) = parse_structure_item(p) {
                items.push(item);
            }
        } else {
            // Parse as expression
            let expr = super::expr::parse_expr(p);

            // OCaml: parse_newline_or_semicolon_structure consumes the semicolon
            // BEFORE computing the location, so structure item location includes the semicolon
            p.optional(&Token::Semicolon);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let expr_idx = p.arena_mut().push_expr(expr);

            items.push(StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((
                    expr_idx,
                    Attributes::new(),
                )))),
                pstr_loc: loc,
            });
        }

        // For non-expression items, check for more items
        // (Expression items already consumed the semicolon above)

        // Stop if we hit the closing paren or EOF
        if matches!(p.token, Token::Rparen | Token::Comma | Token::Eof) {
            break;
        }
    }

    Payload::PStr(Box::new(items))
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
