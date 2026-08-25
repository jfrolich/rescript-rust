//! Built-in PPX transformations.
//!
//! This module implements the built-in PPX transformations that OCaml applies
//! before writing binary AST files. The main transformations are:
//!
//! 1. **External FFI encoding**: For ReScript external declarations, encode
//!    FFI metadata into `pval_prim[1]` as a marshaled blob.
//!
//! 2. **Inline constants**: For `@inline let x = "foo"`, convert to an
//!    external with FFI inline encoding.
//!
//! This mirrors the transformations in:
//! - `compiler/frontend/ppx_entry.ml`
//! - `compiler/frontend/bs_builtin_ppx.ml`
//! - `compiler/frontend/ast_external.ml`

use std::{borrow::Cow, fmt};

use crate::diagnostics::{Warning, WarningConfig};
use crate::intern::StrIdx;
use crate::parse_arena::{
    CoreTypeIdx, ExprIdx, LidentIdx, LocIdx, Located, ModExprIdx, ModTypeIdx, ParseArena, PatIdx,
};
use crate::parser::ast::{
    self as current, ArgLabel, Attribute, Attributes, Case, Constant, ConstructorArguments,
    ConstructorDeclaration, CoreType, CoreTypeDesc, Expression, ExpressionDesc,
    ExpressionRecordField, ExtensionConstructor, ExtensionConstructorKind, FunParam,
    IncludeDeclaration,
    JsxContainerElement, JsxElement, JsxFragment, JsxProp, JsxUnaryElement, LabelDeclaration,
    ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeDesc, ObjectField, Pattern, PatternDesc,
    PatternRecordField, Payload, PexpApply, PexpFun, PrivateFlag, RecFlag, RowField, SignatureItem,
    SignatureItemDesc, StructureItem, StructureItemDesc, TypeArg, TypeDeclaration, TypeExtension,
    TypeKind, ValueBinding, ValueDescription, WithConstraint,
};
use crate::parser::longident::Longident;

use super::ffi_types::{
    Attr, Cst, Delim, ExternalModuleName, ExternalSpec, FfiType, ImportAttributes, Label,
    LabelNoname, LamConstant, ModuleBindName, ObjParam, Param, Params, PointerInfo, ReturnWrapper,
    encode_ffi_type,
};
use super::spice_ppx;

/// The list of attributes that indicate a ReScript external
const EXTERNAL_ATTRS: &[&str] = &[
    "get",
    "set",
    "get_index",
    "return",
    "obj",
    "variadic",
    "val",
    "module",
    "scope",
    "send",
    "new",
    "set_index",
    "taggedTemplate",
];

pub const ACCESSORS_VARIANT_RECORD_ARG_ERROR: &str = "@deriving(accessors) from a variant record argument is unsupported. Either define the record type separately from the variant type or use a positional argument.";
pub const AWAIT_NOT_ASYNC_CONTEXT_ERROR: &str = "Await on expression not in an async context";

#[derive(Debug, Clone)]
pub struct PpxWarning {
    pub loc: LocIdx,
    pub warning: Warning,
}

#[derive(Debug, Clone)]
pub struct WarningAttributeSpec {
    pub spec: String,
    pub as_error: bool,
}

#[derive(Debug, Clone)]
pub struct PpxError {
    loc: Option<LocIdx>,
    message: String,
    warnings: Vec<PpxWarning>,
}

impl PpxError {
    fn message(message: impl Into<String>) -> Self {
        Self {
            loc: None,
            message: message.into(),
            warnings: Vec::new(),
        }
    }

    fn at_loc(loc: LocIdx, message: impl Into<String>) -> Self {
        Self {
            loc: Some(loc),
            message: message.into(),
            warnings: Vec::new(),
        }
    }

    fn int_of_string_failure() -> Self {
        Self::message("Fatal error: exception Failure(\"int_of_string\")\n")
    }

    fn with_warning(mut self, loc: LocIdx, warning: Warning) -> Self {
        self.warnings.push(PpxWarning { loc, warning });
        self
    }

    pub fn loc(&self) -> Option<LocIdx> {
        self.loc
    }

    pub fn message_text(&self) -> &str {
        &self.message
    }

    pub fn warnings(&self) -> &[PpxWarning] {
        &self.warnings
    }
}

impl fmt::Display for PpxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for PpxError {}

pub type PpxResult<T> = Result<T, PpxError>;

/// Check if the first char of a string is special (OCaml FFI marker)
fn first_char_special(s: &str) -> bool {
    matches!(s.chars().next(), Some('#' | '?' | '%'))
}

/// Check if a string starts with the OCaml marshal magic number.
/// The marshal magic bytes are 0x84, 0x95, 0xA6, 0xBE. These are stored as
/// Latin-1 code points (U+0084, U+0095, U+00A6, U+00BE) in UTF-8 strings,
/// so we must compare against chars (not raw UTF-8 bytes).
fn starts_with_marshal_magic(s: &str) -> bool {
    let mut chars = s.chars();
    matches!(
        (chars.next(), chars.next(), chars.next(), chars.next()),
        (
            Some('\u{84}'),
            Some('\u{95}'),
            Some('\u{A6}'),
            Some('\u{BE}')
        )
    )
}

fn prim_str(arena: &mut ParseArena, s: impl Into<String>) -> StrIdx {
    arena.push_string(s.into())
}

/// Check if primitives need to be encoded as ReScript FFI
fn prims_to_be_encoded(pval_prim: &[StrIdx], arena: &ParseArena) -> bool {
    match pval_prim.first() {
        None => false, // shouldn't happen for externals
        Some(first) if first_char_special(arena.get_string(*first)) => false,
        Some(_) => {
            // Check if second string already has marshal magic
            match pval_prim.get(1) {
                Some(second) if starts_with_marshal_magic(arena.get_string(*second)) => false,
                _ => true,
            }
        }
    }
}

/// Check if an external declaration has ReScript FFI attributes
fn has_external_attrs(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _payload)| {
        let name = arena.get_string(attr_name.txt);
        EXTERNAL_ATTRS.iter().any(|&ext_attr| name == ext_attr)
    })
}

/// Check if a value description represents a ReScript external
pub fn is_rs_external(attrs: &[Attribute], pval_prim: &[StrIdx], arena: &ParseArena) -> bool {
    if pval_prim.is_empty() {
        return false;
    }
    has_external_attrs(attrs, arena) || prims_to_be_encoded(pval_prim, arena)
}

/// Check if attributes contain @obj
fn has_obj_attr(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _)| {
        let name = arena.get_string(attr_name.txt);
        name == "obj"
    })
}

/// Check if attributes contain @let.unwrap.
fn has_unwrap_attr(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs
        .iter()
        .any(|(attr_name, _)| arena.get_string(attr_name.txt) == "let.unwrap")
}

/// Conservative variable extraction used by OCaml's Ast_pat helper.
fn single_var_pattern_name_conservative(pat: &Pattern, arena: &ParseArena) -> Option<String> {
    match &*pat.ppat_desc {
        PatternDesc::Ppat_any => Some(String::new()),
        PatternDesc::Ppat_var(name) => Some(arena.get_string(name.txt).to_string()),
        PatternDesc::Ppat_alias(inner, alias_name) => {
            if single_var_pattern_name_conservative(arena.get_pat(*inner), arena).is_some() {
                Some(arena.get_string(alias_name.txt).to_string())
            } else {
                None
            }
        }
        PatternDesc::Ppat_constraint(inner) => {
            let (inner_pat, _) = &**inner;
            single_var_pattern_name_conservative(arena.get_pat(*inner_pat), arena)
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum LetUnwrapVariant {
    ResultOk,
    ResultError,
    OptionSome,
    OptionNone,
}

/// Classify supported let.unwrap binding patterns:
/// `Ok(_)`, `Error(_)`, `Some(_)`, `None`.
fn classify_let_unwrap_pattern(
    pat: &Pattern,
    arena: &ParseArena,
) -> Option<(LetUnwrapVariant, String)> {
    let PatternDesc::Ppat_construct(ctor_lid, payload) = &*pat.ppat_desc else {
        return None;
    };
    let Longident::Lident(ctor_name_idx) = arena.get_longident(ctor_lid.txt) else {
        return None;
    };
    let ctor_name = arena.get_string(*ctor_name_idx);

    let variant = match (ctor_name, payload.is_some()) {
        ("Ok", true) => LetUnwrapVariant::ResultOk,
        ("Error", true) => LetUnwrapVariant::ResultError,
        ("Some", true) => LetUnwrapVariant::OptionSome,
        ("None", false) => LetUnwrapVariant::OptionNone,
        _ => return None,
    };

    let var_name = payload
        .as_ref()
        .and_then(|inner| single_var_pattern_name_conservative(arena.get_pat(*inner), arena))
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| "x".to_string());

    Some((variant, var_name))
}

/// Result of classifying a JavaScript expression.
/// This mirrors OCaml's `Js_raw_info.exp` type.
#[derive(Debug, Clone, PartialEq)]
pub enum JsExpClassification {
    /// A function expression (regular or arrow)
    JsFunction { arity: usize, arrow: bool },
    /// A literal value (string, number, bool, null, undefined, object literal, array literal)
    JsLiteral { comment: Option<String> },
    /// Unknown expression type
    JsExpUnknown,
}

/// Result of classifying a JavaScript statement fragment.
/// This mirrors OCaml's `Js_raw_info.stmt` type.
#[derive(Debug, Clone, PartialEq)]
pub enum JsStmtClassification {
    /// A comment-only statement fragment.
    JsStmtComment,
    /// Unknown statement fragment.
    JsStmtUnknown,
}

/// Check if an OXC expression is an object literal (recursively).
/// This matches OCaml compiler/ml/classify_function.ml:25-38
/// `is_obj_literal`; Flow does not keep the extra parenthesized wrapper that
/// OXC reports for raw snippets such as `({})`.
fn is_obj_literal(expr: &oxc_ast::ast::Expression<'_>) -> bool {
    use oxc_ast::ast::Expression;
    match expr {
        Expression::Identifier(id) if id.name == "undefined" => true,
        Expression::StringLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::BigIntLiteral(_)
        | Expression::RegExpLiteral(_) => true,
        Expression::UnaryExpression(unary) => {
            use oxc_ast::ast::UnaryOperator;
            matches!(unary.operator, UnaryOperator::UnaryNegation)
                && is_obj_literal(&unary.argument)
        }
        Expression::ObjectExpression(obj) => obj.properties.iter().all(|prop| {
            use oxc_ast::ast::ObjectPropertyKind;
            match prop {
                ObjectPropertyKind::ObjectProperty(p) => is_obj_literal(&p.value),
                _ => false,
            }
        }),
        Expression::ArrayExpression(arr) => arr.elements.iter().all(|elem| {
            use oxc_ast::ast::ArrayExpressionElement;
            match elem {
                ArrayExpressionElement::SpreadElement(_) => false,
                ArrayExpressionElement::Elision(_) => true,
                _ => {
                    // Try to get the expression from the element
                    if let Some(expr) = elem.as_expression() {
                        is_obj_literal(expr)
                    } else {
                        false
                    }
                }
            }
        }),
        Expression::ParenthesizedExpression(paren) => is_obj_literal(&paren.expression),
        _ => false,
    }
}

fn extract_raw_js_literal_comment(s: &str) -> Option<String> {
    use oxc_allocator::Allocator;
    use oxc_ast::ast::CommentKind;
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    let allocator = Allocator::default();
    let parser_return = Parser::new(&allocator, s, SourceType::default()).parse();
    if !parser_return.errors.is_empty() {
        return None;
    }

    let mut leading_comments = parser_return
        .program
        .comments
        .iter()
        .copied()
        .filter(|comment| comment.is_leading());
    let comment = leading_comments.next()?;
    if leading_comments.next().is_some() {
        return None;
    }

    let comment_text = comment.content_span().source_text(s);
    Some(match comment.kind {
        CommentKind::Block => format!("/*{comment_text}*/"),
        CommentKind::Line => format!("//{comment_text}"),
    })
}

/// Classify a JavaScript expression string.
/// This mirrors OCaml's `classify_exp` function which uses the Flow parser.
/// We use OXC (Oxidation Compiler) for parsing.
///
/// Returns the classification of the expression.
pub fn classify_js_exp(s: &str) -> JsExpClassification {
    use oxc_allocator::Allocator;
    use oxc_ast::ast::Expression;
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    // Create allocator in its own scope to ensure proper cleanup
    let allocator = Allocator::default();
    let source_type = SourceType::default();

    // Try to parse the string as a JavaScript expression
    let parser_result = Parser::new(&allocator, s, source_type).parse_expression();

    let result = match parser_result {
        Ok(expr) => {
            match &expr {
                // Function expression: function(...) { ... }
                // OCaml only matches non-async, non-generator functions
                Expression::FunctionExpression(func) => {
                    if !func.r#async && !func.generator {
                        JsExpClassification::JsFunction {
                            arity: func.params.parameters_count(),
                            arrow: false,
                        }
                    } else {
                        JsExpClassification::JsExpUnknown
                    }
                }
                // Arrow function expression: (...) => ...
                // OCaml only matches non-async, non-generator arrow functions with no id
                Expression::ArrowFunctionExpression(arrow) => {
                    if !arrow.r#async {
                        JsExpClassification::JsFunction {
                            arity: arrow.params.parameters_count(),
                            arrow: true,
                        }
                    } else {
                        JsExpClassification::JsExpUnknown
                    }
                }
                // Literals
                Expression::StringLiteral(_)
                | Expression::BooleanLiteral(_)
                | Expression::NullLiteral(_)
                | Expression::NumericLiteral(_)
                | Expression::BigIntLiteral(_)
                | Expression::RegExpLiteral(_) => JsExpClassification::JsLiteral {
                    comment: extract_raw_js_literal_comment(s),
                },
                // undefined identifier
                Expression::Identifier(id) if id.name == "undefined" => {
                    JsExpClassification::JsLiteral { comment: None }
                }
                // Object/array literals (checked recursively)
                _ if is_obj_literal(&expr) => JsExpClassification::JsLiteral { comment: None },
                // Unknown
                _ => JsExpClassification::JsExpUnknown,
            }
        }
        Err(_) => JsExpClassification::JsExpUnknown,
    };

    // Explicitly drop allocator before returning (though this should happen anyway)
    drop(allocator);
    result
}

/// Classify a JavaScript statement fragment.
/// This mirrors OCaml's `Classify_function.classify_stmt`.
pub fn classify_js_stmt(s: &str) -> JsStmtClassification {
    use oxc_allocator::Allocator;
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    let allocator = Allocator::default();
    let source_type = SourceType::default();
    let parser_return = Parser::new(&allocator, s, source_type).parse();

    if parser_return.errors.is_empty() && parser_return.program.body.is_empty() {
        JsStmtClassification::JsStmtComment
    } else {
        JsStmtClassification::JsStmtUnknown
    }
}

fn classify_js_function_arity(s: &str) -> Option<usize> {
    match classify_js_exp(s) {
        JsExpClassification::JsFunction { arity, .. } => Some(arity),
        _ => None,
    }
}

fn classify_recovered_arrow_function_arity(code: &str) -> Option<usize> {
    let trimmed = code.trim();
    let arrow_pos = trimmed.find("=>")?;
    let after_arrow = trimmed.get(arrow_pos + 2..)?.trim();
    let completed = if after_arrow.is_empty() {
        format!("{trimmed} undefined")
    } else if after_arrow == "{" {
        format!("{trimmed}}}")
    } else {
        return None;
    };

    match classify_js_exp(&completed) {
        JsExpClassification::JsFunction { arity, arrow: true } => Some(arity),
        _ => None,
    }
}

fn js_expression_parse_fails(s: &str) -> bool {
    use oxc_allocator::Allocator;
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    let allocator = Allocator::default();
    let source_type = SourceType::default();
    Parser::new(&allocator, s, source_type)
        .parse_expression()
        .is_err()
}

/// Detect if a JavaScript string contains a function expression.
/// This mirrors `Ast_payload.raw_as_string_exp_exn` at
/// compiler/ml/ast_payload.ml:140-158: classify the parsed Flow expression,
/// then set `is_function` only when Classify_function.classify_exp sees a
/// function root at compiler/ml/classify_function.ml:45-66. The keyword
/// fallback is only for Flow/OXC recovery cases like `function`, not valid call
/// expressions such as `function () {} ()`.
fn is_js_function(s: &str) -> bool {
    classify_js_function_arity(s).is_some()
        || (js_expression_parse_fails(s) && starts_with_keyword(s, "function"))
        || classify_recovered_arrow_function_arity(s).is_some()
}

struct RawJsParseWarning {
    loc: LocIdx,
    message: String,
}

fn byte_offset_to_flow_position(code: &str, offset: usize) -> (i32, i32) {
    let capped_offset = offset.min(code.len());
    let mut line = 1;
    let mut line_start = 0;
    for (idx, byte) in code.as_bytes().iter().enumerate().take(capped_offset) {
        if *byte == b'\n' {
            line += 1;
            line_start = idx + 1;
        }
    }
    (line, capped_offset.saturating_sub(line_start) as i32)
}

// Mirrors compiler/ml/bs_flow_ast_utils.ml:offset_pos. Flow locations are
// relative to the JavaScript payload, then shifted onto the ReScript string loc.
fn flow_offset_position(
    base: crate::location::Position,
    line: i32,
    column: i32,
    first_line_offset: i32,
) -> crate::location::Position {
    if line == 1 {
        crate::location::Position {
            cnum: base.cnum + column + first_line_offset,
            ..base
        }
    } else {
        crate::location::Position {
            line: base.line + line - 1,
            cnum: base.bol + column,
            ..base
        }
    }
}

// Mirrors Ast_payload.raw_as_string_exp_exn's first Flow parser warning for
// expression payloads. OXC supplies the parse failure; this keeps OCaml's
// warning location shift and the common EOF wording used by Parse_error.PP.
fn raw_js_warning_loc(
    code: &str,
    payload_loc: LocIdx,
    start_offset: usize,
    end_offset: usize,
    first_line_offset: i32,
    arena: &mut ParseArena,
) -> LocIdx {
    let base = *arena.loc_start(payload_loc);
    let loc_ghost = arena.loc_ghost(payload_loc);
    let (start_line, start_column) = byte_offset_to_flow_position(code, start_offset);
    let (end_line, end_column) = byte_offset_to_flow_position(code, end_offset);
    let start = flow_offset_position(base, start_line, start_column, first_line_offset);
    let end = flow_offset_position(base, end_line, end_column, first_line_offset);
    let start_idx = arena.push_position(start);
    let end_idx = arena.push_position(end);
    arena.push_loc(start_idx, end_idx, loc_ghost)
}

fn flow_like_raw_js_parse_message(code: &str, oxc_message: &str, start_offset: usize) -> String {
    if oxc_message == "Unexpected token" && start_offset >= code.trim_end().len() {
        "Unexpected end of input".to_string()
    } else {
        oxc_message.to_string()
    }
}

fn is_js_regex_like_literal(s: &str) -> bool {
    let trimmed = s.trim_start();
    trimmed.starts_with('/') && !trimmed.starts_with("//") && !trimmed.starts_with("/*")
}

fn starts_with_keyword(code: &str, keyword: &str) -> bool {
    let trimmed = code.trim_start();
    let Some(after_keyword) = trimmed.strip_prefix(keyword) else {
        return false;
    };
    !after_keyword
        .chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '$')
}

fn js_identifier_end(code: &str, start: usize) -> usize {
    let mut end = start;
    for (offset, ch) in code[start..].char_indices() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '$' {
            end = start + offset + ch.len_utf8();
        } else {
            break;
        }
    }
    end
}

fn flow_like_function_expression_parse_warning(code: &str) -> Option<(String, usize, usize)> {
    let trimmed = code.trim_start();
    let leading = code.len() - trimmed.len();
    let after_function = trimmed.strip_prefix("function")?;
    if after_function
        .chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '$')
    {
        return None;
    }

    let function_end = leading + "function".len();
    let rest = code.get(function_end..)?;
    let rest_trimmed = rest.trim_start();
    let token_offset = function_end + rest.len() - rest_trimmed.len();

    match rest_trimmed.chars().next() {
        None => Some((
            "Unexpected end of input, expected an identifier".to_string(),
            code.len(),
            code.len(),
        )),
        Some('{') => Some((
            "Unexpected token `{`, expected an identifier".to_string(),
            token_offset,
            token_offset,
        )),
        Some('(') => {
            let close_offset = code[token_offset..]
                .find(')')
                .map(|idx| token_offset + idx)?;
            let after_close = code.get(close_offset + 1..)?;
            if after_close.trim().is_empty() {
                Some((
                    "Unexpected end of input, expected the token `{`".to_string(),
                    code.len(),
                    code.len(),
                ))
            } else {
                None
            }
        }
        Some(ch) if ch.is_ascii_alphabetic() || ch == '_' || ch == '$' => {
            let ident_end = js_identifier_end(code, token_offset);
            let after_ident = code.get(ident_end..)?;
            let after_ident_trimmed = after_ident.trim_start();
            let next_offset = ident_end + after_ident.len() - after_ident_trimmed.len();
            match after_ident_trimmed.chars().next() {
                None => Some((
                    "Unexpected end of input, expected the token `(`".to_string(),
                    code.len(),
                    code.len(),
                )),
                Some('{') => Some((
                    "Unexpected token `{`, expected the token `(`".to_string(),
                    next_offset,
                    next_offset,
                )),
                Some('(') => {
                    let close_offset =
                        code[next_offset..].find(')').map(|idx| next_offset + idx)?;
                    let after_close = code.get(close_offset + 1..)?;
                    if after_close.trim().is_empty() {
                        Some((
                            "Unexpected end of input, expected the token `{`".to_string(),
                            code.len(),
                            code.len(),
                        ))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn flow_like_raw_js_expression_parse_warning(
    code: &str,
    oxc_message: &str,
    start_offset: usize,
    end_offset: usize,
) -> (String, usize, usize) {
    if is_js_regex_like_literal(code) && oxc_message == "Unterminated regular expression" {
        let eof_offset = code.len();
        return (
            "Invalid regular expression: missing /".to_string(),
            eof_offset,
            eof_offset,
        );
    }

    if let Some(warning) = flow_like_function_expression_parse_warning(code) {
        return warning;
    }

    if oxc_message == "Unexpected token" {
        for keyword in ["const", "var", "if", "return"] {
            if starts_with_keyword(code, keyword) {
                return (
                    format!("Unexpected token `{keyword}`"),
                    start_offset,
                    end_offset,
                );
            }
        }

        if let Some((token_offset, '{')) = first_non_whitespace_after_keyword(code, "import") {
            return (
                "Unexpected token `{`, expected the token `(`".to_string(),
                token_offset,
                token_offset,
            );
        }
    }

    if oxc_message == "Expected `}` but found `EOF`" {
        return (
            "Unexpected end of input, expected the token `}`".to_string(),
            start_offset,
            end_offset,
        );
    }

    (
        flow_like_raw_js_parse_message(code, oxc_message, start_offset),
        start_offset,
        end_offset,
    )
}

fn first_non_whitespace_after_keyword(code: &str, keyword: &str) -> Option<(usize, char)> {
    let trimmed = code.trim_start();
    let leading = code.len() - trimmed.len();
    let after_keyword = trimmed.strip_prefix(keyword)?;
    if after_keyword
        .chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '$')
    {
        return None;
    }

    let after_keyword_offset = leading + keyword.len();
    let rest = code.get(after_keyword_offset..)?;
    let rest_trimmed = rest.trim_start();
    let token_offset = after_keyword_offset + rest.len() - rest_trimmed.len();
    let token = rest_trimmed.chars().next()?;
    Some((token_offset, token))
}

fn flow_like_raw_js_program_parse_warning(
    code: &str,
    oxc_message: &str,
    start_offset: usize,
    end_offset: usize,
) -> (String, usize, usize) {
    if is_js_regex_like_literal(code) && oxc_message == "Unterminated regular expression" {
        let eof_offset = code.len();
        return (
            "Invalid regular expression: missing /".to_string(),
            eof_offset,
            eof_offset,
        );
    }

    for keyword in ["let", "const", "var"] {
        if let Some((token_offset, '=')) = first_non_whitespace_after_keyword(code, keyword) {
            return (
                "Unexpected token `=`, expected an identifier".to_string(),
                token_offset,
                token_offset,
            );
        }
    }

    for keyword in ["class", "function"] {
        if let Some((token_offset, '{')) = first_non_whitespace_after_keyword(code, keyword) {
            return (
                "Unexpected token `{`, expected an identifier".to_string(),
                token_offset,
                token_offset,
            );
        }
    }

    if oxc_message == "A 'return' statement can only be used within a function body." {
        return (
            "Illegal return statement".to_string(),
            start_offset,
            end_offset,
        );
    }

    if oxc_message == "Expected `}` but found `EOF`" {
        return (
            "Unexpected end of input, expected the token `}`".to_string(),
            start_offset,
            end_offset,
        );
    }

    if oxc_message == "Unexpected token" {
        if start_offset >= code.trim_end().len() {
            return (
                "Unexpected end of input".to_string(),
                start_offset,
                end_offset,
            );
        }

        if let Some(token) = code.get(start_offset..).and_then(|s| s.chars().next()) {
            return (
                format!("Unexpected token `{token}`"),
                start_offset,
                end_offset,
            );
        }
    }

    (oxc_message.to_string(), start_offset, end_offset)
}

fn raw_js_expression_parse_warning(
    code: &str,
    payload_loc: LocIdx,
    first_line_offset: i32,
    arena: &mut ParseArena,
) -> Option<RawJsParseWarning> {
    use oxc_allocator::Allocator;
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    let allocator = Allocator::default();
    let parser_result = Parser::new(&allocator, code, SourceType::default()).parse_expression();
    let mut errors = match parser_result {
        Ok(_) => return None,
        Err(errors) => errors.into_iter(),
    };
    let first_error = errors.next()?;
    let first_label = first_error
        .labels
        .as_ref()
        .and_then(|labels| labels.first());
    let start_offset = first_label.map_or_else(|| code.len(), |label| label.offset());
    let end_offset = first_label.map_or(start_offset, |label| label.offset() + label.len());
    let (message, start_offset, end_offset) = flow_like_raw_js_expression_parse_warning(
        code,
        &first_error.to_string(),
        start_offset,
        end_offset,
    );
    let loc = raw_js_warning_loc(
        code,
        payload_loc,
        start_offset,
        end_offset,
        first_line_offset,
        arena,
    );

    Some(RawJsParseWarning { loc, message })
}

fn raw_js_program_parse_warning(
    code: &str,
    payload_loc: LocIdx,
    first_line_offset: i32,
    arena: &mut ParseArena,
) -> Option<RawJsParseWarning> {
    use oxc_allocator::Allocator;
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    let allocator = Allocator::default();
    let parser_return = Parser::new(&allocator, code, SourceType::default()).parse();
    let first_error = parser_return.errors.into_iter().next()?;
    let first_label = first_error
        .labels
        .as_ref()
        .and_then(|labels| labels.first());
    let start_offset = first_label.map_or_else(|| code.len(), |label| label.offset());
    let end_offset = first_label.map_or(start_offset, |label| label.offset() + label.len());
    let (message, start_offset, end_offset) = flow_like_raw_js_program_parse_warning(
        code,
        &first_error.to_string(),
        start_offset,
        end_offset,
    );
    let loc = raw_js_warning_loc(
        code,
        payload_loc,
        start_offset,
        end_offset,
        first_line_offset,
        arena,
    );

    Some(RawJsParseWarning { loc, message })
}

fn push_raw_js_expression_warning(
    payload: &Payload,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let payload_info = payload_single_string_literal_info(payload, arena)
        .map(|(code, loc, offset)| (code.to_string(), loc, offset));
    if let Some((code, loc, offset)) = payload_info {
        if let Some(warning) = raw_js_expression_parse_warning(&code, loc, offset, arena) {
            warnings.push(PpxWarning {
                loc: warning.loc,
                warning: Warning::BsFfiWarning {
                    message: warning.message,
                },
            });
        }
    }
}

fn push_raw_re_warning(payload: &Payload, arena: &mut ParseArena, warnings: &mut Vec<PpxWarning>) {
    let payload_info = payload_single_string_literal_info(payload, arena)
        .map(|(code, loc, offset)| (code.to_string(), loc, offset));
    if let Some((code, loc, offset)) = payload_info {
        if is_js_regex_like_literal(&code) {
            if let Some(warning) = raw_js_expression_parse_warning(&code, loc, offset, arena) {
                warnings.push(PpxWarning {
                    loc: warning.loc,
                    warning: Warning::BsFfiWarning {
                        message: warning.message,
                    },
                });
            }
        }
    }
}

fn push_ffi_function_warning(
    payload: &Payload,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let payload_info = payload_single_string_literal_info(payload, arena)
        .map(|(code, loc, offset)| (code.to_string(), loc, offset));
    if let Some((code, loc, offset)) = payload_info {
        if is_js_function(&code) {
            if let Some(warning) = raw_js_expression_parse_warning(&code, loc, offset, arena) {
                warnings.push(PpxWarning {
                    loc: warning.loc,
                    warning: Warning::BsFfiWarning {
                        message: warning.message,
                    },
                });
            }
        }
    }
}

fn push_raw_js_program_warning(
    payload: &Payload,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let payload_info = payload_single_string_literal_info(payload, arena)
        .map(|(code, loc, offset)| (code.to_string(), loc, offset));
    if let Some((code, loc, offset)) = payload_info {
        if let Some(warning) = raw_js_program_parse_warning(&code, loc, offset, arena) {
            warnings.push(PpxWarning {
                loc: warning.loc,
                warning: Warning::BsFfiWarning {
                    message: warning.message,
                },
            });
        }
    }
}

fn collect_raw_js_warnings_from_expr_idx(
    expr_idx: ExprIdx,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let expr = arena.get_expr(expr_idx).clone();
    collect_raw_js_warnings_from_expr(&expr, arena, warnings);
}

fn collect_raw_js_warnings_from_mod_expr_idx(
    mod_expr_idx: ModExprIdx,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let mod_expr = arena.get_mod_expr(mod_expr_idx).clone();
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => {
            collect_raw_js_warnings_from_structure(items, arena, warnings)
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_name, _mty, body) = &**inner;
            collect_raw_js_warnings_from_mod_expr_idx(*body, arena, warnings);
        }
        ModuleExprDesc::Pmod_apply(left, right) => {
            collect_raw_js_warnings_from_mod_expr_idx(*left, arena, warnings);
            collect_raw_js_warnings_from_mod_expr_idx(*right, arena, warnings);
        }
        ModuleExprDesc::Pmod_constraint(inner, _mty) => {
            collect_raw_js_warnings_from_mod_expr_idx(*inner, arena, warnings);
        }
        ModuleExprDesc::Pmod_unpack(expr) => {
            collect_raw_js_warnings_from_expr_idx(*expr, arena, warnings);
        }
        _ => {}
    }
}

fn collect_raw_js_warnings_from_structure_item(
    item: &StructureItem,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    match &*item.pstr_desc {
        StructureItemDesc::Pstr_primitive(vd) => {
            collect_obj_optional_as_warnings(vd, arena, warnings);
            collect_external_string_redundant_warnings(vd, arena, warnings);
        }
        StructureItemDesc::Pstr_eval(inner) => {
            let (expr, attrs) = &**inner;
            collect_unused_bs_attributes(attrs, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*expr, arena, warnings);
        }
        StructureItemDesc::Pstr_value(inner) => {
            let (_rec, bindings) = &**inner;
            for binding in bindings {
                collect_raw_js_warnings_from_value_binding(binding, arena, warnings);
            }
        }
        StructureItemDesc::Pstr_type(inner) => {
            let (_rec_flag, tdcls) = &**inner;
            collect_deriving_not_applicable_warnings(
                tdcls,
                arena,
                warnings,
                DerivingExpansionContext::StructureItem,
            );
        }
        StructureItemDesc::Pstr_module(mb) => {
            collect_raw_js_warnings_from_mod_expr_idx(mb.pmb_expr, arena, warnings);
        }
        StructureItemDesc::Pstr_recmodule(bindings) => {
            for binding in bindings.iter() {
                collect_raw_js_warnings_from_mod_expr_idx(binding.pmb_expr, arena, warnings);
            }
        }
        StructureItemDesc::Pstr_include(include_decl) => {
            collect_raw_js_warnings_from_mod_expr_idx(include_decl.pincl_mod, arena, warnings);
        }
        StructureItemDesc::Pstr_extension(inner) => {
            let (extension, attrs) = &**inner;
            collect_unused_bs_attributes(attrs, arena, warnings);
            let (ext_name, payload) = extension;
            let name = arena.get_string(ext_name.txt);
            if name == "raw" {
                push_raw_js_program_warning(payload, arena, warnings);
            } else if name == "private" {
                if let Payload::PStr(items) = payload {
                    collect_raw_js_warnings_from_structure(items, arena, warnings);
                }
            }
        }
        _ => {}
    }
}

fn warning_spec_parse_ok(spec: &str, errflag: bool) -> bool {
    let mut config = WarningConfig::new();
    if errflag {
        config.parse_as_error(spec).is_ok()
    } else {
        config.parse(spec).is_ok()
    }
}

fn collect_builtin_warning_attribute(
    attr: &Attribute,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let (name, payload) = attr;
    let attr_name = arena.get_string(name.txt);
    match attr_name {
        "warning" | "ocaml.warning" | "warnerror" | "ocaml.warnerror" => {
            let errflag = matches!(attr_name, "warnerror" | "ocaml.warnerror");
            if let Some(spec) = payload_single_string_literal(payload, arena) {
                if !warning_spec_parse_ok(spec, errflag) {
                    warnings.push(PpxWarning {
                        loc: name.loc,
                        warning: Warning::AttributePayload {
                            attr: attr_name.to_string(),
                            message: "Ill-formed list of warnings".to_string(),
                        },
                    });
                }
            } else {
                warnings.push(PpxWarning {
                    loc: name.loc,
                    warning: Warning::AttributePayload {
                        attr: attr_name.to_string(),
                        message: "A single string literal is expected".to_string(),
                    },
                });
            }
        }
        "ppwarning" | "ocaml.ppwarning" => {
            if let Some((message, loc)) = payload_single_string_literal_with_loc(payload, arena) {
                warnings.push(PpxWarning {
                    loc,
                    warning: Warning::Preprocessor {
                        message: message.to_string(),
                    },
                });
            }
        }
        _ => {}
    }
}

fn builtin_warning_attribute_spec(
    attr: &Attribute,
    arena: &ParseArena,
) -> Option<WarningAttributeSpec> {
    let (name, payload) = attr;
    let attr_name = arena.get_string(name.txt);
    match attr_name {
        "warning" | "ocaml.warning" | "warnerror" | "ocaml.warnerror" => {
            let spec = payload_single_string_literal(payload, arena)?;
            Some(WarningAttributeSpec {
                spec: spec.to_string(),
                as_error: matches!(attr_name, "warnerror" | "ocaml.warnerror"),
            })
        }
        _ => None,
    }
}

/// Mirrors `Bs_ast_invariant.iter_warnings_on_stru`: only leading floating
/// structure attributes are checked before frontend rewriting.
pub fn collect_leading_builtin_warning_attributes(
    structure: &[StructureItem],
    arena: &ParseArena,
) -> Vec<PpxWarning> {
    let mut warnings = Vec::new();
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_attribute(attr) => {
                collect_builtin_warning_attribute(attr, arena, &mut warnings);
            }
            _ => break,
        }
    }
    warnings
}

/// Mirrors `Bs_ast_invariant.iter_warnings_on_stru` at
/// compiler/frontend/bs_ast_invariant.ml:151-158: leading `@@warning` and
/// `@@warnerror` attributes update the warning state before frontend rewriting.
pub fn collect_leading_builtin_warning_attribute_specs(
    structure: &[StructureItem],
    arena: &ParseArena,
) -> Vec<WarningAttributeSpec> {
    let mut specs = Vec::new();
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_attribute(attr) => {
                if let Some(spec) = builtin_warning_attribute_spec(attr, arena) {
                    specs.push(spec);
                }
            }
            _ => break,
        }
    }
    specs
}

/// Mirrors `Bs_ast_invariant.iter_warnings_on_sigi` at
/// compiler/frontend/bs_ast_invariant.ml:160-167 for interface files.
pub fn collect_leading_builtin_warning_signature_attributes(
    signature: &[SignatureItem],
    arena: &ParseArena,
) -> Vec<PpxWarning> {
    let mut warnings = Vec::new();
    for item in signature {
        match &*item.psig_desc {
            SignatureItemDesc::Psig_attribute(attr) => {
                collect_builtin_warning_attribute(attr, arena, &mut warnings);
            }
            _ => break,
        }
    }
    warnings
}

/// Mirrors `Bs_ast_invariant.iter_warnings_on_sigi` for interface files.
pub fn collect_leading_builtin_warning_signature_attribute_specs(
    signature: &[SignatureItem],
    arena: &ParseArena,
) -> Vec<WarningAttributeSpec> {
    let mut specs = Vec::new();
    for item in signature {
        match &*item.psig_desc {
            SignatureItemDesc::Psig_attribute(attr) => {
                if let Some(spec) = builtin_warning_attribute_spec(attr, arena) {
                    specs.push(spec);
                }
            }
            _ => break,
        }
    }
    specs
}

fn attr_named(attrs: &[Attribute], name: &str, arena: &ParseArena) -> bool {
    attrs
        .iter()
        .any(|(attr_name, _)| arena.get_string(attr_name.txt) == name)
}

fn is_bs_unused_attribute_candidate(name: &str) -> bool {
    matches!(
        name,
        "as" | "config" | "ignore" | "int" | "optional" | "string" | "unwrap"
    )
}

fn collect_unused_bs_attributes_from_slice(
    attrs: &[Attribute],
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    for (attr_name, _) in attrs {
        let name = arena.get_string(attr_name.txt);
        if is_bs_unused_attribute_candidate(name) && !arena.loc_ghost(attr_name.loc) {
            warnings.push(PpxWarning {
                loc: attr_name.loc,
                warning: Warning::BsUnusedAttribute {
                    name: name.to_string(),
                },
            });
        }
    }
}

fn collect_unused_bs_attributes(
    attrs: &Attributes,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    collect_unused_bs_attributes_from_slice(attrs.as_slice(), arena, warnings);
}

fn collect_unused_bs_attributes_from_core_type_idx(
    typ_idx: CoreTypeIdx,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let typ = arena.get_core_type(typ_idx);
    collect_unused_bs_attributes_from_core_type(typ, arena, warnings);
}

fn collect_unused_bs_attributes_from_core_type(
    typ: &CoreType,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    collect_unused_bs_attributes(&typ.ptyp_attributes, arena, warnings);

    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, result, _) = &**inner;
            collect_unused_bs_attributes(&arg.attrs, arena, warnings);
            collect_unused_bs_attributes_from_core_type_idx(arg.typ, arena, warnings);
            collect_unused_bs_attributes_from_core_type_idx(*result, arena, warnings);
        }
        CoreTypeDesc::Ptyp_tuple(types) => {
            for typ_idx in types.iter() {
                collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
            }
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (_, args) = &**inner;
            for typ_idx in args.iter() {
                collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
            }
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            let (fields, _) = &**inner;
            for field in fields.iter() {
                match field {
                    ObjectField::Otag(_, attrs, typ_idx) => {
                        collect_unused_bs_attributes(attrs, arena, warnings);
                        collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
                    }
                    ObjectField::Oinherit(typ_idx) => {
                        collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
                    }
                }
            }
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (typ_idx, _) = &**inner;
            collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (rows, _, _) = &**inner;
            for row in rows.iter() {
                match row {
                    RowField::Rtag(_, attrs, _, types) => {
                        collect_unused_bs_attributes(attrs, arena, warnings);
                        for typ_idx in types.iter() {
                            collect_unused_bs_attributes_from_core_type_idx(
                                *typ_idx, arena, warnings,
                            );
                        }
                    }
                    RowField::Rinherit(typ_idx) => {
                        collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
                    }
                }
            }
        }
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (_, typ_idx) = &**inner;
            collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
        }
        CoreTypeDesc::Ptyp_package(pkg) => {
            let (_, constraints) = &**pkg;
            for (_, typ_idx) in constraints.iter() {
                collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
            }
        }
        CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) | CoreTypeDesc::Ptyp_extension(_) => {}
    }
}

fn collect_unused_bs_attributes_from_pat_idx(
    pat_idx: PatIdx,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let pat = arena.get_pat(pat_idx);
    collect_unused_bs_attributes(&pat.ppat_attributes, arena, warnings);

    match &*pat.ppat_desc {
        PatternDesc::Ppat_alias(inner, _) | PatternDesc::Ppat_exception(inner) => {
            collect_unused_bs_attributes_from_pat_idx(*inner, arena, warnings);
        }
        PatternDesc::Ppat_tuple(items) | PatternDesc::Ppat_array(items) => {
            for item in items.iter() {
                collect_unused_bs_attributes_from_pat_idx(*item, arena, warnings);
            }
        }
        PatternDesc::Ppat_construct(_, payload) => {
            if let Some(payload) = payload {
                collect_unused_bs_attributes_from_pat_idx(*payload, arena, warnings);
            }
        }
        PatternDesc::Ppat_variant(inner) => {
            let (_, payload) = &**inner;
            if let Some(payload) = payload {
                collect_unused_bs_attributes_from_pat_idx(*payload, arena, warnings);
            }
        }
        PatternDesc::Ppat_record(inner) => {
            let (fields, _) = &**inner;
            for field in fields.iter() {
                collect_unused_bs_attributes_from_pat_idx(field.pat, arena, warnings);
            }
        }
        PatternDesc::Ppat_or(left, right) => {
            collect_unused_bs_attributes_from_pat_idx(*left, arena, warnings);
            collect_unused_bs_attributes_from_pat_idx(*right, arena, warnings);
        }
        PatternDesc::Ppat_constraint(inner) => {
            let (inner_pat, typ_idx) = &**inner;
            collect_unused_bs_attributes_from_pat_idx(*inner_pat, arena, warnings);
            collect_unused_bs_attributes_from_core_type_idx(*typ_idx, arena, warnings);
        }
        PatternDesc::Ppat_open(_, inner) => {
            collect_unused_bs_attributes_from_pat_idx(*inner, arena, warnings);
        }
        PatternDesc::Ppat_any
        | PatternDesc::Ppat_var(_)
        | PatternDesc::Ppat_constant(_)
        | PatternDesc::Ppat_interval(_)
        | PatternDesc::Ppat_type(_)
        | PatternDesc::Ppat_unpack(_)
        | PatternDesc::Ppat_extension(_) => {}
    }
}

fn collect_raw_js_warnings_from_value_binding(
    binding: &ValueBinding,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    collect_unused_bs_attributes(&binding.pvb_attributes, arena, warnings);
    collect_unused_bs_attributes_from_pat_idx(binding.pvb_pat, arena, warnings);
    collect_raw_js_warnings_from_expr_idx(binding.pvb_expr, arena, warnings);
}

fn collect_obj_optional_as_warnings(
    vd: &ValueDescription,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    if !attr_named(vd.pval_attributes.as_slice(), "obj", arena) {
        return;
    }

    let vd_type = arena.get_core_type(vd.pval_type);
    let (args, _) = list_of_arrow(vd_type, arena);
    for arg in args {
        let arg_type = arena.get_core_type(arg.typ);
        let warn_type_as = match arg.lbl {
            // Rust collects warnings in a pre-pass, but OCaml reaches the same
            // optional-arg helper before unused `@as` warnings can be reported.
            ArgLabel::Optional(_) => get_opt_arg_type(false, arg_type, arena).is_ok(),
            ArgLabel::Labelled(_) => !matches!(&*arg_type.ptyp_desc, CoreTypeDesc::Ptyp_any),
            ArgLabel::Nolabel => false,
        };
        if !warn_type_as {
            continue;
        }
        // OCaml leaves these @as payloads unused for @obj arguments, then
        // warns once during FFI processing and once during the remaining
        // unused-attribute sweep.
        for _ in 0..2 {
            for (attr_name, _) in arg_type.ptyp_attributes.iter() {
                if arena.get_string(attr_name.txt) == "as" {
                    warnings.push(PpxWarning {
                        loc: attr_name.loc,
                        warning: Warning::BsUnusedAttribute {
                            name: "as".to_string(),
                        },
                    });
                }
            }
        }
    }
}

fn collect_external_string_redundant_warnings(
    vd: &ValueDescription,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    if !is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return;
    }

    let vd_type = arena.get_core_type(vd.pval_type).clone();
    let (args, _) = list_of_arrow(&vd_type, arena);
    for arg in args {
        let typ = arena.get_core_type(arg.typ).clone();
        collect_string_redundant_warning_from_type(&typ, arena, warnings);
    }
}

fn collect_string_redundant_warning_from_type(
    typ: &CoreType,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    if check_type_ffi_attrs(typ, arena) != Some("string") || type_ffi_attr_count(typ, arena) != 1 {
        return;
    }

    let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc else {
        return;
    };
    let (row_fields, closed, labels) = &**variant_inner;
    if !matches!(closed, current::ClosedFlag::Closed) || labels.is_some() || row_fields.is_empty() {
        return;
    }

    let redundant = row_fields.iter().all(|field| match field {
        RowField::Rtag(_tag, attrs, true, types) if types.is_empty() => {
            !attr_named(attrs, "as", arena)
        }
        _ => false,
    });
    if redundant {
        warnings.push(PpxWarning {
            loc: typ.ptyp_loc,
            warning: Warning::BsFfiWarning {
                message: "@string is redundant here, you can safely remove it".to_string(),
            },
        });
    }
}

fn type_ffi_attr_count(typ: &CoreType, arena: &ParseArena) -> usize {
    typ.ptyp_attributes
        .iter()
        .filter(|(attr_name, _)| {
            matches!(
                arena.get_string(attr_name.txt),
                "string" | "int" | "ignore" | "unwrap"
            )
        })
        .count()
}

fn collect_raw_js_warnings_from_expr(
    expr: &Expression,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    collect_unused_bs_attributes(&expr.pexp_attributes, arena, warnings);

    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_extension(ext) => {
            let (ext_name, payload) = &**ext;
            match arena.get_string(ext_name.txt) {
                "raw" => push_raw_js_expression_warning(payload, arena, warnings),
                "re" => push_raw_re_warning(payload, arena, warnings),
                "ffi" => push_ffi_function_warning(payload, arena, warnings),
                _ => {}
            }
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (_rec_flag, bindings, body) = &**inner;
            for binding in bindings {
                collect_raw_js_warnings_from_value_binding(binding, arena, warnings);
            }
            collect_raw_js_warnings_from_expr_idx(*body, arena, warnings);
        }
        ExpressionDesc::Pexp_fun(fun) => {
            collect_unused_bs_attributes_from_pat_idx(fun.lhs, arena, warnings);
            if let Some(default) = fun.default {
                collect_raw_js_warnings_from_expr_idx(default, arena, warnings);
            }
            collect_raw_js_warnings_from_expr_idx(fun.rhs, arena, warnings);
        }
        ExpressionDesc::Pexp_apply(apply) => {
            collect_raw_js_warnings_from_expr_idx(apply.funct, arena, warnings);
            for (_label, arg) in &apply.args {
                collect_raw_js_warnings_from_expr_idx(*arg, arena, warnings);
            }
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*scrutinee, arena, warnings);
            for case in cases {
                collect_unused_bs_attributes_from_pat_idx(case.pc_lhs, arena, warnings);
                if let Some(guard) = case.pc_guard {
                    collect_raw_js_warnings_from_expr_idx(guard, arena, warnings);
                }
                collect_raw_js_warnings_from_expr_idx(case.pc_rhs, arena, warnings);
            }
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            for item in items.iter() {
                collect_raw_js_warnings_from_expr_idx(*item, arena, warnings);
            }
        }
        ExpressionDesc::Pexp_construct(_lid, payload) => {
            if let Some(payload) = payload {
                collect_raw_js_warnings_from_expr_idx(*payload, arena, warnings);
            }
        }
        ExpressionDesc::Pexp_variant(inner) => {
            let (_label, payload) = &**inner;
            if let Some(payload) = payload {
                collect_raw_js_warnings_from_expr_idx(*payload, arena, warnings);
            }
        }
        ExpressionDesc::Pexp_record(fields_and_spread) => {
            let (fields, spread) = &**fields_and_spread;
            for field in fields {
                collect_raw_js_warnings_from_expr_idx(field.expr, arena, warnings);
            }
            if let Some(spread) = spread {
                collect_raw_js_warnings_from_expr_idx(*spread, arena, warnings);
            }
        }
        ExpressionDesc::Pexp_field(expr, _)
        | ExpressionDesc::Pexp_assert(expr)
        | ExpressionDesc::Pexp_await(expr)
        | ExpressionDesc::Pexp_comptime_compile_error(expr)
        | ExpressionDesc::Pexp_comptime_build_variant(expr)
        | ExpressionDesc::Pexp_comptime_variant_case(expr)
        | ExpressionDesc::Pexp_comptime_build_record(expr)
        | ExpressionDesc::Pexp_comptime_record_field(expr) => {
            collect_raw_js_warnings_from_expr_idx(*expr, arena, warnings);
        }
        ExpressionDesc::Pexp_send(inner) => {
            let (expr, _method) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*expr, arena, warnings);
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (_name, expr) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*expr, arena, warnings);
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (_override, _lid, expr) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*expr, arena, warnings);
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (record, _field, value) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*record, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*value, arena, warnings);
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (condition, consequent, alternate) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*condition, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*consequent, arena, warnings);
            if let Some(alternate) = alternate {
                collect_raw_js_warnings_from_expr_idx(*alternate, arena, warnings);
            }
        }
        ExpressionDesc::Pexp_sequence(left, right) | ExpressionDesc::Pexp_while(left, right) => {
            collect_raw_js_warnings_from_expr_idx(*left, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*right, arena, warnings);
        }
        ExpressionDesc::Pexp_comptime_field(inner) => {
            let (value, field) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*value, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*field, arena, warnings);
        }
        ExpressionDesc::Pexp_comptime_record(inner) => {
            let (typ, fields) = &**inner;
            collect_unused_bs_attributes_from_core_type_idx(*typ, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*fields, arena, warnings);
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (_pat, from, to, _dir, body) = &**inner;
            collect_unused_bs_attributes_from_pat_idx(*_pat, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*from, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*to, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*body, arena, warnings);
        }
        ExpressionDesc::Pexp_for_of(inner)
        | ExpressionDesc::Pexp_for_await_of(inner)
        | ExpressionDesc::Pexp_inline_for(inner) => {
            let (_pat, collection, body) = &**inner;
            collect_unused_bs_attributes_from_pat_idx(*_pat, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*collection, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*body, arena, warnings);
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (expr, typ) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*expr, arena, warnings);
            collect_unused_bs_attributes_from_core_type_idx(*typ, arena, warnings);
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (expr, from_type, to_type) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*expr, arena, warnings);
            if let Some(from_type) = from_type {
                collect_unused_bs_attributes_from_core_type_idx(*from_type, arena, warnings);
            }
            collect_unused_bs_attributes_from_core_type_idx(*to_type, arena, warnings);
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_name, mod_expr, body) = &**inner;
            collect_raw_js_warnings_from_mod_expr_idx(*mod_expr, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*body, arena, warnings);
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (_extension, body) = &**inner;
            collect_raw_js_warnings_from_expr_idx(*body, arena, warnings);
        }
        ExpressionDesc::Pexp_pack(mod_expr) => {
            collect_raw_js_warnings_from_mod_expr_idx(*mod_expr, arena, warnings);
        }
        ExpressionDesc::Pexp_comptime_variant(inner) => {
            let (typ, name, payload) = &**inner;
            collect_unused_bs_attributes_from_core_type_idx(*typ, arena, warnings);
            collect_raw_js_warnings_from_expr_idx(*name, arena, warnings);
            if let Some(payload) = payload {
                collect_raw_js_warnings_from_expr_idx(*payload, arena, warnings);
            }
        }
        ExpressionDesc::Pexp_comptime_typeinfo(typ)
        | ExpressionDesc::Pexp_comptime_typename(typ) => {
            collect_unused_bs_attributes_from_core_type_idx(*typ, arena, warnings);
        }
        _ => {}
    }
}

fn collect_raw_js_warnings_from_structure(
    structure: &[StructureItem],
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    for item in structure {
        collect_raw_js_warnings_from_structure_item(item, arena, warnings);
    }
}

pub fn collect_raw_js_warnings(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> Vec<PpxWarning> {
    let mut warnings = Vec::new();
    collect_raw_js_warnings_from_structure(structure, arena, &mut warnings);
    warnings
}

fn collect_signature_warnings_from_value_description(
    vd: &ValueDescription,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    collect_obj_optional_as_warnings(vd, arena, warnings);
    collect_external_string_redundant_warnings(vd, arena, warnings);

    if is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return;
    }

    collect_unused_bs_attributes(&vd.pval_attributes, arena, warnings);
    collect_unused_bs_attributes_from_core_type_idx(vd.pval_type, arena, warnings);
}

fn collect_signature_warnings_from_mod_type_idx(
    mod_type_idx: ModTypeIdx,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let mod_type = arena.get_mod_type(mod_type_idx);
    collect_unused_bs_attributes(&mod_type.pmty_attributes, arena, warnings);

    match &*mod_type.pmty_desc {
        ModuleTypeDesc::Pmty_signature(items) => {
            collect_signature_warnings_from_items(items, arena, warnings);
        }
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_, param_type, result_type) = &**inner;
            if let Some(param_type) = param_type {
                collect_signature_warnings_from_mod_type_idx(*param_type, arena, warnings);
            }
            collect_signature_warnings_from_mod_type_idx(*result_type, arena, warnings);
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (mod_type, _constraints) = &**inner;
            collect_signature_warnings_from_mod_type_idx(*mod_type, arena, warnings);
        }
        ModuleTypeDesc::Pmty_ident(_)
        | ModuleTypeDesc::Pmty_typeof(_)
        | ModuleTypeDesc::Pmty_extension(_)
        | ModuleTypeDesc::Pmty_alias(_) => {}
    }
}

fn collect_signature_warnings_from_item(
    item: &SignatureItem,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    match &*item.psig_desc {
        SignatureItemDesc::Psig_value(vd) => {
            collect_signature_warnings_from_value_description(vd, arena, warnings);
        }
        SignatureItemDesc::Psig_module(md) => {
            collect_unused_bs_attributes(&md.pmd_attributes, arena, warnings);
            collect_signature_warnings_from_mod_type_idx(md.pmd_type, arena, warnings);
        }
        SignatureItemDesc::Psig_recmodule(items) => {
            for md in items.iter() {
                collect_unused_bs_attributes(&md.pmd_attributes, arena, warnings);
                collect_signature_warnings_from_mod_type_idx(md.pmd_type, arena, warnings);
            }
        }
        SignatureItemDesc::Psig_modtype(mtd) => {
            collect_unused_bs_attributes(&mtd.pmtd_attributes, arena, warnings);
            if let Some(mod_type) = mtd.pmtd_type {
                collect_signature_warnings_from_mod_type_idx(mod_type, arena, warnings);
            }
        }
        SignatureItemDesc::Psig_include(include_desc) => {
            collect_unused_bs_attributes(&include_desc.pincl_attributes, arena, warnings);
            collect_signature_warnings_from_mod_type_idx(include_desc.pincl_mod, arena, warnings);
        }
        SignatureItemDesc::Psig_attribute(attr) => {
            collect_unused_bs_attributes_from_slice(std::slice::from_ref(attr), arena, warnings);
        }
        SignatureItemDesc::Psig_extension(inner) => {
            let (_, attrs) = &**inner;
            collect_unused_bs_attributes(attrs, arena, warnings);
        }
        SignatureItemDesc::Psig_type(inner) => {
            let (_rec_flag, tdcls) = &**inner;
            collect_deriving_not_applicable_warnings(
                tdcls,
                arena,
                warnings,
                DerivingExpansionContext::SignatureItem,
            );
        }
        SignatureItemDesc::Psig_typext(_)
        | SignatureItemDesc::Psig_exception(_)
        | SignatureItemDesc::Psig_open(_) => {}
    }
}

fn collect_signature_warnings_from_items(
    items: &[SignatureItem],
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    for item in items {
        collect_signature_warnings_from_item(item, arena, warnings);
    }
}

pub fn collect_signature_warnings(
    signature: &[SignatureItem],
    arena: &ParseArena,
) -> Vec<PpxWarning> {
    let mut warnings = Vec::new();
    collect_signature_warnings_from_items(signature, arena, &mut warnings);
    warnings
}

fn is_js_regex_literal(s: &str) -> bool {
    use oxc_allocator::Allocator;
    use oxc_ast::ast::Expression;
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    let allocator = Allocator::default();
    matches!(
        Parser::new(&allocator, s, SourceType::default()).parse_expression(),
        Ok(Expression::RegExpLiteral(_))
    )
}

/// Process args from list_of_arrow into FFI Param specs and compute arity.
/// This mirrors OCaml's fold_right in handle_attributes which builds
/// arg_type_specs and arg_type_specs_length.
fn build_arg_type_specs(typ: &CoreType, arena: &mut ParseArena) -> (Params, usize) {
    let (args, _result) = list_of_arrow(typ, arena);

    let mut param_specs: Vec<Param> = Vec::new();
    let mut arity = 0;
    // OCaml tracks whether any runtime argument remains after filtering Arg_cst.
    // When all args are constants but arity > 0, it appends a trailing unit param.
    let mut has_runtime_args = false;

    for arg in &args {
        let (label_noname, arg_type, keeps_runtime_arg) = match &arg.lbl {
            ArgLabel::Optional(_) => {
                let arg_typ = arena.get_core_type(arg.typ).clone();
                let arg_type = get_opt_arg_type_unchecked(false, &arg_typ, arena);
                // Optional args are never Arg_cst and are kept in `args`.
                (LabelNoname::ArgOptional, arg_type, true)
            }
            ArgLabel::Labelled(_) => {
                let arg_typ = arena.get_core_type(arg.typ).clone();
                let arg_type = refine_arg_type(false, &arg_typ, arena);
                let keeps_runtime_arg = !matches!(arg_type, Attr::ArgCst(_));
                (LabelNoname::ArgLabel, arg_type, keeps_runtime_arg)
            }
            ArgLabel::Nolabel => {
                let arg_typ = arena.get_core_type(arg.typ).clone();
                let arg_type = refine_arg_type(true, &arg_typ, arena);
                let keeps_runtime_arg = !matches!(arg_type, Attr::ArgCst(_));
                (LabelNoname::ArgEmpty, arg_type, keeps_runtime_arg)
            }
        };

        if keeps_runtime_arg {
            has_runtime_args = true;
        }

        let is_ignored = matches!(arg_type, Attr::Ignore);
        if !is_ignored {
            arity += 1;
        }

        param_specs.push(Param {
            arg_type,
            arg_label: label_noname,
        });
    }

    // OCaml: if every argument got erased from the callable type (all Arg_cst) but
    // arg_type_specs_length > 0, append a trailing unit parameter to keep it callable.
    if !has_runtime_args && arity > 0 {
        param_specs.push(Param {
            arg_type: Attr::ExternUnit,
            arg_label: LabelNoname::ArgEmpty,
        });
    }

    // OCaml's ffi_bs_aux: if all args are {Nothing, Arg_empty}, use ParamNumber(n)
    // Otherwise use Params(list)
    let all_simple = param_specs.iter().all(|p| {
        matches!(
            (&p.arg_label, &p.arg_type),
            (LabelNoname::ArgEmpty, Attr::Nothing)
        )
    });
    let params = if all_simple {
        Params::ParamNumber(arity as i64)
    } else {
        Params::Params(param_specs)
    };

    (params, arity)
}

fn params_is_single_extern_unit(params: &Params) -> bool {
    matches!(
        params,
        Params::Params(param_specs)
            if matches!(
                param_specs.as_slice(),
                [Param {
                    arg_type: Attr::ExternUnit,
                    ..
                }]
            )
    )
}

fn params_first_arg_is_const(params: &Params) -> bool {
    matches!(
        params,
        Params::Params(param_specs)
            if matches!(
                param_specs.first(),
                Some(Param {
                    arg_type: Attr::ArgCst(_),
                    ..
                })
            )
    )
}

fn external_desc_is_plain_get(desc: &ExternalDesc) -> bool {
    desc.get_name.is_some()
        && desc.val_name.is_none()
        && desc.call_name.is_none()
        && !desc.module_as_val
        && desc.external_module_name.is_none()
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.set_name.is_none()
        && !desc.set_index
        && !desc.get_index
        && !desc.splice
}

fn external_desc_is_plain_set(desc: &ExternalDesc) -> bool {
    desc.set_name.is_some()
        && desc.val_name.is_none()
        && desc.call_name.is_none()
        && !desc.module_as_val
        && desc.external_module_name.is_none()
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.get_name.is_none()
        && !desc.set_index
        && !desc.get_index
        && !desc.splice
}

fn external_desc_is_plain_send(desc: &ExternalDesc) -> bool {
    desc.send_name.is_some()
        && desc.val_name.is_none()
        && desc.call_name.is_none()
        && !desc.module_as_val
        && desc.external_module_name.is_none()
        && desc.new_name.is_none()
        && desc.set_name.is_none()
        && desc.get_name.is_none()
        && !desc.set_index
        && !desc.get_index
}

fn external_desc_is_plain_obj(desc: &ExternalDesc) -> bool {
    desc.mk_obj
        && desc.val_name.is_none()
        && desc.call_name.is_none()
        && !desc.module_as_val
        && desc.external_module_name.is_none()
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.set_name.is_none()
        && desc.get_name.is_none()
        && !desc.set_index
        && !desc.get_index
        && !desc.splice
        && desc.scopes.is_empty()
        && desc.return_wrapper == ReturnWrapper::ReturnUnset
}

fn external_desc_is_plain_get_index(desc: &ExternalDesc) -> bool {
    desc.get_index
        && desc.val_name.is_none()
        && desc.call_name.is_none()
        && !desc.module_as_val
        && desc.external_module_name.is_none()
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.set_name.is_none()
        && desc.get_name.is_none()
        && !desc.set_index
        && !desc.splice
}

fn external_desc_is_plain_set_index(desc: &ExternalDesc) -> bool {
    desc.set_index
        && desc.val_name.is_none()
        && desc.call_name.is_none()
        && !desc.module_as_val
        && desc.external_module_name.is_none()
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.set_name.is_none()
        && desc.get_name.is_none()
        && !desc.get_index
        && !desc.splice
}

fn module_as_val_conflict_reason(desc: &ExternalDesc) -> Option<&'static str> {
    if !desc.module_as_val {
        return None;
    }

    if desc.send_name.is_some() {
        return Some(
            "Conflicting attributes: @module is for imports from a module, @send does not need import a module ",
        );
    }

    let has_conflicting_shape = desc.external_module_name.is_some()
        || desc.call_name.is_some()
        || desc.set_name.is_some()
        || desc.get_name.is_some()
        || !desc.scopes.is_empty();
    let has_conflicting_new_val = desc.new_name.is_some() && desc.val_name.is_some();

    if has_conflicting_shape || has_conflicting_new_val {
        Some("Conflicting attributes: Attribute found that conflicts with @module.")
    } else {
        None
    }
}

fn external_desc_is_plain_call(desc: &ExternalDesc) -> bool {
    desc.call_name.is_some()
        && desc.val_name.is_none()
        && !desc.module_as_val
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.set_name.is_none()
        && desc.get_name.is_none()
        && !desc.set_index
        && !desc.get_index
}

fn external_desc_is_plain_val(desc: &ExternalDesc) -> bool {
    desc.val_name.is_some()
        && desc.call_name.is_none()
        && !desc.module_as_val
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.set_name.is_none()
        && desc.get_name.is_none()
        && !desc.set_index
        && !desc.get_index
        && !desc.splice
}

fn external_desc_is_plain_new(desc: &ExternalDesc) -> bool {
    desc.new_name.is_some()
        && desc.val_name.is_none()
        && desc.call_name.is_none()
        && !desc.module_as_val
        && desc.send_name.is_none()
        && desc.set_name.is_none()
        && desc.get_name.is_none()
        && !desc.set_index
        && !desc.get_index
}

fn external_desc_is_module_as_class(desc: &ExternalDesc) -> bool {
    desc.module_as_val
        && desc.new_name.is_some()
        && desc.val_name.is_none()
        && desc.call_name.is_none()
        && desc.external_module_name.is_none()
        && desc.send_name.is_none()
        && desc.set_name.is_none()
        && desc.get_name.is_none()
        && !desc.set_index
        && !desc.get_index
        && desc.scopes.is_empty()
}

fn validate_plain_obj_arg_type_errors(
    vd_type: &CoreType,
    external_loc: LocIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let (args, _result) = list_of_arrow(vd_type, arena);
    for arg in args {
        let typ = arena.get_core_type(arg.typ).clone();
        match arg.lbl {
            ArgLabel::Labelled(label_loc) => {
                if matches!(&*typ.ptyp_desc, CoreTypeDesc::Ptyp_any)
                    && get_as_string_attr(&arg.attrs, arena).is_none()
                    && get_as_int_attr(&arg.attrs, arena).is_none()
                    // OCaml compiler/syntax/src/res_core.ml:5018-5026 keeps
                    // labelled `@as(json`...`) _` external arguments as
                    // arity-changing constants. The `@as` payload was already
                    // validated by `validate_external_arg_type_errors`, so only
                    // reject a truly bare `_` here.
                    && !typ
                        .ptyp_attributes
                        .iter()
                        .any(|(attr_name, _)| arena.get_string(attr_name.txt) == "as")
                {
                    return Err(PpxError::at_loc(
                        typ.ptyp_loc,
                        "_ is not allowed in combination with external optional type",
                    ));
                }

                let label = arena.get_string(label_loc.txt).to_string();
                match spec_of_ptyp(false, &typ, arena) {
                    Attr::PolyVar { .. } => {
                        return Err(PpxError::at_loc(
                            external_loc,
                            format!("@obj label {label} does not support such arg type"),
                        ));
                    }
                    Attr::Unwrap => {
                        return Err(PpxError::at_loc(
                            external_loc,
                            format!("@obj label {label} does not support @unwrap arguments"),
                        ));
                    }
                    _ => {}
                }
            }
            ArgLabel::Optional(label_loc) => {
                let label = arena.get_string(label_loc.txt).to_string();
                match get_opt_arg_type(false, &typ, arena)? {
                    Attr::PolyVar { .. } => {
                        return Err(PpxError::at_loc(
                            external_loc,
                            format!("@obj label {label} does not support such arg type"),
                        ));
                    }
                    Attr::Unwrap => {
                        return Err(PpxError::at_loc(
                            external_loc,
                            format!("@obj label {label} does not support @unwrap arguments"),
                        ));
                    }
                    _ => {}
                }
            }
            ArgLabel::Nolabel => {
                if !is_unit_type(&typ, arena) {
                    return Err(PpxError::at_loc(
                        external_loc,
                        "expect label, optional, or unit here",
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_external_attribute_payload_errors(
    attrs: &[Attribute],
    prim_name: &str,
    arena: &ParseArena,
) -> PpxResult<()> {
    for (attr_name, payload) in attrs {
        match arena.get_string(attr_name.txt) {
            "taggedTemplate" => {
                // Upstream compiler/frontend/ast_external_process.ml:354-362.
                return Err(PpxError::at_loc(
                    attr_name.loc,
                    "The @taggedTemplate decorator has been removed. Bind the external with the builtin taggedTemplate<'param, 'output> type instead, e.g. `@module(\"x\") external sql: taggedTemplate<'a, 'b> = \"sql\"`.",
                ));
            }
            "val" | "send" | "set" | "get" | "new" => {
                if !payload_is_empty_str(payload)
                    && !payload_is_single_string_literal(payload, arena)
                {
                    return Err(PpxError::at_loc(attr_name.loc, "Invalid payload"));
                }
            }
            "module" => {
                if validate_module_import_attributes_payload(payload, arena)? {
                    continue;
                }
                let strings =
                    match payload_string_literals_or_error_loc(payload, arena, attr_name.loc) {
                        Ok(strings) => strings,
                        Err(loc) => {
                            return Err(PpxError::at_loc(loc, "expect string tuple list"));
                        }
                    };
                if strings.len() > 2 {
                    return Err(PpxError::at_loc(attr_name.loc, "Illegal attributes"));
                }
            }
            "scope" => {
                let scopes =
                    match payload_string_literals_or_error_loc(payload, arena, attr_name.loc) {
                        Ok(scopes) => scopes,
                        Err(loc) => {
                            return Err(PpxError::at_loc(loc, "expect string tuple list"));
                        }
                    };
                if scopes.is_empty() {
                    return Err(PpxError::at_loc(attr_name.loc, "Illegal attributes"));
                }
            }
            "set_index" => {
                if !prim_name.is_empty() {
                    return Err(PpxError::at_loc(
                        attr_name.loc,
                        "@set_index this particular external's name needs to be a placeholder empty string",
                    ));
                }
            }
            "get_index" => {
                if !prim_name.is_empty() {
                    return Err(PpxError::at_loc(
                        attr_name.loc,
                        "@get_index this particular external's name needs to be a placeholder empty string",
                    ));
                }
            }
            "return" => {
                validate_return_wrapper_config_shape(payload, arena)?;
                let config_warning = return_wrapper_config_warning(payload, arena, attr_name.loc);
                let Some(wrapper) = get_return_wrapper_config(payload, arena) else {
                    let mut error =
                        PpxError::at_loc(attr_name.loc, "Not supported return directive");
                    if let Some((loc, message)) = config_warning {
                        error = error.with_warning(
                            loc,
                            Warning::BsDeriveWarning {
                                message: message.to_string(),
                            },
                        );
                    }
                    return Err(error);
                };
                match wrapper.as_str() {
                    "null_to_opt" | "nullable" | "null_undefined_to_opt" | "identity" => {}
                    _ => {
                        return Err(PpxError::at_loc(
                            attr_name.loc,
                            "Not supported return directive",
                        ));
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_return_wrapper_result_type(
    return_wrapper: &ReturnWrapper,
    result_type: &CoreType,
    external_loc: LocIdx,
    arena: &ParseArena,
) -> PpxResult<()> {
    if matches!(
        return_wrapper,
        ReturnWrapper::ReturnNullToOpt | ReturnWrapper::ReturnNullUndefinedToOpt
    ) && !is_user_option_type(result_type, arena)
    {
        return Err(PpxError::at_loc(
            external_loc,
            "%@return directive *_to_opt expect return type to be \nsyntax wise `_ option` for safety",
        ));
    }
    Ok(())
}

fn validate_variadic_arg_type_errors(
    args: &[TypeArg],
    external_loc: LocIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let Some(last_arg) = args.last() else {
        return Ok(());
    };

    if matches!(last_arg.lbl, ArgLabel::Optional(_)) {
        return Err(PpxError::at_loc(
            external_loc,
            "@variadic expect the last type to be a non optional",
        ));
    }

    let typ = arena.get_core_type(last_arg.typ).clone();
    let array_error = || {
        PpxError::at_loc(
            external_loc,
            "@variadic expect the last type to be an array",
        )
    };

    if matches!(&*typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
        return Err(array_error());
    }

    if !matches!(refine_arg_type(true, &typ, arena), Attr::Nothing) {
        return Err(array_error());
    }

    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            if args.len() == 1 {
                if let Longident::Lident(name) = arena.get_longident(lid.txt) {
                    if arena.get_string(*name) == "array" {
                        return Ok(());
                    }
                }
            }
            Err(array_error())
        }
        _ => Err(array_error()),
    }
}

fn validate_non_obj_optional_arg_type_errors(
    args: &[TypeArg],
    external_loc: LocIdx,
    arena: &ParseArena,
) -> PpxResult<()> {
    for arg in args {
        let ArgLabel::Optional(label_loc) = arg.lbl else {
            continue;
        };

        let typ = arena.get_core_type(arg.typ);
        if matches!(get_opt_arg_type(false, typ, arena)?, Attr::PolyVar { .. }) {
            let label = arena.get_string(label_loc.txt);
            return Err(PpxError::at_loc(
                external_loc,
                format!("@string does not work with optional when it has arities in label {label}"),
            ));
        }
    }
    Ok(())
}

fn validate_external_arg_type_errors(args: &[TypeArg], arena: &mut ParseArena) -> PpxResult<()> {
    for arg in args {
        let typ = arena.get_core_type(arg.typ).clone();
        validate_external_core_type_arg_errors(&typ, arena)?;
    }
    Ok(())
}

fn validate_external_core_type_arg_errors(typ: &CoreType, arena: &mut ParseArena) -> PpxResult<()> {
    if matches!(&*typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
        validate_string_or_int_as_attrs(&typ.ptyp_attributes, arena)?;
    }

    match external_type_ffi_attr(typ, arena)? {
        Some("string") => validate_bs_string_type(typ, arena),
        Some("int") => validate_bs_int_type(typ, arena),
        Some("unwrap") => validate_bs_unwrap_type(typ),
        Some("ignore") | None => Ok(()),
        Some(_) => Ok(()),
    }
}

fn validate_external_attribute_errors(
    vd: &ValueDescription,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    if !is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return Ok(());
    }

    let Some(prim_name) = vd.pval_prim.first() else {
        return Ok(());
    };
    let prim_name = arena.get_string(*prim_name).to_string();
    let vd_type = arena.get_core_type(vd.pval_type).clone();
    let (args, result_type) = list_of_arrow(&vd_type, arena);

    validate_external_attribute_payload_errors(&vd.pval_attributes, prim_name.as_str(), arena)?;
    validate_external_arg_type_errors(&args, arena)?;

    let desc = parse_external_attrs(
        &vd.pval_attributes,
        prim_name.as_str(),
        args.is_empty(),
        vd.pval_loc,
        arena,
    );

    if desc.mk_obj {
        if external_desc_is_plain_obj(&desc) {
            // OCaml Ast_external_process.process_obj rejects non-empty
            // primitive names for plain @obj externals before reconstructing
            // the external type.
            if !prim_name.is_empty() {
                return Err(PpxError::at_loc(
                    vd.pval_loc,
                    "@obj expect external names to be empty string",
                ));
            }
            validate_plain_obj_arg_type_errors(&vd_type, vd.pval_loc, arena)?;
            return Ok(());
        }
        return Err(PpxError::at_loc(
            vd.pval_loc,
            "Attribute found that conflicts with @obj",
        ));
    }

    if desc.splice {
        validate_variadic_arg_type_errors(&args, vd.pval_loc, arena)?;
    }

    validate_non_obj_optional_arg_type_errors(&args, vd.pval_loc, arena)?;

    let (params, arity) = build_arg_type_specs(&vd_type, arena);

    if desc.set_index && !external_desc_is_plain_set_index(&desc) {
        return Err(PpxError::at_loc(
            vd.pval_loc,
            "Conflicting attributes: Attribute found that conflicts with %@set_index",
        ));
    }

    if desc.get_index && !external_desc_is_plain_get_index(&desc) {
        return Err(PpxError::at_loc(
            vd.pval_loc,
            "Conflicting attributes: Attribute found that conflicts with %@get_index",
        ));
    }

    if external_desc_is_plain_set_index(&desc) && arity != 3 {
        return Err(PpxError::at_loc(
            vd.pval_loc,
            "Ill defined attribute @set_index (arity of 3)",
        ));
    }

    if external_desc_is_plain_get_index(&desc) && arity != 2 {
        return Err(PpxError::at_loc(
            vd.pval_loc,
            format!("Ill defined attribute @get_index (arity expected 2 : while {arity})"),
        ));
    }

    if !desc.mk_obj {
        if let Some(reason) = module_as_val_conflict_reason(&desc) {
            return Err(PpxError::at_loc(vd.pval_loc, reason));
        }

        if desc.module_as_val && desc.new_name_from_payload && desc.val_name.is_none() {
            return Err(PpxError::at_loc(
                vd.pval_loc,
                "Incorrect FFI attribute found: (@new should not carry a payload here)",
            ));
        }

        if desc.call_name.is_some() && !external_desc_is_plain_call(&desc) {
            return Err(PpxError::at_loc(
                vd.pval_loc,
                "Conflicting attributes: Attribute found that conflicts with %@val",
            ));
        }

        if desc.val_name.is_some() && !desc.module_as_val && !external_desc_is_plain_val(&desc) {
            return Err(PpxError::at_loc(
                vd.pval_loc,
                "Conflicting attributes: Attribute found that conflicts with %@val",
            ));
        }

        if external_desc_is_plain_send(&desc) {
            if arity == 0 {
                return Err(PpxError::at_loc(
                    vd.pval_loc,
                    "Ill defined attribute @send(the external needs to be a regular function call with at least one argument)",
                ));
            }

            if params_first_arg_is_const(&params) {
                return Err(PpxError::at_loc(
                    vd.pval_loc,
                    "Ill defined attribute @send(first argument can't be const)",
                ));
            }
        } else if desc.send_name.is_some() {
            return Err(PpxError::at_loc(
                vd.pval_loc,
                "You used a FFI attribute that can't be used with @send",
            ));
        }

        if desc.new_name.is_some()
            && !external_desc_is_plain_new(&desc)
            && !external_desc_is_module_as_class(&desc)
        {
            return Err(PpxError::at_loc(
                vd.pval_loc,
                "Conflicting attributes: Attribute found that conflicts with %@new",
            ));
        }

        if external_desc_is_plain_set(&desc) {
            if arity != 2 {
                return Err(PpxError::at_loc(
                    vd.pval_loc,
                    "Ill defined attribute @set (two args required)",
                ));
            }
        } else if desc.set_name.is_some() {
            return Err(PpxError::at_loc(
                vd.pval_loc,
                "conflict attributes found with @set",
            ));
        }

        if external_desc_is_plain_get(&desc) {
            if arity != 1 {
                return Err(PpxError::at_loc(
                    vd.pval_loc,
                    "Ill defined attribute @get (only one argument)",
                ));
            }

            // OCaml Ast_external_process.external_desc_of_non_obj rejects `@get`
            // externals with a single unit argument before emitting FFI metadata.
            if params_is_single_extern_unit(&params) {
                return Err(PpxError::at_loc(
                    vd.pval_loc,
                    "Ill defined attribute @get (unit argument is not allowed)",
                ));
            }
        } else if desc.get_name.is_some() {
            return Err(PpxError::at_loc(
                vd.pval_loc,
                "Attribute found that conflicts with @get",
            ));
        }
    }

    let result_is_unit = is_unit_type(&result_type, arena);
    let ffi = build_ffi_type(&desc, prim_name.as_str(), arity, result_is_unit, params);
    validate_ffi_names(&ffi, vd.pval_loc)?;
    validate_return_wrapper_result_type(&desc.return_wrapper, &result_type, vd.pval_loc, arena)?;

    Ok(())
}

/// Determine the arg type for a non-labeled argument type.
/// Mirrors OCaml's refine_arg_type / spec_of_ptyp.
fn refine_arg_type(nolabel: bool, typ: &CoreType, arena: &mut ParseArena) -> Attr {
    // For Ptyp_any with @as attribute, handle constant args
    if matches!(&*typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
        // Check for @as attribute on the type
        for (attr_name, payload) in &typ.ptyp_attributes {
            let name = arena.get_string(attr_name.txt).to_string();
            if name == "as" {
                // Try int first (mirrors OCaml's is_single_int check first)
                if let Some(i) = get_payload_int(payload, arena) {
                    return Attr::ArgCst(Cst::ArgIntLit(i as i64));
                }
                // Then try string with proper delimiter handling
                if let Some((s, delim)) = get_payload_string_with_delim(payload, arena) {
                    return Attr::ArgCst(Cst::ArgStringLit(s, delim));
                }
            }
        }
    }
    spec_of_ptyp(nolabel, typ, arena)
}

/// Check for @string, @int, @unwrap, @ignore attributes on a type.
/// Returns `Some(attr_type)` if found, `None` otherwise.
/// Mirrors OCaml's iter_process_bs_string_int_unwrap_uncurry.
fn check_type_ffi_attrs(typ: &CoreType, arena: &ParseArena) -> Option<&'static str> {
    for (attr_name, _) in &typ.ptyp_attributes {
        let name = arena.get_string(attr_name.txt);
        match name {
            "string" => return Some("string"),
            "int" => return Some("int"),
            "ignore" => return Some("ignore"),
            "unwrap" => return Some("unwrap"),
            _ => {}
        }
    }
    None
}

fn external_type_ffi_attr(typ: &CoreType, arena: &ParseArena) -> PpxResult<Option<&'static str>> {
    let mut found = None;
    for (attr_name, _) in &typ.ptyp_attributes {
        let name = arena.get_string(attr_name.txt);
        let attr = match name {
            "string" => "string",
            "int" => "int",
            "ignore" => "ignore",
            "unwrap" => "unwrap",
            _ => continue,
        };
        if found.is_some() {
            return Err(PpxError::at_loc(attr_name.loc, "conflicting attributes "));
        }
        found = Some(attr);
    }
    Ok(found)
}

fn payload_str_items(payload: &Payload) -> Option<&[StructureItem]> {
    match payload {
        Payload::PStr(items) => Some(items),
        _ => None,
    }
}

fn payload_is_empty_str(payload: &Payload) -> bool {
    matches!(payload, Payload::PStr(items) if items.is_empty())
}

fn payload_is_single_string_literal(payload: &Payload, arena: &ParseArena) -> bool {
    payload_single_string_literal(payload, arena).is_some()
}

fn payload_single_string_literal<'a>(
    payload: &'a Payload,
    arena: &'a ParseArena,
) -> Option<&'a str> {
    payload_single_string_literal_with_loc(payload, arena).map(|(s, _loc)| s)
}

fn payload_single_string_literal_with_loc<'a>(
    payload: &'a Payload,
    arena: &'a ParseArena,
) -> Option<(&'a str, LocIdx)> {
    payload_single_string_literal_info(payload, arena).map(|(s, loc, _offset)| (s, loc))
}

fn payload_single_string_literal_info<'a>(
    payload: &'a Payload,
    arena: &'a ParseArena,
) -> Option<(&'a str, LocIdx, i32)> {
    match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (expr, _) = &**eval_inner;
                let expr = arena.get_expr(*expr);
                if let ExpressionDesc::Pexp_constant(c) = &*expr.pexp_desc {
                    if let Constant::String(s, delim) = &**c {
                        let flow_offset = match delim {
                            None => 1,
                            Some(delim) => delim.len() as i32 + 2,
                        };
                        return Some((s.as_ref(), expr.pexp_loc, flow_offset));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

fn payload_single_record_fields_without_spread<'a>(
    payload: &'a Payload,
    arena: &'a ParseArena,
) -> Option<&'a Vec<ExpressionRecordField>> {
    match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (expr, _) = &**eval_inner;
                if let ExpressionDesc::Pexp_record(record) = &*arena.get_expr(*expr).pexp_desc {
                    if record.1.is_none() {
                        return Some(&record.0);
                    }
                }
            }
            None
        }
        _ => None,
    }
}

fn payload_string_literals(payload: &Payload, arena: &ParseArena) -> Option<Vec<String>> {
    match payload {
        Payload::PStr(items) if items.is_empty() => Some(Vec::new()),
        Payload::PStr(items) if items.len() == 1 => {
            let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc else {
                return None;
            };
            let (expr, _) = &**eval_inner;
            match &*arena.get_expr(*expr).pexp_desc {
                ExpressionDesc::Pexp_constant(c) => match &**c {
                    Constant::String(s, _) => Some(vec![s.to_string()]),
                    _ => None,
                },
                ExpressionDesc::Pexp_tuple(exprs) => {
                    let mut result = Vec::with_capacity(exprs.len());
                    for expr in exprs.iter() {
                        let ExpressionDesc::Pexp_constant(c) = &*arena.get_expr(*expr).pexp_desc
                        else {
                            return None;
                        };
                        let Constant::String(s, _) = &**c else {
                            return None;
                        };
                        result.push(s.to_string());
                    }
                    Some(result)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn payload_string_literals_or_error_loc(
    payload: &Payload,
    arena: &ParseArena,
    default_loc: LocIdx,
) -> Result<Vec<String>, LocIdx> {
    match payload {
        Payload::PStr(items) if items.is_empty() => Ok(Vec::new()),
        Payload::PStr(items) if items.len() == 1 => {
            let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc else {
                return Err(default_loc);
            };
            let (expr, _) = &**eval_inner;
            match &*arena.get_expr(*expr).pexp_desc {
                ExpressionDesc::Pexp_constant(c) => match &**c {
                    Constant::String(s, _) => Ok(vec![s.to_string()]),
                    _ => Err(default_loc),
                },
                ExpressionDesc::Pexp_tuple(exprs) => {
                    let mut result = Vec::with_capacity(exprs.len());
                    for expr in exprs.iter() {
                        let ExpressionDesc::Pexp_constant(c) = &*arena.get_expr(*expr).pexp_desc
                        else {
                            return Err(items[0].pstr_loc);
                        };
                        let Constant::String(s, _) = &**c else {
                            return Err(items[0].pstr_loc);
                        };
                        result.push(s.to_string());
                    }
                    Ok(result)
                }
                _ => Err(default_loc),
            }
        }
        _ => Err(default_loc),
    }
}

/// Extract @as("string") from attributes.
/// Mirrors OCaml's iter_process_bs_string_as.
fn get_as_string_attr(attrs: &[Attribute], arena: &ParseArena) -> Option<String> {
    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        if name == "as" {
            // Try to get string payload
            if let Some(items) = payload_str_items(payload) {
                if items.len() == 1 {
                    if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                        let (ref expr, _) = **eval_inner;
                        if let ExpressionDesc::Pexp_constant(c) = &*arena.get_expr(*expr).pexp_desc
                        {
                            if let Constant::String(s, _) = &**c {
                                return Some(s.to_string());
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

/// Extract @as(int) from attributes.
/// Mirrors OCaml's iter_process_bs_int_as.
fn get_as_int_attr(attrs: &[Attribute], arena: &ParseArena) -> Option<i64> {
    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        if name == "as" {
            // Try to get int payload
            if let Some(items) = payload_str_items(payload) {
                if items.len() == 1 {
                    if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                        let (ref expr, _) = **eval_inner;
                        if let ExpressionDesc::Pexp_constant(c) = &*arena.get_expr(*expr).pexp_desc
                        {
                            if let Constant::Integer(s, suffix) = &**c {
                                // Reject bigint suffix
                                if matches!(suffix, Some('n')) {
                                    return None;
                                }
                                return s.parse::<i64>().ok();
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

fn validate_string_as_attrs(attrs: &[Attribute], arena: &ParseArena) -> PpxResult<()> {
    let mut seen_as = false;
    for (attr_name, payload) in attrs {
        if arena.get_string(attr_name.txt) != "as" {
            continue;
        }
        if seen_as {
            return Err(PpxError::at_loc(attr_name.loc, "duplicate @as "));
        }
        if get_payload_string(payload, arena).is_none() {
            return Err(PpxError::at_loc(attr_name.loc, "expect string literal "));
        }
        seen_as = true;
    }
    Ok(())
}

fn validate_int_as_attrs(attrs: &[Attribute], arena: &ParseArena) -> PpxResult<()> {
    let mut seen_as = false;
    for (attr_name, payload) in attrs {
        if arena.get_string(attr_name.txt) != "as" {
            continue;
        }
        if seen_as {
            return Err(PpxError::at_loc(attr_name.loc, "duplicate @as "));
        }
        if get_payload_int_result(payload, arena)?.is_none() {
            return Err(PpxError::at_loc(attr_name.loc, "expect int literal "));
        }
        seen_as = true;
    }
    Ok(())
}

fn validate_string_or_int_as_attrs(attrs: &[Attribute], arena: &mut ParseArena) -> PpxResult<()> {
    let mut seen_as = false;
    for (attr_name, payload) in attrs {
        if arena.get_string(attr_name.txt) != "as" {
            continue;
        }
        if seen_as {
            return Err(PpxError::at_loc(attr_name.loc, "duplicate @as "));
        }
        if get_payload_int_result(payload, arena)?.is_some() {
            seen_as = true;
            continue;
        }
        let Some((payload, delim, loc, flow_offset)) =
            get_payload_string_with_delim_info(payload, arena)
        else {
            return Err(PpxError::at_loc(
                attr_name.loc,
                "expect int, string literal or json literal {json|text here|json} ",
            ));
        };
        if matches!(delim, Delim::DNoQuotes)
            && !matches!(
                classify_js_exp(&payload),
                JsExpClassification::JsLiteral { .. }
            )
        {
            let err = PpxError::at_loc(loc, "an object literal expected");
            return if let Some(warning) =
                raw_js_expression_parse_warning(&payload, loc, flow_offset, arena)
            {
                Err(err.with_warning(
                    warning.loc,
                    Warning::BsFfiWarning {
                        message: warning.message,
                    },
                ))
            } else {
                Err(err)
            };
        }
        seen_as = true;
    }
    Ok(())
}

fn validate_bs_string_type(typ: &CoreType, arena: &ParseArena) -> PpxResult<()> {
    let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc else {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "Not a valid type for %@string",
        ));
    };
    let (row_fields, closed, labels) = &**variant_inner;
    if !matches!(closed, current::ClosedFlag::Closed) || labels.is_some() || row_fields.is_empty() {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "Not a valid type for %@string",
        ));
    }

    enum StringRows {
        Nothing,
        Null,
        NonNull,
    }

    let mut rows = StringRows::Nothing;
    for row in row_fields {
        match (&rows, row) {
            (StringRows::Nothing | StringRows::Null, RowField::Rtag(_, attrs, true, types))
                if types.is_empty() =>
            {
                validate_string_as_attrs(attrs, arena)?;
                rows = StringRows::Null;
            }
            (StringRows::Nothing | StringRows::NonNull, RowField::Rtag(_, attrs, false, types))
                if types.len() == 1 =>
            {
                validate_string_as_attrs(attrs, arena)?;
                rows = StringRows::NonNull;
            }
            _ => {
                return Err(PpxError::at_loc(
                    typ.ptyp_loc,
                    "Not a valid type for %@string",
                ));
            }
        }
    }

    Ok(())
}

fn validate_bs_int_type(typ: &CoreType, arena: &ParseArena) -> PpxResult<()> {
    let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc else {
        return Err(PpxError::at_loc(typ.ptyp_loc, "Not a valid type for %@int"));
    };
    let (row_fields, closed, labels) = &**variant_inner;
    if !matches!(closed, current::ClosedFlag::Closed) || labels.is_some() || row_fields.is_empty() {
        return Err(PpxError::at_loc(typ.ptyp_loc, "Not a valid type for %@int"));
    }

    for row in row_fields {
        let RowField::Rtag(_, attrs, true, types) = row else {
            return Err(PpxError::at_loc(typ.ptyp_loc, "Not a valid type for %@int"));
        };
        if !types.is_empty() {
            return Err(PpxError::at_loc(typ.ptyp_loc, "Not a valid type for %@int"));
        }
        validate_int_as_attrs(attrs, arena)?;
    }

    Ok(())
}

fn validate_bs_unwrap_type(typ: &CoreType) -> PpxResult<()> {
    let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc else {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "Not a valid type for %@unwrap. Type must be an inline variant (closed), and\neach constructor must have an argument.",
        ));
    };
    let (row_fields, closed, labels) = &**variant_inner;
    if !matches!(closed, current::ClosedFlag::Closed)
        || labels.is_some()
        || row_fields.is_empty()
        || !variant_can_unwrap(row_fields)
    {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "Not a valid type for %@unwrap. Type must be an inline variant (closed), and\neach constructor must have an argument.",
        ));
    }
    Ok(())
}

/// Map polyvariant row fields to (tag_name, string_value) pairs for @string.
/// Mirrors OCaml's Ast_polyvar.map_row_fields_into_strings.
///
/// Returns (has_as, result) where has_as indicates if any @as was found.
fn map_row_fields_into_strings(
    row_fields: &[RowField],
    arena: &ParseArena,
) -> (bool, Vec<(String, String)>) {
    let mut has_as = false;
    let mut result = Vec::new();

    for rf in row_fields {
        match rf {
            RowField::Rtag(tag_loc, attrs, _nullary, _types) => {
                // Get the tag name (Label = String)
                let tag = &tag_loc.txt;

                // Check for @as("value") attribute
                let value = match get_as_string_attr(attrs, arena) {
                    Some(v) => {
                        has_as = true;
                        v
                    }
                    None => tag.to_string(),
                };

                result.push((tag.to_string(), value));
            }
            RowField::Rinherit(_) => {
                // Inherited types not supported for @string
            }
        }
    }

    (has_as, result)
}

/// Map polyvariant row fields to (tag_name, int_value) pairs for @int.
/// Mirrors OCaml's Ast_polyvar.map_row_fields_into_ints.
fn map_row_fields_into_ints(row_fields: &[RowField], arena: &ParseArena) -> Vec<(String, i64)> {
    let mut result = Vec::new();
    let mut counter: i64 = 0;

    for rf in row_fields {
        match rf {
            RowField::Rtag(tag_loc, attrs, _nullary, _types) => {
                // Get the tag name (Label = String)
                let tag = &tag_loc.txt;

                // Check for @as(int) attribute
                let value = match get_as_int_attr(attrs, arena) {
                    Some(v) => {
                        counter = v + 1; // Next default value is one more
                        v
                    }
                    None => {
                        let v = counter;
                        counter += 1;
                        v
                    }
                };

                result.push((tag.to_string(), value));
            }
            RowField::Rinherit(_) => {
                // Inherited types not supported for @int
            }
        }
    }

    result
}

/// Check if variant row fields can be unwrapped (each has exactly one payload type).
/// Mirrors OCaml's variant_can_unwrap_aux.
fn variant_can_unwrap(row_fields: &[RowField]) -> bool {
    for rf in row_fields {
        match rf {
            RowField::Rtag(_tag_loc, _attrs, false, types) if types.len() == 1 => {
                // OK: non-nullary with exactly one type
            }
            _ => return false,
        }
    }
    !row_fields.is_empty()
}

/// Determine the arg type for a type expression.
/// Mirrors OCaml's spec_of_ptyp.
fn spec_of_ptyp(nolabel: bool, typ: &CoreType, arena: &mut ParseArena) -> Attr {
    // Check for special attributes on the type (@string, @int, @unwrap, @ignore)
    let attr_type = check_type_ffi_attrs(typ, arena);

    match attr_type {
        Some("string") => {
            // @string: must be applied to a closed polyvariant
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc {
                let (ref row_fields, _, _) = **variant_inner;
                let (has_as, descr) = map_row_fields_into_strings(row_fields, arena);

                // Check if any tags are non-nullary (have payloads)
                let has_payload = row_fields.iter().any(
                    |rf| matches!(rf, RowField::Rtag(_, _, false, types) if !types.is_empty()),
                );

                if has_payload {
                    // Non-nullary: use Poly_var
                    return Attr::PolyVar {
                        descr: if has_as { Some(descr) } else { None },
                    };
                } else {
                    // All nullary: use Poly_var_string if @as was used
                    if has_as {
                        return Attr::PolyVarString { descr };
                    } else {
                        // @string without @as on nullary polyvars is redundant
                        return Attr::Nothing;
                    }
                }
            }
            // Invalid @string usage - not on closed polyvariant
            // In OCaml this raises an error, but we'll return Nothing for now
            Attr::Nothing
        }
        Some("int") => {
            // @int: must be applied to a closed polyvariant
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc {
                let (ref row_fields, _, _) = **variant_inner;
                let int_list = map_row_fields_into_ints(row_fields, arena);
                return Attr::Int(int_list);
            }
            // Invalid @int usage
            Attr::Nothing
        }
        Some("ignore") => Attr::Ignore,
        Some("unwrap") => {
            // @unwrap: must be applied to a closed polyvariant where each tag has exactly one payload
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc {
                let (ref row_fields, _, _) = **variant_inner;
                if variant_can_unwrap(row_fields) {
                    return Attr::Unwrap;
                }
            }
            // Invalid @unwrap usage
            Attr::Nothing
        }
        _ => {
            // No special attribute - default behavior
            // Check if unit type
            match &*typ.ptyp_desc {
                CoreTypeDesc::Ptyp_constr(inner) if inner.1.is_empty() => {
                    let (ref lid, ref args) = **inner;
                    let longident = arena.get_longident(lid.txt);
                    if matches!(longident, Longident::Lident(s) if arena.get_string(*s) == "unit") {
                        if nolabel {
                            return Attr::ExternUnit;
                        }
                    }
                    Attr::Nothing
                }
                _ => Attr::Nothing,
            }
        }
    }
}

/// Check if a type is unit
fn is_unit_type(typ: &CoreType, arena: &ParseArena) -> bool {
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            args.is_empty() && {
                let longident = arena.get_longident(lid.txt);
                matches!(longident, Longident::Lident(s) if arena.get_string(*s) == "unit")
            }
        }
        _ => false,
    }
}

fn is_user_option_type(typ: &CoreType, arena: &ParseArena) -> bool {
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            if args.len() != 1 {
                return false;
            }
            match arena.get_longident(lid.txt) {
                Longident::Lident(name) => arena.get_string(*name) == "option",
                Longident::Ldot(parent, name) => {
                    let Longident::Lident(parent_name) = parent.as_ref() else {
                        return false;
                    };
                    arena.get_string(*parent_name) == "*predef*"
                        && arena.get_string(*name) == "option"
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// Deconstruct an arrow type into a list of args and the result type.
/// This mirrors OCaml's `Ast_core_type.list_of_arrow`:
/// ```ocaml
/// let rec aux (ty : t) acc =
///   match ty.ptyp_desc with
///   | Ptyp_arrow {arg; ret; arity} when arity = None || acc = [] ->
///     aux ret (arg :: acc)
///   | _ -> (ty, List.rev acc)
/// ```
/// The guard `arity = None || acc = []` means:
/// - Always descend for the first arrow (acc is empty)
/// - For subsequent arrows, only descend if arity is None
fn list_of_arrow(typ: &CoreType, arena: &ParseArena) -> (Vec<TypeArg>, CoreType) {
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, arity) = &**inner;
            (
                arena.nary_arrow_args(arg, *arity).into_owned(),
                arena.get_core_type(*ret).clone(),
            )
        }
        _ => (Vec::new(), typ.clone()),
    }
}

/// Reconstruct an arrow type with a new location, matching OCaml's `Ast_helper.Typ.arrows ~loc`.
///
/// OCaml's FFI processing deconstructs the parsed arrow type and reconstructs it
/// with `ptyp_loc = pval_loc`. This changes the location of the outermost arrow chain
/// from the original type span to the full value description span.
///
/// The individual argument types and result type are preserved unchanged.
fn reconstruct_arrow_type_with_loc(
    typ: &CoreType,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> CoreType {
    let (args, result) = list_of_arrow(typ, arena);
    if args.is_empty() {
        // Not an arrow type, return as-is
        return typ.clone();
    }

    // Filter out @as(_) constant params (OCaml: Arg_cst _ -> arg_types, skips param)
    let mut filtered_args: Vec<&TypeArg> = Vec::new();
    let mut had_args = false;
    for arg in &args {
        had_args = true;
        let nolabel = matches!(arg.lbl, ArgLabel::Nolabel);
        let is_labelled = matches!(arg.lbl, ArgLabel::Labelled(_));
        let arg_typ = arena.get_core_type(arg.typ).clone();
        let arg_type = refine_arg_type(nolabel, &arg_typ, arena);
        if matches!(arg_type, Attr::ArgCst(_)) && (nolabel || is_labelled) {
            // Skip this param - it's an @as(_) constant arg
            continue;
        }
        filtered_args.push(arg);
    }

    // If all args were erased but we had some originally, add a unit param
    // (OCaml: match (args, arg_type_specs_length) with | [], n when n > 0 -> ...)
    if filtered_args.is_empty() && had_args {
        let unit_lid = arena.push_lident_static("unit");
        let unit_type = CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                Located {
                    txt: unit_lid,
                    loc: loc,
                },
                vec![],
            )))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        };
        let arity = arena.push_arity(Some(1));
        let unit_arg = TypeArg {
            attrs: Attributes::new(),
            lbl: ArgLabel::Nolabel,
            typ: arena.push_core_type(unit_type),
        };
        return CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
                Box::new(unit_arg),
                arena.push_core_type(result.clone()),
                arity,
            )))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        };
    }

    let args = filtered_args.into_iter().cloned().collect::<Vec<_>>();
    let arity = arena.push_arity(Some(args.len() as i32));
    let first = args[0].clone();
    arena.set_nary_arrow_args(arity, args);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(first),
            arena.push_core_type(result),
            arity,
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Process an @obj external declaration, transforming the type.
///
/// When @obj is present and the return type is Ptyp_any, this function
/// builds a Ptyp_object from the labeled arguments.
///
/// Mirrors OCaml's `process_obj` in ast_external_process.ml.
fn process_obj_type(
    typ: &CoreType,
    loc: LocIdx,
    attrs: &[Attribute],
    arena: &mut ParseArena,
) -> CoreType {
    // Only process if @obj attribute is present
    if !has_obj_attr(attrs, arena) {
        return reconstruct_arrow_type_with_loc(typ, loc, arena);
    }

    let (args, result) = list_of_arrow(typ, arena);
    if args.is_empty() {
        return typ.clone();
    }

    // Check if result type is Ptyp_any
    let result_is_any = matches!(&*result.ptyp_desc, CoreTypeDesc::Ptyp_any);

    // Build result_types (object fields) from labeled arguments
    // Mirrors OCaml's fold_right in process_obj
    let mut filtered_args: Vec<&TypeArg> = Vec::new();
    let mut result_types: Vec<ObjectField> = Vec::new();

    for arg in &args {
        let nolabel = matches!(arg.lbl, ArgLabel::Nolabel);

        match &arg.lbl {
            ArgLabel::Nolabel => {
                // Nolabel args in @obj: only unit is allowed, doesn't contribute to result_types
                filtered_args.push(arg);
            }
            ArgLabel::Labelled(label_loc) => {
                // Labeled args: check for @as("alias") and arg type
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name =
                    get_as_string_attr(&arg.attrs, arena).unwrap_or_else(|| label_name.clone());

                let arg_typ = arena.get_core_type(arg.typ).clone();
                let arg_type = refine_arg_type(false, &arg_typ, arena);

                match arg_type {
                    Attr::Ignore => {
                        // @ignore: skip from result_types
                        filtered_args.push(arg);
                    }
                    Attr::ArgCst(_) => {
                        // @as(_) constant: skip from arg_types, skip from result_types
                        // (doesn't appear in function signature)
                    }
                    Attr::Nothing => {
                        // Regular arg: add to result_types with original type
                        filtered_args.push(arg);
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc: loc,
                            },
                            Attributes::new(),
                            arg.typ.clone(),
                        ));
                    }
                    Attr::Int(_) => {
                        // @int polyvariant: add to result_types with int type
                        filtered_args.push(arg);
                        let int_lid = arena.push_lident_static("int");
                        let int_type = CoreType {
                            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                                Located { txt: int_lid, loc },
                                vec![],
                            )))),
                            ptyp_loc: loc,
                            ptyp_attributes: Attributes::new(),
                        };
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc: loc,
                            },
                            Attributes::new(),
                            arena.push_core_type(int_type),
                        ));
                    }
                    Attr::PolyVarString { .. } => {
                        // @string polyvariant: add to result_types with string type
                        filtered_args.push(arg);
                        let string_lid = arena.push_lident_static("string");
                        let string_type = CoreType {
                            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                                Located {
                                    txt: string_lid,
                                    loc,
                                },
                                vec![],
                            )))),
                            ptyp_loc: loc,
                            ptyp_attributes: Attributes::new(),
                        };
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc: loc,
                            },
                            Attributes::new(),
                            arena.push_core_type(string_type),
                        ));
                    }
                    Attr::PolyVar { .. } | Attr::Unwrap | Attr::ExternUnit => {
                        // These are errors in OCaml but we'll just add the original type
                        filtered_args.push(arg);
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc: loc,
                            },
                            Attributes::new(),
                            arg.typ.clone(),
                        ));
                    }
                }
            }
            ArgLabel::Optional(label_loc) => {
                // Optional args: add to result_types with Js.undefined wrapper
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name =
                    get_as_string_attr(&arg.attrs, arena).unwrap_or_else(|| label_name.clone());

                let arg_typ = arena.get_core_type(arg.typ).clone();
                let arg_type = get_opt_arg_type_unchecked(false, &arg_typ, arena);

                match arg_type {
                    Attr::Ignore => {
                        // @ignore: skip from result_types
                        filtered_args.push(arg);
                    }
                    Attr::ArgCst(_) => {
                        // OCaml raises error for @as with optional in @obj
                        // We'll skip for now
                        filtered_args.push(arg);
                    }
                    Attr::Nothing => {
                        // Regular optional: wrap type in Js.undefined
                        filtered_args.push(arg);
                        let arg_typ = arena.get_core_type(arg.typ).clone();
                        let wrapped_type = to_undefined_type(&arg_typ, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc: loc,
                            },
                            Attributes::new(),
                            arena.push_core_type(wrapped_type),
                        ));
                    }
                    Attr::Int(_) => {
                        // @int optional: wrap int in Js.undefined
                        filtered_args.push(arg);
                        let int_lid = arena.push_lident_static("int");
                        let int_type = CoreType {
                            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                                Located { txt: int_lid, loc },
                                vec![],
                            )))),
                            ptyp_loc: loc,
                            ptyp_attributes: Attributes::new(),
                        };
                        let wrapped_type = to_undefined_type(&int_type, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc: loc,
                            },
                            Attributes::new(),
                            arena.push_core_type(wrapped_type),
                        ));
                    }
                    Attr::PolyVarString { .. } => {
                        // @string optional: wrap string in Js.undefined
                        filtered_args.push(arg);
                        let string_lid = arena.push_lident_static("string");
                        let string_type = CoreType {
                            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                                Located {
                                    txt: string_lid,
                                    loc,
                                },
                                vec![],
                            )))),
                            ptyp_loc: loc,
                            ptyp_attributes: Attributes::new(),
                        };
                        let wrapped_type = to_undefined_type(&string_type, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc: loc,
                            },
                            Attributes::new(),
                            arena.push_core_type(wrapped_type),
                        ));
                    }
                    _ => {
                        // Other types: add with undefined wrapper
                        filtered_args.push(arg);
                        let arg_typ = arena.get_core_type(arg.typ).clone();
                        let wrapped_type = to_undefined_type(&arg_typ, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc: loc,
                            },
                            Attributes::new(),
                            arena.push_core_type(wrapped_type),
                        ));
                    }
                }
            }
        }
    }

    // If result type is Ptyp_any, build Ptyp_object from result_types
    // Even if result_types is empty, we still build an empty closed object
    let final_result = if result_is_any {
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_object(Box::new((
                result_types,
                current::ClosedFlag::Closed,
            )))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        }
    } else {
        result.clone()
    };

    // Rebuild the arrow chain
    if filtered_args.is_empty() {
        return final_result;
    }

    let args = filtered_args.into_iter().cloned().collect::<Vec<_>>();
    let arity = arena.push_arity(Some(args.len() as i32));
    let first = args[0].clone();
    let ret = arena.push_core_type(final_result);
    arena.set_nary_arrow_args(arity, args);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(first),
            ret,
            arity,
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Get optional arg type (for Optional labels).
/// Mirrors OCaml's get_opt_arg_type.
fn get_opt_arg_type(nolabel: bool, typ: &CoreType, arena: &ParseArena) -> PpxResult<Attr> {
    if matches!(&*typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "_ is not allowed in combination with external optional type",
        ));
    }
    Ok(get_opt_arg_type_unchecked(nolabel, typ, arena))
}

/// Same classifier after the validation pass has already rejected Ptyp_any.
fn get_opt_arg_type_unchecked(_nolabel: bool, typ: &CoreType, arena: &ParseArena) -> Attr {
    let attr_type = check_type_ffi_attrs(typ, arena);
    match attr_type {
        Some("ignore") => Attr::Ignore,
        Some("int") => {
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc {
                let (row_fields, closed_flag, labels_opt) = &**variant_inner;
                if matches!(closed_flag, current::ClosedFlag::Closed) && labels_opt.is_none() {
                    let int_list = map_row_fields_into_ints(row_fields, arena);
                    return Attr::Int(int_list);
                }
            }
            Attr::Nothing
        }
        Some("string") => {
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc {
                let (row_fields, closed_flag, labels_opt) = &**variant_inner;
                if matches!(closed_flag, current::ClosedFlag::Closed) && labels_opt.is_none() {
                    let (has_as, descr) = map_row_fields_into_strings(row_fields, arena);
                    let has_payload = row_fields.iter().any(
                        |rf| matches!(rf, RowField::Rtag(_, _, false, types) if !types.is_empty()),
                    );

                    if has_payload {
                        return Attr::PolyVar {
                            descr: if has_as { Some(descr) } else { None },
                        };
                    }

                    if has_as {
                        return Attr::PolyVarString { descr };
                    }
                }
            }
            Attr::Nothing
        }
        Some("unwrap") => {
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &*typ.ptyp_desc {
                let (row_fields, closed_flag, _labels_opt) = &**variant_inner;
                if matches!(closed_flag, current::ClosedFlag::Closed)
                    && variant_can_unwrap(row_fields)
                {
                    return Attr::Unwrap;
                }
            }
            Attr::Nothing
        }
        _ => Attr::Nothing,
    }
}

/// Wrap a type in Js.undefined<T>.
/// Mirrors OCaml's Ast_comb.to_undefined_type.
fn to_undefined_type(typ: &CoreType, loc: LocIdx, arena: &mut ParseArena) -> CoreType {
    // Build Js.undefined<typ>
    let js_str = arena.push_string("Js".to_string());
    let undefined_str = arena.push_string("undefined".to_string());
    let longident = arena.push_longident(Longident::Ldot(
        Box::new(Longident::Lident(js_str)),
        undefined_str,
    ));

    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: longident,
                loc,
            },
            vec![arena.push_core_type(typ.clone())],
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Parse external attributes to determine FFI encoding details
#[derive(Debug)]
struct ExternalDesc {
    val_name: Option<String>,
    module_as_val: bool,                         // @module with no payload
    external_module_name: Option<String>,        // @module("name") with string payload
    module_bind_name: Option<String>,            // @module("name", "bind") second string
    import_attributes: Option<ImportAttributes>, // @module({from, with})
    call_name: Option<String>,
    send_name: Option<String>,
    new_name: Option<String>,
    new_name_from_payload: bool,
    get_name: Option<String>,
    set_name: Option<String>,
    get_index: bool,
    set_index: bool,
    splice: bool,
    scopes: Vec<String>,
    return_wrapper: ReturnWrapper,
    mk_obj: bool,
}

impl Default for ExternalDesc {
    fn default() -> Self {
        Self {
            val_name: None,
            module_as_val: false,
            external_module_name: None,
            module_bind_name: None,
            import_attributes: None,
            call_name: None,
            send_name: None,
            new_name: None,
            new_name_from_payload: false,
            get_name: None,
            set_name: None,
            get_index: false,
            set_index: false,
            splice: false,
            scopes: Vec::new(),
            return_wrapper: ReturnWrapper::ReturnUnset,
            mk_obj: false,
        }
    }
}

fn parse_external_attrs(
    attrs: &[Attribute],
    prim_name: &str,
    no_arguments: bool,
    pval_loc: LocIdx,
    arena: &ParseArena,
) -> ExternalDesc {
    let mut desc = ExternalDesc::default();

    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        if name == "genType.import" || name == "gentype.import" {
            // Match OCaml ast_external_process.parse_external_attributes:
            // @genType.import/@gentype.import rewrites externals to import from
            // "./<basename>.gen", which must be treated as a relative module path.
            let input_name = arena.get_string(arena.to_location(pval_loc).loc_start.file_name);
            let basename = std::path::Path::new(input_name)
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or(input_name);
            let stem = basename
                .rsplit_once('.')
                .map(|(name, _)| name)
                .unwrap_or(basename);
            desc.external_module_name = Some(format!("./{stem}.gen"));
            desc.module_bind_name = None;
            desc.import_attributes = None;
            continue;
        }
        match name {
            "val" => {
                let name =
                    get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string());
                if no_arguments {
                    desc.val_name = Some(name);
                } else {
                    desc.call_name = Some(name);
                }
            }
            "module" => {
                if let Some((bundle, import_attributes)) =
                    get_module_import_attributes(payload, arena)
                {
                    desc.external_module_name = Some(bundle);
                    desc.module_bind_name = None;
                    desc.import_attributes = Some(import_attributes);
                    continue;
                }

                let strings = get_payload_strings(payload, arena);
                match strings.len() {
                    0 => {
                        // @module with no payload - module_as_val, bundle = prim_name
                        desc.module_as_val = true;
                    }
                    1 => {
                        // @module("name") - sets external_module_name
                        desc.external_module_name = Some(strings[0].clone());
                        desc.module_bind_name = None;
                        desc.import_attributes = None;
                    }
                    2 => {
                        // @module("bundle", "bind_name") - sets external_module_name with bind name
                        desc.external_module_name = Some(strings[0].clone());
                        desc.module_bind_name = Some(strings[1].clone());
                        desc.import_attributes = None;
                    }
                    _ => {}
                }
            }
            "send" => {
                desc.send_name = Some(
                    get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()),
                );
            }
            "new" => {
                let payload_name = get_payload_string(payload, arena);
                desc.new_name_from_payload = payload_name.is_some();
                desc.new_name = Some(payload_name.unwrap_or_else(|| prim_name.to_string()));
            }
            "get" => {
                desc.get_name = Some(
                    get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()),
                );
            }
            "set" => {
                desc.set_name = Some(
                    get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()),
                );
            }
            "get_index" => {
                desc.get_index = true;
            }
            "set_index" => {
                desc.set_index = true;
            }
            "variadic" => {
                desc.splice = true;
            }
            "scope" => {
                let scopes = get_payload_strings(payload, arena);
                if !scopes.is_empty() {
                    desc.scopes = scopes;
                }
            }
            "return" => {
                if let Some(wrapper_str) = get_return_wrapper_config(payload, arena) {
                    desc.return_wrapper = match wrapper_str.as_str() {
                        "null_to_opt" => ReturnWrapper::ReturnNullToOpt,
                        "nullable" | "null_undefined_to_opt" => {
                            ReturnWrapper::ReturnNullUndefinedToOpt
                        }
                        "identity" => ReturnWrapper::ReturnIdentity,
                        _ => ReturnWrapper::ReturnUnset,
                    };
                }
            }
            "obj" => {
                desc.mk_obj = true;
            }
            _ => {}
        }
    }

    // Default: if no specific attr, treat as @val for a call
    if desc.val_name.is_none()
        && desc.call_name.is_none()
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.get_name.is_none()
        && desc.set_name.is_none()
        && !desc.get_index
        && !desc.set_index
        && !desc.module_as_val
        && desc.external_module_name.is_none()
        && !desc.mk_obj
    {
        // Default to Js_call with the prim name
        desc.call_name = Some(prim_name.to_string());
    }

    desc
}

/// Extract string from attribute payload (simplified)
fn get_payload_string(payload: &current::Payload, arena: &ParseArena) -> Option<String> {
    match payload {
        current::Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (ref expr, _) = **eval_inner;
                match &*arena.get_expr(*expr).pexp_desc {
                    ExpressionDesc::Pexp_constant(c) => {
                        if let current::Constant::String(s, _) = &**c {
                            return Some(s.to_string());
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract return-wrapper config from payload.
/// Mirrors OCaml's Ast_payload.ident_or_record_as_config shape used by
/// ast_external_process.ml for `@return`:
/// - `@return(nullable)` -> `nullable`
/// - `@return({null_to_opt: null_to_opt})` -> `null_to_opt`
/// Non-punned record entries are intentionally rejected here.
fn get_return_wrapper_config(payload: &current::Payload, arena: &ParseArena) -> Option<String> {
    let current::Payload::PStr(items) = payload else {
        return None;
    };
    if items.len() != 1 {
        return None;
    }
    let StructureItemDesc::Pstr_eval(inner) = &*items[0].pstr_desc else {
        return None;
    };
    let (expr_idx, _) = &**inner;
    let expr = arena.get_expr(*expr_idx);

    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => {
            let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
                return None;
            };
            Some(arena.get_string(*name_idx).to_string())
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, with_obj) = &**inner;
            if with_obj.is_some() || fields.len() != 1 {
                return None;
            }
            let field = &fields[0];
            let Longident::Lident(field_name_idx) = arena.get_longident(field.lid.txt) else {
                return None;
            };
            let field_expr = arena.get_expr(field.expr);
            let ExpressionDesc::Pexp_ident(value_lid) = &*field_expr.pexp_desc else {
                return None;
            };
            let Longident::Lident(value_name_idx) = arena.get_longident(value_lid.txt) else {
                return None;
            };
            if arena.get_string(*field_name_idx) == arena.get_string(*value_name_idx) {
                Some(arena.get_string(*field_name_idx).to_string())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn validate_return_wrapper_config_shape(
    payload: &current::Payload,
    arena: &ParseArena,
) -> PpxResult<()> {
    let current::Payload::PStr(items) = payload else {
        return Ok(());
    };
    if items.len() != 1 {
        return Ok(());
    }
    let StructureItemDesc::Pstr_eval(inner) = &*items[0].pstr_desc else {
        return Ok(());
    };
    let (expr_idx, _) = &**inner;
    let expr = arena.get_expr(*expr_idx);
    let ExpressionDesc::Pexp_record(inner) = &*expr.pexp_desc else {
        return Ok(());
    };
    let (fields, with_obj) = &**inner;
    if with_obj.is_some() {
        return Ok(());
    }
    for field in fields {
        if !matches!(arena.get_longident(field.lid.txt), Longident::Lident(_)) {
            return Err(PpxError::at_loc(
                expr.pexp_loc,
                "Qualified label is not allowed",
            ));
        }
    }
    Ok(())
}

fn return_wrapper_config_warning(
    payload: &current::Payload,
    arena: &ParseArena,
    default_loc: LocIdx,
) -> Option<(LocIdx, &'static str)> {
    let current::Payload::PStr(items) = payload else {
        return Some((default_loc, "invalid attribute config-record, ignoring"));
    };
    if items.is_empty() {
        return None;
    }
    if items.len() != 1 {
        return Some((default_loc, "invalid attribute config-record, ignoring"));
    }
    let StructureItemDesc::Pstr_eval(inner) = &*items[0].pstr_desc else {
        return Some((default_loc, "invalid attribute config-record, ignoring"));
    };
    let (expr_idx, _) = &**inner;
    let expr = arena.get_expr(*expr_idx);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_record(inner) => {
            let (_fields, with_obj) = &**inner;
            with_obj
                .is_some()
                .then_some((expr.pexp_loc, "`with` is not supported, discarding"))
        }
        ExpressionDesc::Pexp_ident(lid)
            if matches!(arena.get_longident(lid.txt), Longident::Lident(_)) =>
        {
            None
        }
        _ => Some((default_loc, "invalid attribute config-record, ignoring")),
    }
}

/// Extract integer from attribute payload (mirrors OCaml's Ast_payload.is_single_int)
fn get_payload_int_result(
    payload: &current::Payload,
    arena: &ParseArena,
) -> PpxResult<Option<i32>> {
    match payload {
        current::Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (ref expr, _) = **eval_inner;
                if let ExpressionDesc::Pexp_constant(c) = &*arena.get_expr(*expr).pexp_desc {
                    if let current::Constant::Integer(name, suffix) = &**c {
                        // OCaml's is_single_int rejects 'n' suffix (bigint)
                        if matches!(suffix, Some('n')) {
                            return Ok(None);
                        }
                        return name
                            .parse::<i32>()
                            .map(Some)
                            .map_err(|_| PpxError::int_of_string_failure());
                    }
                }
            }
            Ok(None)
        }
        _ => Ok(None),
    }
}

fn get_payload_int(payload: &current::Payload, arena: &ParseArena) -> Option<i32> {
    get_payload_int_result(payload, arena).ok().flatten()
}

/// Extract string with delimiter from attribute payload.
/// Mirrors OCaml's string extraction in iter_process_bs_string_or_int_as,
/// including the parse_processed_delim logic that converts raw string delimiters
/// to FFI Delim values.
///
/// The OCaml PPX pipeline rewrites all plain string delimiters (None → Some "*j")
/// before external processing, so we need to apply the same transformation here.
fn get_payload_string_with_delim(
    payload: &current::Payload,
    arena: &ParseArena,
) -> Option<(String, Delim)> {
    get_payload_string_with_delim_info(payload, arena).map(|(s, delim, _loc, _offset)| (s, delim))
}

fn get_payload_string_with_delim_info(
    payload: &current::Payload,
    arena: &ParseArena,
) -> Option<(String, Delim, LocIdx, i32)> {
    match payload {
        current::Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (ref expr, _) = **eval_inner;
                let expr = arena.get_expr(*expr);
                if let ExpressionDesc::Pexp_constant(c) = &*expr.pexp_desc {
                    if let current::Constant::String(s, raw_delim) = &**c {
                        // Apply parse_processed_delim logic:
                        // In OCaml, strings get rewritten: None → "*j", then
                        // parse_processed_delim maps: None→DNone, "*j"→DStarJ, "json"→DNoQuotes, "bq"→DBackQuotes
                        // Rust parser uses "js" for plain strings (equivalent to OCaml's None → "*j" rewrite)
                        let delim = match raw_delim.as_deref() {
                            None => Delim::DStarJ,       // None → rewritten to "*j" → DStarJ
                            Some("js") => Delim::DStarJ, // Rust parser's plain string delimiter
                            Some("*j") => Delim::DStarJ, // Already rewritten (OCaml format)
                            Some("json") => Delim::DNoQuotes,
                            Some("bq") => Delim::DBackQuotes,
                            Some("j") => Delim::DStarJ, // "j" delimiter → DStarJ
                            _ => return None,           // Unrecognized delimiter
                        };
                        let flow_offset = match raw_delim {
                            None => 1,
                            Some(delim) => delim.len() as i32 + 2,
                        };
                        return Some((s.to_string(), delim, expr.pexp_loc, flow_offset));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract multiple strings from attribute payload (mirrors OCaml's Ast_payload.assert_strings)
/// Handles: @attr("str"), @attr(("str1", "str2", ...)), @attr (empty → [])
fn get_payload_strings(payload: &current::Payload, arena: &ParseArena) -> Vec<String> {
    payload_string_literals(payload, arena).unwrap_or_default()
}

fn validate_module_import_attributes_payload(
    payload: &current::Payload,
    arena: &ParseArena,
) -> PpxResult<bool> {
    let current::Payload::PStr(items) = payload else {
        return Ok(false);
    };
    if items.len() != 1 {
        return Ok(false);
    }
    let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc else {
        return Ok(false);
    };
    let (expr_idx, _) = &**eval_inner;
    let expr = arena.get_expr(*expr_idx);
    let ExpressionDesc::Pexp_record(record_inner) = &*expr.pexp_desc else {
        return Ok(false);
    };
    let (fields, _) = &**record_inner;

    let mut from_name = false;
    let mut with_fields: Option<&[ExpressionRecordField]> = None;

    for field in fields {
        let Longident::Lident(field_name_idx) = arena.get_longident(field.lid.txt) else {
            continue;
        };
        match arena.get_string(*field_name_idx) {
            "from" => {
                let field_expr = arena.get_expr(field.expr);
                if let ExpressionDesc::Pexp_constant(c) = &*field_expr.pexp_desc {
                    if matches!(&**c, current::Constant::String(_, _)) {
                        from_name = true;
                    }
                }
            }
            "with" => {
                let field_expr = arena.get_expr(field.expr);
                if let ExpressionDesc::Pexp_record(with_inner) = &*field_expr.pexp_desc {
                    let (import_fields, _) = &**with_inner;
                    with_fields = Some(import_fields.as_slice());
                }
            }
            _ => {}
        }
    }

    if !from_name {
        return Err(PpxError::at_loc(
            expr.pexp_loc,
            "@module annotations with import attributes must have a \"from\" field. This \"from\" field should point to the JS module to import, just like the string payload to @module normally does.",
        ));
    }

    let Some(with_fields) = with_fields else {
        return Err(PpxError::at_loc(
            expr.pexp_loc,
            "@module annotations with import attributes must have a \"with\" field. This \"with\" field should hold a record of the import attributes you want applied to the import.",
        ));
    };

    for field in with_fields {
        let field_expr = arena.get_expr(field.expr);
        let Longident::Lident(_) = arena.get_longident(field.lid.txt) else {
            return Err(PpxError::at_loc(
                field_expr.pexp_loc,
                "Field must be a regular key.",
            ));
        };
        let ExpressionDesc::Pexp_constant(c) = &*field_expr.pexp_desc else {
            return Err(PpxError::at_loc(
                field_expr.pexp_loc,
                "Only string values are allowed here.",
            ));
        };
        if !matches!(&**c, current::Constant::String(_, _)) {
            return Err(PpxError::at_loc(
                field_expr.pexp_loc,
                "Only string values are allowed here.",
            ));
        }
    }

    Ok(true)
}

/// Extract `@module({from: "...", with: {...}})` payload.
/// Mirrors OCaml `ast_external_process.ml` record-payload path in `parse_external_attributes`.
fn get_module_import_attributes(
    payload: &current::Payload,
    arena: &ParseArena,
) -> Option<(String, ImportAttributes)> {
    let current::Payload::PStr(items) = payload else {
        return None;
    };
    if items.len() != 1 {
        return None;
    }
    let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc else {
        return None;
    };
    let (expr_idx, _) = &**eval_inner;
    let expr = arena.get_expr(*expr_idx);
    let ExpressionDesc::Pexp_record(record_inner) = &*expr.pexp_desc else {
        return None;
    };
    let (fields, _) = &**record_inner;

    let mut from_name: Option<String> = None;
    let mut with_fields: Option<ImportAttributes> = None;

    for field in fields {
        let Longident::Lident(field_name_idx) = arena.get_longident(field.lid.txt) else {
            continue;
        };
        match arena.get_string(*field_name_idx) {
            "from" => {
                let field_expr = arena.get_expr(field.expr);
                if let ExpressionDesc::Pexp_constant(c) = &*field_expr.pexp_desc {
                    if let current::Constant::String(s, _) = &**c {
                        from_name = Some(s.to_string());
                    }
                }
            }
            "with" => {
                let field_expr = arena.get_expr(field.expr);
                let ExpressionDesc::Pexp_record(with_inner) = &*field_expr.pexp_desc else {
                    continue;
                };
                let (import_fields, _) = &**with_inner;
                let mut import_attributes: ImportAttributes =
                    Vec::with_capacity(import_fields.len());
                for import_field in import_fields {
                    let Longident::Lident(key_idx) = arena.get_longident(import_field.lid.txt)
                    else {
                        continue;
                    };
                    let import_field_expr = arena.get_expr(import_field.expr);
                    let ExpressionDesc::Pexp_constant(c) = &*import_field_expr.pexp_desc else {
                        continue;
                    };
                    let current::Constant::String(value, _) = &**c else {
                        continue;
                    };
                    let key = match arena.get_string(*key_idx) {
                        "type_" => "type".to_string(),
                        key => key.to_string(),
                    };
                    import_attributes.push((key, value.to_string()));
                }
                with_fields = Some(import_attributes);
            }
            _ => {}
        }
    }

    match (from_name, with_fields) {
        (Some(from_name), Some(with_fields)) => Some((from_name, with_fields)),
        _ => None,
    }
}

/// Build FFI type from external description and type info
fn build_ffi_type(
    desc: &ExternalDesc,
    prim_name: &str,
    arity: usize,
    result_is_unit: bool,
    params: Params,
) -> FfiType {
    // Determine return wrapper
    let return_wrapper =
        if result_is_unit && matches!(desc.return_wrapper, ReturnWrapper::ReturnUnset) {
            ReturnWrapper::ReturnReplacedWithUnit
        } else {
            desc.return_wrapper.clone()
        };

    // Build ExternalModuleName from desc.external_module_name if present
    // (this is @module("name") or @module("name", "bind") with string payload)
    let external_module_name =
        desc.external_module_name
            .as_ref()
            .map(|bundle| ExternalModuleName {
                bundle: bundle.clone(),
                module_bind_name: match &desc.module_bind_name {
                    Some(name) => ModuleBindName::PhintName(name.clone()),
                    None => ModuleBindName::PhintNothing,
                },
                import_attributes: desc.import_attributes.clone(),
            });

    // Determine external spec based on attributes
    // Priority follows OCaml's external_desc_of_non_obj pattern matching
    let external_spec = if desc.get_index {
        ExternalSpec::JsGetIndex {
            js_get_index_scopes: desc.scopes.clone(),
        }
    } else if desc.set_index {
        ExternalSpec::JsSetIndex {
            js_set_index_scopes: desc.scopes.clone(),
        }
    } else if desc.module_as_val {
        // @module with no payload: module_as_val
        // OCaml: module_as_val = Some external_module_name
        let emn = ExternalModuleName {
            bundle: prim_name.to_string(),
            module_bind_name: ModuleBindName::PhintNothing,
            import_attributes: None,
        };
        if arity == 0 {
            // No args → Js_module_as_var
            ExternalSpec::JsModuleAsVar(emn)
        } else if let Some(ref _new_name) = desc.new_name {
            // @new + @module → Js_module_as_class
            ExternalSpec::JsModuleAsClass(emn)
        } else {
            // Has args, no @new → Js_module_as_fn
            ExternalSpec::JsModuleAsFn {
                external_module_name: emn,
                splice: desc.splice,
            }
        }
    } else if let Some(ref name) = desc.send_name {
        ExternalSpec::JsSend {
            name: name.clone(),
            splice: desc.splice,
            js_send_scopes: desc.scopes.clone(),
        }
    } else if let Some(ref name) = desc.new_name {
        ExternalSpec::JsNew {
            name: name.clone(),
            external_module_name: external_module_name.clone(),
            splice: desc.splice,
            scopes: desc.scopes.clone(),
        }
    } else if let Some(ref name) = desc.get_name {
        ExternalSpec::JsGet {
            js_get_name: name.clone(),
            js_get_scopes: desc.scopes.clone(),
        }
    } else if let Some(ref name) = desc.set_name {
        ExternalSpec::JsSet {
            js_set_name: name.clone(),
            js_set_scopes: desc.scopes.clone(),
        }
    } else if let Some(ref name) = desc.val_name {
        // @val - always Js_var
        ExternalSpec::JsVar {
            name: name.clone(),
            external_module_name: external_module_name.clone(),
            scopes: desc.scopes.clone(),
        }
    } else if let Some(ref name) = desc.call_name {
        // Explicit call_name (set as default when no specific attr)
        if arity == 0 {
            ExternalSpec::JsVar {
                name: name.clone(),
                external_module_name: external_module_name.clone(),
                scopes: desc.scopes.clone(),
            }
        } else {
            ExternalSpec::JsCall {
                name: name.clone(),
                external_module_name,
                splice: desc.splice,
                scopes: desc.scopes.clone(),
            }
        }
    } else if external_module_name.is_some() {
        // @module("name") with payload but no other specific attr
        let name = prim_name.to_string();
        if arity == 0 {
            ExternalSpec::JsVar {
                name,
                external_module_name,
                scopes: desc.scopes.clone(),
            }
        } else {
            ExternalSpec::JsCall {
                name,
                external_module_name,
                splice: desc.splice,
                scopes: desc.scopes.clone(),
            }
        }
    } else if arity == 0 {
        // No args = Js_var
        ExternalSpec::JsVar {
            name: prim_name.to_string(),
            external_module_name: None,
            scopes: desc.scopes.clone(),
        }
    } else {
        // Default: Js_call
        ExternalSpec::JsCall {
            name: prim_name.to_string(),
            external_module_name: None,
            splice: desc.splice,
            scopes: desc.scopes.clone(),
        }
    };

    FfiType::FfiBs {
        params,
        return_wrapper,
        external_spec,
    }
}

/// Check if an external value description has relative paths that require
/// wrapping in Pstr_include to prevent cross-module inlining.
fn check_external_relative(vd: &ValueDescription, arena: &mut ParseArena) -> bool {
    let prim_name = match vd.pval_prim.first() {
        Some(name) => arena.get_string(*name).to_string(),
        None => return false,
    };
    if !is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return false;
    }
    let vd_type = arena.get_core_type(vd.pval_type).clone();
    let (params, arity) = build_arg_type_specs(&vd_type, arena);
    let (args, result_type) = list_of_arrow(&vd_type, arena);
    let no_arguments = args.is_empty();
    let desc = parse_external_attrs(
        &vd.pval_attributes,
        prim_name.as_str(),
        no_arguments,
        vd.pval_loc,
        arena,
    );
    let result_is_unit = is_unit_type(&result_type, arena);
    let ffi = build_ffi_type(&desc, prim_name.as_str(), arity, result_is_unit, params);
    check_ffi_relative(&ffi)
}

/// Check if a path string is a package-relative path (starts with "./" or "../").
fn is_package_relative_path(s: &str) -> bool {
    s.starts_with("./") || s.starts_with("../")
}

fn valid_js_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '$'
}

fn valid_first_js_char(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || c == '$'
}

fn valid_ident(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    valid_js_char(first) && valid_first_js_char(first) && chars.all(valid_js_char)
}

fn validate_global_name(name: &str, loc: LocIdx) -> PpxResult<()> {
    if valid_ident(name) || name.split('.').all(valid_ident) {
        return Ok(());
    }
    Err(PpxError::at_loc(
        loc,
        format!("Not a valid global name {name}"),
    ))
}

fn validate_external_module_name(
    module_name: &ExternalModuleName,
    loc: Option<LocIdx>,
) -> PpxResult<()> {
    if module_name.bundle.is_empty()
        || matches!(
            &module_name.module_bind_name,
            ModuleBindName::PhintName(name) if name.is_empty()
        )
    {
        return Err(match loc {
            Some(loc) => PpxError::at_loc(loc, "empty name encountered"),
            None => PpxError::message("empty name encountered"),
        });
    }
    Ok(())
}

fn validate_ffi_names(ffi: &FfiType, loc: LocIdx) -> PpxResult<()> {
    match ffi {
        FfiType::FfiBs { external_spec, .. } => match external_spec {
            ExternalSpec::JsVar { name, .. } => validate_global_name(name, loc),
            ExternalSpec::JsModuleAsVar(module_name)
            | ExternalSpec::JsModuleAsFn {
                external_module_name: module_name,
                ..
            }
            | ExternalSpec::JsModuleAsClass(module_name) => {
                validate_external_module_name(module_name, None)
            }
            ExternalSpec::JsCall {
                name,
                external_module_name,
                ..
            }
            | ExternalSpec::JsNew {
                name,
                external_module_name,
                ..
            } => {
                if let Some(module_name) = external_module_name {
                    validate_external_module_name(module_name, Some(loc))?;
                }
                validate_global_name(name, loc)
            }
            ExternalSpec::JsSend { .. }
            | ExternalSpec::JsSet { .. }
            | ExternalSpec::JsGet { .. }
            | ExternalSpec::JsGetIndex { .. }
            | ExternalSpec::JsSetIndex { .. } => Ok(()),
        },
        _ => Ok(()),
    }
}

/// Check if an FFI external spec contains relative paths.
/// When true, the external must be wrapped in Pstr_include to prevent cross-module inlining.
/// Mirrors OCaml's check_ffi in external_ffi_types.ml.
fn check_ffi_relative(ffi: &FfiType) -> bool {
    match ffi {
        FfiType::FfiBs { external_spec, .. } => match external_spec {
            ExternalSpec::JsVar {
                name,
                external_module_name,
                ..
            } => {
                is_package_relative_path(name)
                    || external_module_name
                        .as_ref()
                        .map_or(false, |m| is_package_relative_path(&m.bundle))
            }
            ExternalSpec::JsModuleAsVar(emn)
            | ExternalSpec::JsModuleAsFn {
                external_module_name: emn,
                ..
            }
            | ExternalSpec::JsModuleAsClass(emn) => is_package_relative_path(&emn.bundle),
            ExternalSpec::JsNew {
                external_module_name,
                ..
            }
            | ExternalSpec::JsCall {
                external_module_name,
                ..
            } => external_module_name
                .as_ref()
                .map_or(false, |m| is_package_relative_path(&m.bundle)),
            _ => false,
        },
        _ => false,
    }
}

/// Result of encoding an external: new pval_prim and filtered attributes
pub struct EncodedExternal {
    pub pval_prim: Vec<StrIdx>,
    pub pval_attributes: Vec<Attribute>,
}

/// Filter out ReScript FFI attributes (they're consumed by encoding)
///
/// Note: OCaml's parse_external_attributes uses fold_left with cons, which
/// reverses the attribute order. We match this behavior by reversing the result.
fn filter_ffi_attributes(attrs: &[Attribute], arena: &mut ParseArena) -> Vec<Attribute> {
    let mut result: Vec<Attribute> = attrs
        .iter()
        .filter(|(attr_name, _payload)| {
            let name = arena.get_string(attr_name.txt);
            !EXTERNAL_ATTRS.iter().any(|&ext_attr| name == ext_attr)
        })
        .cloned()
        .collect();
    result.reverse();
    result
}

/// Encode external value description with FFI metadata
pub fn encode_external(vd: &ValueDescription, arena: &mut ParseArena) -> EncodedExternal {
    // Get the primitive name
    let prim_name = match vd.pval_prim.first() {
        Some(name) => arena.get_string(*name).to_string(),
        None => {
            return EncodedExternal {
                pval_prim: vd.pval_prim.clone(),
                pval_attributes: vd.pval_attributes.to_vec(),
            };
        }
    };

    // Check if this is a ReScript external
    if !is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return EncodedExternal {
            pval_prim: vd.pval_prim.clone(),
            pval_attributes: vd.pval_attributes.to_vec(),
        };
    }

    // Build arg type specs (mirrors OCaml's fold_right in handle_attributes)
    // Must compute before parse_external_attrs because @val behavior depends on no_arguments
    let vd_type = arena.get_core_type(vd.pval_type).clone();
    let (params, arity) = build_arg_type_specs(&vd_type, arena);
    // no_arguments = arg_types_ty = [] in OCaml: checks if there are ANY arrow args,
    // regardless of ignored. Use list_of_arrow directly.
    let (args, result_type) = list_of_arrow(&vd_type, arena);
    let no_arguments = args.is_empty();

    // Parse attributes
    let desc = parse_external_attrs(
        &vd.pval_attributes,
        prim_name.as_str(),
        no_arguments,
        vd.pval_loc,
        arena,
    );

    // Check if result is unit - use the result from list_of_arrow, not get_final_result_type
    // OCaml's handle_attributes uses result_type from list_of_arrow, which respects arity boundaries.
    // For `int => (unit => unit)`, result_type is `(unit => unit)`, NOT `unit`.
    let result_is_unit = is_unit_type(&result_type, arena);

    // Build FFI type
    let ffi = if desc.mk_obj {
        // @obj external: build FfiObjCreate with field names
        build_obj_ffi_type(&vd_type, arena)
    } else {
        build_ffi_type(&desc, prim_name.as_str(), arity, result_is_unit, params)
    };

    // Encode FFI type
    let encoded = encode_ffi_type(&ffi);

    // Filter out consumed FFI attributes
    let filtered_attrs = filter_ffi_attributes(&vd.pval_attributes, arena);

    EncodedExternal {
        pval_prim: vec![prim_str(arena, prim_name), prim_str(arena, encoded)],
        pval_attributes: filtered_attrs,
    }
}

/// Build FfiObjCreate from the type's labeled arguments.
/// Mirrors OCaml's process_obj which builds arg_kinds from arg_types_ty.
fn build_obj_ffi_type(typ: &CoreType, arena: &mut ParseArena) -> FfiType {
    let (args, _result) = list_of_arrow(typ, arena);

    let mut obj_params: Vec<ObjParam> = Vec::new();

    for arg in &args {
        match &arg.lbl {
            ArgLabel::Nolabel => {
                // Nolabel in @obj: only unit allowed, mark as empty_kind Extern_unit
                // OCaml process_obj line 449: External_arg_spec.empty_kind Extern_unit
                obj_params.push(ObjParam {
                    obj_arg_type: Attr::ExternUnit,
                    obj_arg_label: Label::ObjEmpty,
                });
            }
            ArgLabel::Labelled(label_loc) => {
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name =
                    get_as_string_attr(&arg.attrs, arena).unwrap_or_else(|| label_name.clone());

                let arg_typ = arena.get_core_type(arg.typ).clone();
                let arg_type = refine_arg_type(false, &arg_typ, arena);

                match arg_type {
                    Attr::Ignore => {
                        // @ignore: empty_kind with Ignore type (ObjEmpty label)
                        obj_params.push(ObjParam {
                            obj_arg_type: Attr::Ignore,
                            obj_arg_label: Label::ObjEmpty,
                        });
                    }
                    Attr::ArgCst(_) => {
                        // @as(_) constant: add obj_label but not to arg_types
                        obj_params.push(ObjParam {
                            obj_arg_type: arg_type,
                            obj_arg_label: Label::ObjLabel { name: field_name },
                        });
                    }
                    _ => {
                        // Regular arg
                        obj_params.push(ObjParam {
                            obj_arg_type: arg_type,
                            obj_arg_label: Label::ObjLabel { name: field_name },
                        });
                    }
                }
            }
            ArgLabel::Optional(label_loc) => {
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name =
                    get_as_string_attr(&arg.attrs, arena).unwrap_or_else(|| label_name.clone());

                let arg_typ = arena.get_core_type(arg.typ).clone();
                let arg_type = get_opt_arg_type_unchecked(false, &arg_typ, arena);

                match arg_type {
                    Attr::Ignore => {
                        // @ignore: empty_kind with Ignore type (ObjEmpty label)
                        obj_params.push(ObjParam {
                            obj_arg_type: Attr::Ignore,
                            obj_arg_label: Label::ObjEmpty,
                        });
                    }
                    Attr::Nothing => {
                        // Check if for_sure_no_nested_option
                        let for_sure_not_nested = match &*arena.get_core_type(arg.typ).ptyp_desc {
                            CoreTypeDesc::Ptyp_constr(inner) if inner.1.is_empty() => {
                                let (ref lid, ref args) = **inner;
                                let longident = arena.get_longident(lid.txt);
                                if let Longident::Lident(s) = longident {
                                    let name = arena.get_string(*s);
                                    // is_builtin_rank0_type
                                    matches!(
                                        name,
                                        "int" | "float" | "string" | "bool" | "unit" | "exn"
                                    )
                                } else {
                                    false
                                }
                            }
                            _ => false,
                        };
                        obj_params.push(ObjParam {
                            obj_arg_type: arg_type,
                            obj_arg_label: Label::ObjOptional {
                                name: field_name,
                                for_sure_no_nested_option: for_sure_not_nested,
                            },
                        });
                    }
                    Attr::Int(_) | Attr::PolyVarString { .. } => {
                        // @int or @string optional: for_sure_no_nested = true
                        obj_params.push(ObjParam {
                            obj_arg_type: arg_type,
                            obj_arg_label: Label::ObjOptional {
                                name: field_name,
                                for_sure_no_nested_option: true,
                            },
                        });
                    }
                    _ => {
                        // Other optional types
                        obj_params.push(ObjParam {
                            obj_arg_type: arg_type,
                            obj_arg_label: Label::ObjOptional {
                                name: field_name,
                                for_sure_no_nested_option: false,
                            },
                        });
                    }
                }
            }
        }
    }

    FfiType::FfiObjCreate(obj_params)
}

/// Encode inline string constant
/// Matches OCaml's Delim.parse_processed:
///   None -> Some(DNone)
///   Some "json" -> Some(DNoQuotes)
///   Some "*j" -> Some(DStarJ)
///   Some "bq" -> Some(DBackQuotes)
///   _ -> None
///
/// NOTE: In OCaml, the PPX transforms attribute payloads BEFORE extracting @inline,
/// so "js" -> "*j" transformation happens first. In Rust, we get the original delimiter,
/// so we need to handle "js" as if it were already transformed to "*j".
pub fn inline_string_primitive(
    s: &str,
    delim: Option<&str>,
    arena: &mut ParseArena,
) -> Vec<StrIdx> {
    let delim = match delim {
        None => Some(Delim::DNone), // Key difference: OCaml wraps None in Some(DNone)
        Some("json") => Some(Delim::DNoQuotes),
        Some("*j") | Some("js") => Some(Delim::DStarJ), // "js" is transformed to "*j" by PPX, both map to DStarJ
        Some("bq") => Some(Delim::DBackQuotes),
        _ => None,
    };

    let constant = LamConstant::ConstString {
        s: s.to_string(),
        delim,
    };

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![arena.prim_empty_external_ffi(), prim_str(arena, encoded)]
}

/// Encode inline bool constant
pub fn inline_bool_primitive(b: bool, arena: &mut ParseArena) -> Vec<StrIdx> {
    let constant = if b {
        LamConstant::ConstJsTrue
    } else {
        LamConstant::ConstJsFalse
    };

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![arena.prim_empty_external_ffi(), prim_str(arena, encoded)]
}

/// Encode inline int constant
pub fn inline_int_primitive(i: i32, arena: &mut ParseArena) -> Vec<StrIdx> {
    let constant = LamConstant::ConstInt {
        i,
        comment: PointerInfo::None,
    };

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![arena.prim_empty_external_ffi(), prim_str(arena, encoded)]
}

/// Encode inline float constant
pub fn inline_float_primitive(f: &str, arena: &mut ParseArena) -> Vec<StrIdx> {
    let constant = LamConstant::ConstFloat(f.to_string());

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![arena.prim_empty_external_ffi(), prim_str(arena, encoded)]
}

/// Encode inline bigint constant
pub fn inline_bigint_primitive(s: &str, arena: &mut ParseArena) -> Vec<StrIdx> {
    // Parse bigint: handle optional - sign
    let (negative, digits) = if let Some(stripped) = s.strip_prefix('-') {
        (true, stripped.to_string())
    } else {
        (false, s.to_string())
    };

    let constant = LamConstant::ConstBigint(negative, digits);

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![arena.prim_empty_external_ffi(), prim_str(arena, encoded)]
}

// ========== @inline Handling ==========

/// Check if attributes contain @inline
fn has_inline_attr(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _)| {
        let name = arena.get_string(attr_name.txt);
        name == "inline"
    })
}

/// Find @inline attribute with a payload containing an expression.
/// Returns the expression from @inline(expr) if found.
/// This is used for signature items like: @inline("value") let x: t
fn find_inline_payload_expr<'a>(
    attrs: &[Attribute],
    arena: &'a ParseArena,
) -> Option<&'a Expression> {
    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        if name == "inline" {
            // @inline(expr) has PStr with a single Pstr_eval
            if let Some(items) = payload_str_items(payload) {
                if items.len() == 1 {
                    if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                        let (ref expr, _) = **eval_inner;
                        return Some(arena.get_expr(*expr));
                    }
                }
            }
        }
    }
    None
}

/// Transform @inline("value") let x: t in a signature to a primitive
fn transform_inline_sig_value(
    vd: &ValueDescription,
    arena: &mut ParseArena,
) -> Option<ValueDescription> {
    let expr = find_inline_payload_expr(&vd.pval_attributes, arena)?.clone();

    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_constant(c) => match &**c {
            // @inline("string") or @inline(`template`) let x: t
            Constant::String(s, delim) => {
                // OCaml's PPX transforms template literal delimiters ("js" → "bq")
                // before extracting @inline payloads. We must match that behavior here
                // since the payload expression isn't run through rewrite_expression.
                let effective_delim = match delim.as_deref() {
                    Some("js") if has_template_attr(&expr, arena) => Some("bq"),
                    other => other,
                };
                let prim = inline_string_primitive(s, effective_delim, arena);
                Some(ValueDescription {
                    pval_name: vd.pval_name.clone(),
                    pval_type: vd.pval_type.clone(),
                    pval_prim: prim,
                    pval_attributes: Attributes::new(), // Clear attributes
                    pval_loc: vd.pval_loc,
                })
            }
            // @inline(42) let x: t
            Constant::Integer(s, None) => {
                let i = s.parse::<i32>().ok()?;
                let prim = inline_int_primitive(i, arena);
                Some(ValueDescription {
                    pval_name: vd.pval_name.clone(),
                    pval_type: vd.pval_type.clone(),
                    pval_prim: prim,
                    pval_attributes: Attributes::new(), // Clear attributes
                    pval_loc: vd.pval_loc,
                })
            }
            // @inline(42n) let x: t (bigint)
            Constant::Integer(s, Some('n')) => {
                let prim = inline_bigint_primitive(s, arena);
                Some(ValueDescription {
                    pval_name: vd.pval_name.clone(),
                    pval_type: vd.pval_type.clone(),
                    pval_prim: prim,
                    pval_attributes: Attributes::new(), // Clear attributes
                    pval_loc: vd.pval_loc,
                })
            }
            // @inline(3.14) let x: t
            Constant::Float(s, None) => {
                let prim = inline_float_primitive(s, arena);
                Some(ValueDescription {
                    pval_name: vd.pval_name.clone(),
                    pval_type: vd.pval_type.clone(),
                    pval_prim: prim,
                    pval_attributes: Attributes::new(), // Clear attributes
                    pval_loc: vd.pval_loc,
                })
            }
            _ => None,
        },
        // @inline(true) or @inline(false) let x: t
        ExpressionDesc::Pexp_construct(lid, None) => {
            let longident = arena.get_longident(lid.txt);
            if let Longident::Lident(name_idx) = longident {
                let name = arena.get_string(*name_idx);
                if name == "true" || name == "false" {
                    let prim = inline_bool_primitive(name == "true", arena);
                    return Some(ValueDescription {
                        pval_name: vd.pval_name.clone(),
                        pval_type: vd.pval_type.clone(),
                        pval_prim: prim,
                        pval_attributes: Attributes::new(), // Clear attributes
                        pval_loc: vd.pval_loc,
                    });
                }
            }
            None
        }
        _ => None,
    }
}

/// Create a type for a simple builtin type (string, int, float, bool)
fn make_simple_type(type_name: &'static str, arena: &mut ParseArena) -> CoreType {
    let none_loc = arena.none_loc();
    let lid_idx = match type_name {
        "string" => arena.ast_literal_type_string_lident(),
        "int" => arena.ast_literal_type_int_lident(),
        "bool" => arena.ast_literal_type_bool_lident(),
        "float" => arena.ast_literal_type_float_lident(),
        _ => arena.push_lident_static(type_name),
    };
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: lid_idx,
                loc: none_loc,
            },
            vec![],
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    }
}
/// Transform an @inline let binding into a primitive
fn transform_inline_binding(
    pval_name: &Located<StrIdx>,
    expr: &Expression,
    pvb_loc: LocIdx,
    pstr_loc: LocIdx,
    arena: &mut ParseArena,
) -> Option<StructureItem> {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_constant(c) => match &**c {
            // @inline let x = "string"
            Constant::String(s, delim) => {
                let prim = inline_string_primitive(s, delim.as_deref(), arena);
                Some(StructureItem {
                    pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(
                        ValueDescription {
                            pval_name: Located {
                                txt: pval_name.txt,
                                loc: pval_name.loc,
                            },
                            pval_type: arena.ast_literal_type_string(),
                            pval_prim: prim,
                            pval_attributes: Attributes::new(),
                            pval_loc: pvb_loc,
                        },
                    ))),
                    pstr_loc,
                })
            }
            // @inline let x = 42
            Constant::Integer(s, None) => {
                let i = s.parse::<i32>().ok()?;
                let prim = inline_int_primitive(i, arena);
                Some(StructureItem {
                    pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(
                        ValueDescription {
                            pval_name: Located {
                                txt: pval_name.txt,
                                loc: pval_name.loc,
                            },
                            pval_type: arena.ast_literal_type_int(),
                            pval_prim: prim,
                            pval_attributes: Attributes::new(),
                            pval_loc: pvb_loc,
                        },
                    ))),
                    pstr_loc,
                })
            }
            // @inline let x = 3.14
            Constant::Float(s, None) => {
                let prim = inline_float_primitive(s, arena);
                Some(StructureItem {
                    pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(
                        ValueDescription {
                            pval_name: Located {
                                txt: pval_name.txt,
                                loc: pval_name.loc,
                            },
                            pval_type: arena.ast_literal_type_float(),
                            pval_prim: prim,
                            pval_attributes: Attributes::new(),
                            pval_loc: pvb_loc,
                        },
                    ))),
                    pstr_loc,
                })
            }
            _ => None,
        },
        // @inline let x = true or @inline let x = false
        ExpressionDesc::Pexp_construct(lid, None) => {
            let longident = arena.get_longident(lid.txt);
            if let Longident::Lident(name_idx) = longident {
                let name = arena.get_string(*name_idx);
                if name == "true" || name == "false" {
                    let prim = inline_bool_primitive(name == "true", arena);
                    return Some(StructureItem {
                        pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(
                            ValueDescription {
                                pval_name: Located {
                                    txt: pval_name.txt,
                                    loc: pval_name.loc,
                                },
                                pval_type: arena.ast_literal_type_bool(),
                                pval_prim: prim,
                                pval_attributes: Attributes::new(),
                                pval_loc: pvb_loc,
                            },
                        ))),
                        pstr_loc,
                    });
                }
            }
            None
        }
        _ => None,
    }
}

// ========== Extension Point Handling ==========

/// Handle an extension point in expression position.
/// Transforms:
/// - %raw("...") into the local_external_apply pattern
/// - %re("...") into %raw with RegExp type constraint (TODO)
/// - %debugger into debugger call (TODO)
/// - Other extensions are returned unchanged
fn handle_extension(
    expr: &Expression,
    ext: &current::Extension,
    arena: &mut ParseArena,
) -> Expression {
    let (ext_name, payload) = ext;
    let name = arena.get_string(ext_name.txt);

    // OCaml's handle_extension deconstructs the extension as ({txt; loc}, payload)
    // where loc is the extension IDENTIFIER's location (e.g., just "%raw", not "%raw(...)").
    // This loc is passed to local_external_apply and used for internal structures.
    let ext_loc = ext_name.loc;

    match name {
        "raw" => handle_raw(expr, payload, arena, arena.prim_raw_expr(), ext_loc),
        "ffi" => handle_ffi(expr, payload, arena, ext_loc),
        "re" => handle_re(expr, payload, arena, ext_loc),
        "debugger" => handle_debugger(expr, payload, arena, ext_loc),
        "obj" => handle_obj(expr, payload, arena),
        _ => expr.clone(),
    }
}

/// Handle %obj extension: transforms `%obj({"a": e1, "b": e2})` into a letmodule
/// with an external FFI declaration.
///
/// OCaml transforms `%obj({"key": value, ...})` into:
/// ```text
/// let module J = struct
///   external unsafe_expr: (~a: 'a0, ~b: 'a1) => {"a": 'a0, "b": 'a1} = ""
/// end in J.unsafe_expr(~a=e1, ~b=e2)
/// ```
///
/// This mirrors:
/// - `ast_exp_extension.ml` line 73-86: pattern matching %obj payload
/// - `ast_util.ml:record_as_js_object`: extracts labels and args from record
/// - `ast_external_mk.ml:local_external_obj`: creates the letmodule wrapper
/// - `ast_core_type.ml:from_labels`: builds the arrow type with object return
/// - `ast_external_process.ml:pval_prim_of_labels`: creates FFI encoding
/// - `ast_compatible.ml:apply_labels`: creates labeled function application
fn handle_obj(expr: &Expression, payload: &Payload, arena: &mut ParseArena) -> Expression {
    // Extract the record expression from the payload: PStr [{ Pstr_eval(Box::new((Pexp_record(...), _))) }]
    let (record_expr, label_exprs) = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (ref e, _) = **eval_inner;
                if let ExpressionDesc::Pexp_record(rec_inner) = &*arena.get_expr(*e).pexp_desc {
                    if rec_inner.1.is_none() {
                        (*e, rec_inner.0.clone())
                    } else {
                        return expr.clone();
                    }
                } else {
                    return expr.clone();
                }
            } else {
                return expr.clone();
            }
        }
        _ => return expr.clone(),
    };

    // The loc used for internal structures is the record expression's pexp_loc
    // (OCaml: `e.pexp_loc` passed to `record_as_js_object`)
    let loc = arena.get_expr(record_expr).pexp_loc;
    let none_loc = arena.none_loc();

    // Extract labels and rewritten expressions from the record fields.
    // OCaml: Ext_list.fold_right label_exprs ([], [], 0) (fun {lid={txt;loc}; x=e} ...)
    // Only Lident fields are valid.
    let mut labels: Vec<(StrIdx, LocIdx)> = Vec::with_capacity(label_exprs.len());
    let mut args: Vec<(StrIdx, Expression)> = Vec::with_capacity(label_exprs.len());
    let arity = label_exprs.len();

    for field in &label_exprs {
        let lid = arena.get_longident(field.lid.txt).clone();
        match lid {
            Longident::Lident(str_idx) => {
                let field_loc = field.lid.loc;
                labels.push((str_idx, field_loc));
                // Recursively rewrite the field expression (OCaml: self.expr self e)
                let field_expr = arena.get_expr(field.expr).clone();
                let rewritten_expr = rewrite_expression(&field_expr, arena);
                args.push((str_idx, rewritten_expr));
            }
            _ => return expr.clone(), // Invalid label
        }
    }

    // === Build pval_prim: [""; encode(Ffi_obj_create(obj_params))] ===
    // OCaml: pval_prim_of_labels creates ObjLabel for each field
    let obj_params: Vec<super::ffi_types::ObjParam> = labels
        .iter()
        .map(|(str_idx, _)| {
            let name = arena.get_string(*str_idx).to_owned();
            super::ffi_types::ObjParam {
                obj_arg_type: Attr::Nothing,
                obj_arg_label: super::ffi_types::Label::ObjLabel { name },
            }
        })
        .collect();

    let ffi = FfiType::FfiObjCreate(obj_params);
    let encoded = encode_ffi_type(&ffi);
    let pval_prim = vec![arena.prim_empty_external_ffi(), prim_str(arena, encoded)];

    // === Build pval_type: (~a: 'a0, ~b: 'a1) => {"a": 'a0, "b": 'a1} ===
    // OCaml: from_labels ~loc arity labels

    // Create type variables 'a0, 'a1, ...
    let tyvars: Vec<CoreType> = (0..arity)
        .map(|i| CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(format!(
                "a{}",
                i
            ))))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        })
        .collect();

    // Create object type: {"a": 'a0, "b": 'a1}
    let obj_fields: Vec<current::ObjectField> = labels
        .iter()
        .zip(tyvars.iter())
        .map(|((str_idx, label_loc), tyvar)| {
            current::ObjectField::Otag(
                Located {
                    txt: *str_idx,
                    loc: *label_loc,
                },
                Attributes::new(),
                arena.push_core_type(tyvar.clone()),
            )
        })
        .collect();

    let result_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_object(Box::new((
            obj_fields,
            current::ClosedFlag::Closed,
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create arrow type args: [~a: 'a0, ~b: 'a1]
    // OCaml: Ext_list.map2 labels tyvars (fun label tyvar -> {attrs=[]; lbl=Labelled label; typ=tyvar})
    let type_args: Vec<TypeArg> = labels
        .iter()
        .zip(tyvars.iter())
        .map(|((str_idx, label_loc), tyvar)| TypeArg {
            attrs: Attributes::new(),
            lbl: ArgLabel::Labelled(Located {
                txt: *str_idx,
                loc: *label_loc,
            }),
            typ: arena.push_core_type(tyvar.clone()),
        })
        .collect();

    // Build the arrow chain using Typ.arrows logic:
    // arity = Some(list_length) for outermost, None for inner arrows
    let pval_type = build_arrows(type_args, result_type, loc, arena);

    // === Create the letmodule structure ===
    let module_name_idx = arena.intern_string("J");
    let func_name_idx = arena.intern_string("unsafe_expr");

    let vd = ValueDescription {
        pval_name: Located {
            txt: func_name_idx,
            loc,
        },
        pval_type: arena.push_core_type(pval_type),
        pval_prim,
        pval_attributes: Attributes::new(),
        pval_loc: loc,
    };

    let mod_structure = vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(vd))),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(mod_structure))),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    // === Create the function application: J.unsafe_expr(~a=e1, ~b=e2) ===
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    let func_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: j_unsafe_expr,
            loc,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // OCaml: apply_labels fn args ~loc
    // Labels use Location.none for their loc.
    // Use the original StrIdx from the field name, NOT a fresh intern, so that
    // the string is shared with the same StrIdx used in the type's Labelled arg.
    let apply_args: Vec<(ArgLabel, Expression)> = args
        .into_iter()
        .map(|(str_idx, e)| {
            (
                ArgLabel::Labelled(Located {
                    txt: str_idx,
                    loc: none_loc,
                }),
                e,
            )
        })
        .collect();

    let apply_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(func_ident),
            args: apply_args
                .into_iter()
                .map(|(lbl, e)| (lbl, arena.push_expr(e)))
                .collect(),
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // The final result: {e with pexp_desc = Pexp_letmodule(...)}
    // where e is the record expression, so pexp_loc = record's loc and pexp_attributes = record's attrs
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_letmodule(Box::new((
            Located {
                txt: module_name_idx,
                loc,
            },
            arena.push_mod_expr(mod_expr),
            arena.push_expr(apply_expr),
        )))),
        pexp_loc: arena.get_expr(record_expr).pexp_loc,
        pexp_attributes: arena.get_expr(record_expr).pexp_attributes.clone(),
    }
}

/// Build a chain of arrow types from a list of type arguments and a result type.
/// Mirrors OCaml's `Typ.arrows`:
/// - First arrow gets arity = Some(list_length)
/// - Inner arrows get arity = None
fn build_arrows(
    args: Vec<TypeArg>,
    result: CoreType,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> CoreType {
    if args.is_empty() {
        return result;
    }
    let arity = arena.push_arity(Some(args.len() as i32));
    let first = args[0].clone();
    let ret = arena.push_core_type(result);
    arena.set_nary_arrow_args(arity, args);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(first),
            ret,
            arity,
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Handle %debugger extension by transforming it into local_external_apply pattern.
///
/// OCaml transforms `%debugger` into:
/// ```text
/// let module J = struct
///   external unsafe_expr: _ -> unit = "%debugger"
/// end in J.unsafe_expr(())
/// ```
fn handle_debugger(
    expr: &Expression,
    payload: &Payload,
    arena: &mut ParseArena,
    ext_loc: LocIdx,
) -> Expression {
    // %debugger doesn't accept arguments
    if !payload_is_empty_str(payload) {
        return expr.clone(); // Error case - return unchanged
    }

    // OCaml: loc comes from the extension identifier's location ({txt; loc} pattern)
    let loc = ext_loc;
    let none_loc = arena.none_loc();

    // Create the type: _ -> unit
    let any_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create "unit" type
    let unit_ident = arena.push_lident_static("unit");
    let unit_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: unit_ident,
                loc: none_loc,
            },
            vec![],
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let pval_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(any_type),
            }),
            arena.push_core_type(unit_type),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create strings for the module/function names
    let module_name_idx = arena.intern_string("J");
    let func_name_idx = arena.intern_string("unsafe_expr");

    // Create the value description (external primitive) - uses %debugger
    let vd = ValueDescription {
        pval_name: Located {
            txt: func_name_idx,
            loc,
        },
        pval_type: arena.push_core_type(pval_type),
        pval_prim: vec![prim_str(arena, "%debugger")],
        pval_attributes: Attributes::new(),
        pval_loc: loc,
    };

    // Create the module structure
    let mod_structure = vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(vd))),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(mod_structure))),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    // Create the longident J.unsafe_expr
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    // Create the unit literal: ()
    let unit_construct = arena.push_lident_static("()");
    let unit_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
            Located {
                txt: unit_construct,
                loc: none_loc,
            },
            None,
        )),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    // Create the function application: J.unsafe_expr(())
    let func_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: j_unsafe_expr,
            loc,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    let apply_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(func_ident),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(unit_expr))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // Create the final expression: let module J = struct ... end in J.unsafe_expr(())
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_letmodule(Box::new((
            Located {
                txt: module_name_idx,
                loc,
            },
            arena.push_mod_expr(mod_expr),
            arena.push_expr(apply_expr),
        )))),
        pexp_loc: loc,
        pexp_attributes: expr.pexp_attributes.clone(),
    }
}

/// Handle %re extension by transforming it into %raw with RegExp type constraint.
///
/// OCaml transforms `%re("regex")` into:
/// ```text
/// (handle_raw("regex") : Stdlib_RegExp.t)
/// ```
/// i.e., the same as %raw but with a type constraint to Stdlib_RegExp.t
fn handle_re(
    expr: &Expression,
    payload: &Payload,
    arena: &mut ParseArena,
    ext_loc: LocIdx,
) -> Expression {
    // OCaml: loc comes from the extension identifier's location ({txt; loc} pattern)
    let loc = ext_loc;

    // First, handle it like %raw to get the letmodule expression
    let raw_expr = handle_raw(expr, payload, arena, arena.prim_raw_expr(), ext_loc);

    // Create the type: Stdlib_RegExp.t
    // This is Longident.Ldot(Lident "Stdlib_RegExp", "t")
    // OCaml uses `loc` for both ptyp_loc and the Located.loc:
    //   Typ.constr ~loc {txt = regexp_id; loc} []
    let regexp_t = arena.regexp_t_lident();

    let regexp_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located { txt: regexp_t, loc },
            vec![],
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    };

    // Wrap the raw expression in a type constraint
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
            arena.push_expr(raw_expr),
            arena.push_core_type(regexp_type),
        )))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Handle %raw extension by transforming it into local_external_apply pattern.
///
/// OCaml transforms `%raw("code")` into:
/// ```text
/// let module J = struct
///   external unsafe_expr: 'a -> 'a = "#raw_expr"
/// end in J.unsafe_expr("code")
/// ```
fn handle_raw(
    expr: &Expression,
    payload: &Payload,
    arena: &mut ParseArena,
    pval_prim: StrIdx,
    ext_loc: LocIdx,
) -> Expression {
    // Extract the string expression from the payload
    // OCaml's raw_as_string_exp_exn returns {e with pexp_desc = Pexp_constant ...}
    // where e is the original expression from the payload.
    // The returned expression uses e.pexp_loc (the payload string's location).
    // Also detect if the JS string contains a function (for internal.expansive attribute).
    let (str_exp, payload_loc, is_function) = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (ref e, _) = **eval_inner;
                if let ExpressionDesc::Pexp_constant(c) = &*arena.get_expr(*e).pexp_desc {
                    if let Constant::String(s, _) = &**c {
                        // Check if the JS string contains a function
                        let is_func = is_js_function(&s);

                        // Create a new string expression with delimiter stripped
                        // (OCaml strips the delimiter when transforming %raw)
                        let exp = Expression {
                            pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(
                                Constant::String(
                                    s.clone(),
                                    None, // Strip delimiter
                                ),
                            ))),
                            pexp_loc: arena.get_expr(*e).pexp_loc,
                            pexp_attributes: arena.get_expr(*e).pexp_attributes.clone(),
                        };
                        (exp, arena.get_expr(*e).pexp_loc, is_func)
                    } else {
                        return expr.clone();
                    }
                } else {
                    return expr.clone();
                }
            } else {
                return expr.clone();
            }
        }
        _ => return expr.clone(),
    };

    // OCaml's local_external_apply uses `loc` from the extension identifier's location
    // ({txt; loc} pattern in handle_extension), NOT the full expression's pexp_loc
    let loc = ext_loc;

    // Use none_loc() for types, matching OCaml's Ast_helper.Typ.any()
    // which uses default_loc (= Location.none = in_file "_none_")
    // In the AST, Location is an alias for LocIdx
    let none_loc = arena.none_loc();

    // Create the type: _ -> _
    let any_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let pval_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(any_type.clone()),
            }),
            arena.push_core_type(any_type),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create strings for the module/function names
    let module_name_idx = arena.intern_string("J");
    let func_name_idx = arena.intern_string("unsafe_expr");

    // Create the value description (external primitive)
    let vd = ValueDescription {
        pval_name: Located {
            txt: func_name_idx,
            loc,
        },
        pval_type: arena.push_core_type(pval_type),
        pval_prim: vec![pval_prim],
        pval_attributes: Attributes::new(),
        pval_loc: loc,
    };

    // Create the module structure: struct external unsafe_expr: _ -> _ = "#raw_expr" end
    let mod_structure = vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(vd))),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(mod_structure))),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    // Create the longident J.unsafe_expr
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    // Save attributes before moving str_exp
    let payload_attributes = str_exp.pexp_attributes.clone();

    // Create the function application: J.unsafe_expr("code")
    let func_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: j_unsafe_expr,
            loc,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    let apply_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(func_ident),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(str_exp))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // Create the final expression: let module J = struct ... end in J.unsafe_expr("code")
    // OCaml's handle_raw returns {exp with pexp_desc = ...} so:
    // - pexp_loc = exp.pexp_loc = payload string's location (payload_loc)
    // - pexp_attributes = exp.pexp_attributes (or with internal_expansive added for functions)
    //
    // If the JS string contains a function, prepend the internal.expansive attribute.
    // This matches OCaml's behavior in ast_exp_handle_external.ml:handle_raw
    let final_attributes = if is_function {
        // Create internal.expansive attribute
        // OCaml uses: Ast_attributes.internal_expansive = ({txt="internal.expansive"; loc=locg}, Ast_payload.empty)
        // where locg = Location.none
        let attr_name_idx = arena.intern_string("internal.expansive");
        let internal_expansive: Attribute = (
            Located {
                txt: attr_name_idx,
                loc: none_loc, // OCaml uses Location.none for this attribute
            },
            Payload::PStr(Box::new(vec![])),
        );
        let mut attrs = vec![internal_expansive];
        attrs.extend(payload_attributes.iter().cloned());
        Attributes::from_vec(attrs)
    } else {
        payload_attributes
    };

    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_letmodule(Box::new((
            Located {
                txt: module_name_idx,
                loc,
            },
            arena.push_mod_expr(mod_expr),
            arena.push_expr(apply_expr),
        )))),
        pexp_loc: payload_loc,
        pexp_attributes: final_attributes,
    }
}

/// Detect JS function arity from source code.
/// Matches OCaml's Classify_function.classify_exp behavior.
fn detect_js_function_arity(code: &str) -> Option<usize> {
    if let Some(arity) = classify_js_function_arity(code) {
        return Some(arity);
    }
    if let Some(arity) = classify_recovered_arrow_function_arity(code) {
        return Some(arity);
    }

    let trimmed = code.trim();
    // Recovered function expression: Flow still returns a Function AST for
    // warning-only cases such as `function` or `function foo`.
    if starts_with_keyword(trimmed, "function") {
        if let Some(open) = trimmed.find('(') {
            if let Some(close) = trimmed[open..].find(')') {
                let params_str = trimmed[open + 1..open + close].trim();
                if params_str.is_empty() {
                    return Some(0);
                }
                return Some(params_str.split(',').count());
            }
        }
        return Some(0);
    }
    None
}

/// Handle %ffi extension.
///
/// OCaml transforms `%ffi(\`code\`)` into:
/// ```text
/// Pexp_constraint(
///   (_ -> _) for arity 1, or ((_, _) -> _) for arity 2, etc.,
///   let module J = struct
///     external unsafe_expr: 'a -> 'a = "#raw_expr"
///   end in J.unsafe_expr("code")
/// )
/// ```
fn handle_ffi(
    expr: &Expression,
    payload: &Payload,
    arena: &mut ParseArena,
    ext_loc: LocIdx,
) -> Expression {
    // Extract the string from the payload to detect arity
    let code_str = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (e_idx, _) = &**eval_inner;
                let e = arena.get_expr(*e_idx);
                if let ExpressionDesc::Pexp_constant(c) = &*e.pexp_desc {
                    if let Constant::String(s, _) = &**c {
                        Some(s.to_string())
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
        _ => None,
    };

    let arity = code_str.as_ref().and_then(|s| detect_js_function_arity(s));

    // Create the raw expression (same as %raw with #raw_expr).
    // OCaml passes the extension identifier location into local_external_apply.
    let raw_prim = prim_str(arena, "#raw_expr");
    let raw_expr = handle_raw(expr, payload, arena, raw_prim, ext_loc);

    // Wrap in type constraint based on arity
    if let Some(arity) = arity {
        // OCaml constraints the rewritten expression at e.pexp_loc where e is the
        // payload string expression returned by raw_as_string_exp_exn.
        let loc = raw_expr.pexp_loc;

        let any_type = CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        };
        let any_type_idx = arena.push_core_type(any_type);

        // Build arrow type: (_, _, ...) -> _ with effective_arity args
        let effective_arity = if arity == 0 { 1 } else { arity };
        let args: Vec<_> = (0..effective_arity)
            .map(|_| TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: any_type_idx,
            })
            .collect();

        // Build arrow type matching OCaml's Ast_helper.Typ.arrows:
        // arrows [arg1; arg2] ret => arrow ~arity:(Some n) arg1 (arrow ~arity:None arg2 ret)
        let total_arity = arena.push_arity(Some(effective_arity as i32));
        let none_arity = arena.static_arity_none();
        let arrow_type_idx = {
            // Build from right to left
            let mut result_idx = any_type_idx; // return type
            for i in (0..args.len()).rev() {
                let arity = if i == 0 { total_arity } else { none_arity };
                let arrow = CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
                        Box::new(args[i].clone()),
                        result_idx,
                        arity,
                    )))),
                    ptyp_loc: loc,
                    ptyp_attributes: Attributes::new(),
                };
                result_idx = arena.push_core_type(arrow);
            }
            result_idx
        };

        let raw_expr_idx = arena.push_expr(raw_expr);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                raw_expr_idx,
                arrow_type_idx,
            )))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        raw_expr
    }
}

/// Handle %%raw extension at structure level.
///
/// OCaml transforms `%%raw("code")` into:
/// ```text
/// Pstr_eval(
///   let module J = struct
///     external unsafe_expr: 'a -> 'a = "#raw_stmt"
///   end in J.unsafe_expr("code")
/// )
/// ```
fn handle_raw_structure(
    item: &StructureItem,
    payload: &Payload,
    arena: &mut ParseArena,
    ext_loc: LocIdx,
) -> StructureItem {
    // Extract the string expression from the payload
    let (str_exp, str_loc, payload_attrs) = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                let (ref e, _) = **eval_inner;
                let expr = arena.get_expr(*e);
                if let ExpressionDesc::Pexp_constant(c) = &*expr.pexp_desc {
                    if let Constant::String(s, _) = &**c {
                        // Create a new string expression with delimiter stripped
                        (
                            Expression {
                                pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(
                                    Constant::String(
                                        s.clone(),
                                        None, // Strip delimiter
                                    ),
                                ))),
                                pexp_loc: expr.pexp_loc,
                                pexp_attributes: expr.pexp_attributes.clone(),
                            },
                            expr.pexp_loc,
                            expr.pexp_attributes.clone(),
                        )
                    } else {
                        return item.clone();
                    }
                } else {
                    return item.clone();
                }
            } else {
                return item.clone();
            }
        }
        _ => return item.clone(),
    };

    // OCaml: loc comes from the extension identifier's location ({txt = "raw"; loc})
    let loc = ext_loc;
    let none_loc = arena.none_loc();

    // Create the type: _ -> _
    let any_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let pval_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(any_type.clone()),
            }),
            arena.push_core_type(any_type),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create strings for the module/function names
    let module_name_idx = arena.intern_string("J");
    let func_name_idx = arena.intern_string("unsafe_expr");

    // Create the value description (external primitive) - uses #raw_stmt for structure level
    let vd = ValueDescription {
        pval_name: Located {
            txt: func_name_idx,
            loc,
        },
        pval_type: arena.push_core_type(pval_type),
        pval_prim: vec![arena.prim_raw_stmt()],
        pval_attributes: Attributes::new(),
        pval_loc: loc,
    };

    // Create the module structure
    let mod_structure = vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(vd))),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(mod_structure))),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    // Create the longident J.unsafe_expr
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    // Create the function application: J.unsafe_expr("code")
    // Save attributes before moving str_exp (for template attribute propagation)
    let payload_attributes = str_exp.pexp_attributes.clone();

    let func_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: j_unsafe_expr,
            loc,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    let apply_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(func_ident),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(str_exp))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // Create the let module expression
    // Inherit the template attribute from the string expression (res.template)
    let letmodule_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_letmodule(Box::new((
            Located {
                txt: module_name_idx,
                loc,
            },
            arena.push_mod_expr(mod_expr),
            arena.push_expr(apply_expr),
        )))),
        pexp_loc: str_loc, // Use the string expression's location for outer expr
        pexp_attributes: payload_attributes,
    };

    // Wrap in Pstr_eval - OCaml's Ast_helper.Str.eval uses default_loc (= Location.none)
    // when no ~loc is passed, so we use none_loc here
    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((
            arena.push_expr(letmodule_expr),
            Attributes::new(),
        ))))
        .into(),
        pstr_loc: none_loc,
    }
}

/// Handle %%private(let x = ...) extension.
///
/// Transforms:
/// ```rescript
/// %%private(let x = 34)
/// ```
/// Into:
/// ```rescript
/// module local_1 = { let x = 34 }  // with @internal.local attribute
/// open! local_1
/// ```
///
/// This matches OCaml's expand_reverse in bs_builtin_ppx.ml.
fn handle_private_extension(
    payload: &Payload,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> PpxResult<Vec<StructureItem>> {
    let items = private_extension_structure_items(payload, loc)?;

    // Rewrite the items first (for string transformations etc.)
    let rewritten_items: Vec<StructureItem> = items
        .iter()
        .flat_map(|item| rewrite_structure_item(item, arena))
        .collect();

    check_private_extension_items(&rewritten_items, arena)?;

    Ok(wrap_in_local_module(rewritten_items, loc, arena))
}

fn private_extension_structure_items<'a>(
    payload: &'a Payload,
    loc: LocIdx,
) -> PpxResult<&'a Vec<StructureItem>> {
    match payload {
        Payload::PStr(items) if !items.is_empty() => Ok(items),
        Payload::PStr(_) => Err(PpxError::at_loc(
            loc,
            "%%private extension expects a definition as its argument. Example: %%private(let a = \"Hello\")",
        )),
        Payload::PSig(_) | Payload::PTyp(_) | Payload::PPat(_) => {
            Err(PpxError::at_loc(loc, "private extension is not support"))
        }
    }
}

fn check_private_extension_items(items: &[StructureItem], arena: &ParseArena) -> PpxResult<()> {
    for item in items {
        if !private_extension_item_allowed(item, arena) {
            return Err(PpxError::at_loc(
                item.pstr_loc,
                "the structure is not supported in local extension",
            ));
        }
    }
    Ok(())
}

fn private_extension_item_allowed(item: &StructureItem, arena: &ParseArena) -> bool {
    match &*item.pstr_desc {
        StructureItemDesc::Pstr_eval(_)
        | StructureItemDesc::Pstr_value(_)
        | StructureItemDesc::Pstr_primitive(_)
        | StructureItemDesc::Pstr_typext(_)
        | StructureItemDesc::Pstr_exception(_) => true,
        StructureItemDesc::Pstr_include(incl) => private_extension_include_allowed(incl, arena),
        _ => false,
    }
}

fn private_extension_include_allowed(incl: &IncludeDeclaration, arena: &ParseArena) -> bool {
    let mod_expr = arena.get_mod_expr(incl.pincl_mod);
    let ModuleExprDesc::Pmod_constraint(inner_idx, _) = &*mod_expr.pmod_desc else {
        return false;
    };

    let inner = arena.get_mod_expr(*inner_idx);
    let ModuleExprDesc::Pmod_structure(items) = &*inner.pmod_desc else {
        return false;
    };

    matches!(
        items.as_slice(),
        [item] if matches!(&*item.pstr_desc, StructureItemDesc::Pstr_primitive(_))
    )
}

/// Wraps a set of structure items into a local module + open pair.
/// Used by both single %%private handling and coalesced consecutive %%private handling.
fn wrap_in_local_module(
    rewritten_items: Vec<StructureItem>,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    if rewritten_items.is_empty() {
        return vec![];
    }

    // Generate unique local module name
    let local_name_idx = arena.next_local_module_name();

    // Get the location from the rewritten items
    let first_loc = rewritten_items.first().map(|i| i.pstr_loc).unwrap_or(loc);
    let last_loc = rewritten_items.last().map(|i| i.pstr_loc).unwrap_or(loc);

    // Create a combined location spanning first to last item.
    // OCaml always creates a NEW record via {first_loc with loc_end = last_loc.loc_end},
    // even when first_loc == last_loc. We must always push_loc to avoid sharing with
    // the original parsed item's location.
    let first_location = arena.get_location(first_loc);
    let last_location = arena.get_location(last_loc);
    let combined_loc = arena.push_loc(first_location.loc_start, last_location.loc_end, false);

    // Get none location for the @internal.local attribute
    let none_loc = arena.none_loc();

    // Create @internal.local attribute
    let internal_local_attr: Attribute = (
        Located {
            txt: arena.intern_string("internal.local"),
            loc: none_loc,
        },
        Payload::PStr(Box::new(vec![])),
    );

    // Create the module binding:
    // module local_N = { ... } with @internal.local attribute
    let module_binding = current::ModuleBinding {
        pmb_name: Located {
            txt: local_name_idx,
            loc: combined_loc,
        },
        pmb_expr: arena.push_mod_expr(ModuleExpr {
            pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(rewritten_items))),
            pmod_loc: combined_loc,
            pmod_attributes: Attributes::new(),
        }),
        pmb_attributes: Attributes::from_vec(vec![internal_local_attr]),
        pmb_loc: combined_loc,
    };

    let module_item = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_module(Box::new(module_binding))),
        pstr_loc: combined_loc,
    };

    // Create the open statement:
    // open! local_N
    let local_lident = arena.push_lident_from_idx(local_name_idx);
    let open_desc = current::OpenDescription {
        popen_lid: Located {
            txt: local_lident,
            loc: combined_loc,
        },
        popen_override: current::OverrideFlag::Override,
        popen_loc: combined_loc,
        popen_attributes: Attributes::new(),
    };

    let open_item = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_open(Box::new(open_desc))),
        pstr_loc: combined_loc,
    };

    vec![module_item, open_item]
}

// ========== Async/Await Transformations ==========

/// Transform `await expr` into `Primitive_promise.unsafe_await(expr)`
/// OCaml: ast_await.ml create_await_expression
///
/// The `loc` parameter should be the inner expression's pexp_loc (not the
/// Pexp_await node's loc), matching OCaml: `let loc = {e.pexp_loc with loc_ghost = true}`
fn transform_await(inner: Expression, loc: LocIdx, arena: &mut ParseArena) -> Expression {
    // Create ghost location from the inner expression's location
    let ghost_loc = arena.mk_ghost_loc(loc);

    // Create Primitive_promise.unsafe_await identifier
    let promise_str = arena.intern_string("Primitive_promise");
    let promise_lident = arena.push_lident_from_idx(promise_str);
    let unsafe_await_lid = arena.push_ldot_static(promise_lident, "unsafe_await");

    let func_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: unsafe_await_lid,
            loc: ghost_loc,
        })),
        pexp_loc: ghost_loc,
        pexp_attributes: Attributes::new(),
    };

    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(func_ident),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(inner))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: ghost_loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Wrap expression with `Primitive_promise.unsafe_async(expr)`
/// OCaml: ast_async.ml add_promise_type
///
/// OCaml uses the loc directly (not ghosted): `Ast_helper.Exp.ident ~loc` and
/// `Ast_helper.Exp.apply ~loc`. All three uses of loc (pexp_ident.loc, ident.pexp_loc,
/// apply.pexp_loc) share the same ppat_loc object for pointer-identity-based sharing.
fn wrap_with_unsafe_async(inner: Expression, loc: LocIdx, arena: &mut ParseArena) -> Expression {
    // Create Primitive_promise.unsafe_async identifier
    let promise_str = arena.intern_string("Primitive_promise");
    let promise_lident = arena.push_lident_from_idx(promise_str);
    let unsafe_async_lid = arena.push_ldot_static(promise_lident, "unsafe_async");

    // OCaml uses the same loc object for all three positions
    let func_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: unsafe_async_lid,
            loc,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(func_ident),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(inner))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Recursively find the innermost body of nested Pexp_fun and wrap it with unsafe_async.
/// OCaml: ast_async.ml add_promise_to_result
fn add_promise_to_fun_body(expr: &Expression, loc: LocIdx, arena: &mut ParseArena) -> Expression {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun {
                ref arg_label,
                ref default,
                ref lhs,
                ref rhs,
                ref arity,
                ref is_async,
            } = **inner;
            // Recurse into rhs to find innermost body
            let rhs_expr = arena.get_expr(*rhs).clone();
            let new_rhs = add_promise_to_fun_body(&rhs_expr, loc, arena);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: arg_label.clone(),
                    default: default.clone(),
                    lhs: lhs.clone(),
                    rhs: arena.push_expr(new_rhs),
                    arity: *arity,
                    is_async: *is_async,
                }))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        _ => {
            // This is the innermost body - wrap with unsafe_async
            wrap_with_unsafe_async(expr.clone(), loc, arena)
        }
    }
}

// ========== Module-Level Await Transformation ==========

/// Check if attributes contain @res.await
fn has_await_attribute(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _)| {
        let name = arena.get_string(attr_name.txt);
        name == "res.await"
    })
}

/// Generate a local module type name from a Longident.
/// E.g., `Belt.List` -> `"__Belt_List__"`
/// OCaml: bs_builtin_ppx.ml local_module_type_name
fn local_module_type_name(lid: LidentIdx, arena: &ParseArena) -> String {
    let longident = arena.get_longident(lid);
    let parts = longident.flatten_idx();
    let name = parts
        .iter()
        .map(|s| arena.get_string(*s))
        .collect::<Vec<_>>()
        .join("_");
    format!("__{}__", name)
}

/// Remove @res.await attribute from a list of attributes.
fn remove_await_attribute(attrs: &[Attribute], arena: &ParseArena) -> Vec<Attribute> {
    attrs
        .iter()
        .filter(|(attr_name, _)| {
            let name = arena.get_string(attr_name.txt);
            name != "res.await"
        })
        .cloned()
        .collect()
}

/// Create the await module expression transformation for expression-level await.
///
/// Transforms `@res.await ME` into:
///   `unpack(Primitive_promise.unsafe_await(Primitive_module.import(module(ME: __ME__))))`
///
/// OCaml: ast_await.ml create_await_module_expression
///
/// This is used for expression-level `Pexp_letmodule`:
///   `{ module M = @res.await ME; ... }` -> `{ module M = unpack(...); ... }`
///
/// The `module_type_lid` is the located longident for the module type constraint.
/// The `mod_expr` can be either Pmod_ident or Pmod_constraint - OCaml handles both.
fn create_await_module_expression(
    mod_expr: &current::ModuleExpr,
    module_type_lid: Located<LidentIdx>, // Now includes location!
    arena: &mut ParseArena,
) -> current::ModuleExpr {
    // OCaml uses e.pmod_loc for all generated locations
    let pmod_loc = mod_expr.pmod_loc;

    // Create pack expression: module(ME)
    // OCaml: Exp.pack ~loc:e.pmod_loc {e with pmod_attributes = remove_await_attribute ...}
    // OCaml packs the ENTIRE module expression (could be Pmod_ident OR Pmod_constraint)
    // NOTE: OCaml's remove_await_attribute uses `!=` (physical inequality) which doesn't
    // actually remove the attribute because strings are different objects. So the inner
    // pack expression KEEPS @res.await in the actual output.
    let cleaned_mod_expr = current::ModuleExpr {
        pmod_desc: mod_expr.pmod_desc.clone(), // Keep original desc (Pmod_ident or Pmod_constraint)
        pmod_loc,
        // Keep attributes as-is to match OCaml's actual behavior
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    };

    let pack_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_pack(
            arena.push_mod_expr(cleaned_mod_expr),
        )),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    // Create package type: (__ME__, [])
    // The module_type_lid has its own location from the original source
    let package_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_package(Box::new((
            module_type_lid, // Use the Located<LidentIdx> directly with its location
            vec![],          // No with constraints
        )))),
        ptyp_loc: pmod_loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create constrained expression: (module(ME): __ME__)
    let constrained_pack = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
            arena.push_expr(pack_expr),
            arena.push_core_type(package_type),
        )))),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    // Create Primitive_module.import(constrained_pack)
    let module_str = arena.intern_string("Primitive_module");
    let module_lident = arena.push_lident_from_idx(module_str);
    let import_lid = arena.push_ldot_static(module_lident, "import");

    let import_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: import_lid,
            loc: pmod_loc,
        })),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    let import_apply = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(import_ident),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(constrained_pack))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    // Create Primitive_promise.unsafe_await(import_apply)
    let await_expr = transform_await(import_apply, mod_expr.pmod_loc, arena);

    // Create unpack(await_expr)
    // OCaml: {e with pmod_desc = Pmod_unpack ...} - keeps original pmod_attributes (with @res.await)
    current::ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_unpack(arena.push_expr(await_expr))),
        pmod_loc: mod_expr.pmod_loc,
        // OCaml's {e with pmod_desc = ...} keeps the original attributes including @res.await
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    }
}

/// Spelunk through an expression to find Pexp_letmodule with @res.await attributes.
///
/// For each found, creates a module type declaration to hoist to structure level.
/// Uses a context HashSet to track already-created module type names to avoid duplicates.
///
/// OCaml: bs_builtin_ppx.ml lines 706-752 (spelunk_vbs and aux)
fn spelunk_expression_for_await_module_types(
    expr: &Expression,
    context: &mut std::collections::HashSet<String>,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    match &*expr.pexp_desc {
        // Main case: Pexp_letmodule with Pmod_ident and @res.await
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_, ref mod_expr, ref body) = **inner;
            let mut results = Vec::new();
            let mod_expr_val = arena.get_mod_expr(*mod_expr).clone();

            // Check for Pmod_ident with @res.await
            if let ModuleExprDesc::Pmod_ident(located_lid) = &*mod_expr_val.pmod_desc {
                if has_await_attribute(&mod_expr_val.pmod_attributes, arena) {
                    let module_type_name = local_module_type_name(located_lid.txt, arena);

                    // Only create if not already in context
                    if !context.contains(&module_type_name) {
                        context.insert(module_type_name.clone());

                        // Create module type declaration:
                        // module type __ME__ = module type of ME
                        let module_type_name_idx = arena.intern_string(&module_type_name);
                        let lid_loc = located_lid.loc;

                        let typeof_mod_expr_idx = arena.push_mod_expr(current::ModuleExpr {
                            pmod_desc: Box::new(ModuleExprDesc::Pmod_ident(Located {
                                txt: located_lid.txt,
                                loc: lid_loc,
                            })),
                            // OCaml: Mty.typeof_ ~loc me - `me` keeps its original
                            // pmod_loc allocation (distinct from the lid location).
                            pmod_loc: mod_expr_val.pmod_loc,
                            // OCaml: Mty.typeof_ ~loc me uses original `me` attrs.
                            pmod_attributes: mod_expr_val.pmod_attributes.clone(),
                        });
                        let module_type_idx = arena.push_mod_type(current::ModuleType {
                            pmty_desc: Box::new(ModuleTypeDesc::Pmty_typeof(typeof_mod_expr_idx)),
                            pmty_loc: lid_loc,
                            pmty_attributes: Attributes::new(),
                        });
                        let module_type_decl = StructureItem {
                            pstr_desc: Box::new(StructureItemDesc::Pstr_modtype(Box::new(
                                current::ModuleTypeDeclaration {
                                    pmtd_name: Located {
                                        txt: module_type_name_idx,
                                        loc: lid_loc,
                                    },
                                    pmtd_type: Some(module_type_idx),
                                    pmtd_attributes: Attributes::new(),
                                    pmtd_loc: lid_loc,
                                },
                            ))),
                            pstr_loc: lid_loc,
                        };

                        results.push(module_type_decl);
                    }
                }
            }

            // Continue spelunking into body (body is ExprIdx)
            let body_expr = arena.get_expr(*body).clone();
            results.extend(spelunk_expression_for_await_module_types(
                &body_expr, context, arena,
            ));
            results
        }

        // Recursively traverse other expression forms (matching OCaml's aux function)
        ExpressionDesc::Pexp_let(inner) => {
            let (_, ref bindings, ref body) = **inner;
            let body_expr = arena.get_expr(*body).clone();
            let mut results = spelunk_expression_for_await_module_types(&body_expr, context, arena);
            for vb in bindings {
                let vb_expr = arena.get_expr(vb.pvb_expr).clone();
                results.extend(spelunk_expression_for_await_module_types(
                    &vb_expr, context, arena,
                ));
            }
            results
        }

        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (_, ref then_idx, ref else_idx) = **inner;
            let then_expr = arena.get_expr(*then_idx).clone();
            let mut results = spelunk_expression_for_await_module_types(&then_expr, context, arena);
            if let Some(else_e_idx) = else_idx {
                let else_expr = arena.get_expr(*else_e_idx).clone();
                results.extend(spelunk_expression_for_await_module_types(
                    &else_expr, context, arena,
                ));
            }
            results
        }

        ExpressionDesc::Pexp_construct(_, Some(e_idx)) => {
            let e_expr = arena.get_expr(*e_idx).clone();
            spelunk_expression_for_await_module_types(&e_expr, context, arena)
        }

        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun { rhs: ref body, .. } = **inner;
            let body_expr = arena.get_expr(*body).clone();
            spelunk_expression_for_await_module_types(&body_expr, context, arena)
        }

        ExpressionDesc::Pexp_newtype(inner) => {
            let (_, ref body) = **inner;
            let body_expr = arena.get_expr(*body).clone();
            spelunk_expression_for_await_module_types(&body_expr, context, arena)
        }

        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref e_idx, _) = **inner;
            let e_expr = arena.get_expr(*e_idx).clone();
            spelunk_expression_for_await_module_types(&e_expr, context, arena)
        }

        ExpressionDesc::Pexp_match(inner) => {
            let (ref scrut_idx, ref cases) = **inner;
            let scrut_expr = arena.get_expr(*scrut_idx).clone();
            let mut results =
                spelunk_expression_for_await_module_types(&scrut_expr, context, arena);
            for case in cases {
                let case_rhs = arena.get_expr(case.pc_rhs).clone();
                results.extend(spelunk_expression_for_await_module_types(
                    &case_rhs, context, arena,
                ));
            }
            results
        }

        _ => vec![],
    }
}

/// Spelunk through value bindings to collect module type declarations for hoisting.
///
/// OCaml: bs_builtin_ppx.ml spelunk_vbs
fn spelunk_value_bindings_for_await_module_types(
    bindings: &[ValueBinding],
    context: &mut std::collections::HashSet<String>,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    let mut results = Vec::new();
    for vb in bindings {
        let vb_expr = arena.get_expr(vb.pvb_expr).clone();
        results.extend(spelunk_expression_for_await_module_types(
            &vb_expr, context, arena,
        ));
    }
    results
}

/// Create the module-level await transformation for `module M = @res.await ME`.
/// Returns (optional module type decl, transformed module binding).
///
/// OCaml: bs_builtin_ppx.ml lines 661-702, ast_await.ml create_await_module_expression
///
/// Transforms:
///   `module M = @res.await Belt.List`
/// Into:
///   `module type __Belt_List__ = module type of Belt.List`
///   `module M = unpack(Primitive_promise.unsafe_await(Primitive_module.import(module(Belt.List: __Belt_List__))))`
///
/// Key details from OCaml:
/// - The Pmty_typeof uses the ORIGINAL module expression `me` (with @res.await attribute)
/// - The transformed Pstr_module keeps the ORIGINAL pstr_loc from `item`
/// - The transformed module expr keeps @res.await in pmod_attributes (via {e with pmod_desc = ...})
/// - Only the inner pack expression removes @res.await
fn transform_module_await(
    mb: &current::ModuleBinding,
    original_pstr_loc: LocIdx, // The original structure item location
    arena: &mut ParseArena,
) -> Option<(StructureItem, StructureItem)> {
    // Check if the module expression is Pmod_ident with @res.await attribute
    let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
    if !has_await_attribute(&mod_expr.pmod_attributes, arena) {
        return None;
    }

    // Get the module identifier and its location
    let (lid, lid_loc) = match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_ident(located_lid) => (located_lid.txt, located_lid.loc),
        _ => return None, // Only handle Pmod_ident for now
    };

    // Generate module type name: __Belt_List__
    let module_type_name = local_module_type_name(lid, arena);
    let module_type_name_idx = arena.intern_string(&module_type_name);

    // Locations for generated code:
    // - lid_loc: location of the Longident inside Pmod_ident (used for module type decl)
    // - pmod_loc: location of the module expression (used for import/await expressions)

    // 1. Create module type declaration: module type __Belt_List__ = module type of Belt.List
    // OCaml uses (Mty.typeof_ ~loc me) where `me` is the ORIGINAL module expression
    // This means the Pmty_typeof's inner module expr has the @res.await attribute
    let typeof_mod_expr_idx = arena.push_mod_expr(current::ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_ident(Located {
            txt: lid,
            loc: lid_loc,
        })),
        // OCaml: Mty.typeof_ ~loc me - uses the ORIGINAL `me`, whose pmod_loc
        // was overridden by parse_primary_mod_expr (a fresh allocation, not lid.loc)
        pmod_loc: mod_expr.pmod_loc,
        // OCaml: uses original `me` which has @res.await
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    });
    let module_type_idx = arena.push_mod_type(current::ModuleType {
        pmty_desc: Box::new(current::ModuleTypeDesc::Pmty_typeof(typeof_mod_expr_idx)),
        pmty_loc: lid_loc,
        pmty_attributes: Attributes::new(),
    });
    let module_type_decl = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_modtype(Box::new(
            current::ModuleTypeDeclaration {
                pmtd_name: Located {
                    txt: module_type_name_idx,
                    loc: lid_loc,
                },
                pmtd_type: Some(module_type_idx),
                pmtd_attributes: Attributes::new(),
                pmtd_loc: lid_loc,
            },
        ))),
        pstr_loc: lid_loc,
    };

    // 2. Create the transformed module expression:
    // unpack(Primitive_promise.unsafe_await(Primitive_module.import(module(Belt.List: __Belt_List__))))

    // Create module type lid for constraint: Lident("__Belt_List__")
    let module_type_lid = arena.push_lident_from_idx(module_type_name_idx);

    // Create pack expression: module(Belt.List)
    // OCaml: Exp.pack ~loc:e.pmod_loc {e with pmod_attributes = remove_await_attribute ...}
    // NOTE: OCaml's remove_await_attribute uses `!=` (physical inequality) which doesn't
    // actually remove the attribute because strings are different objects. So the inner
    // pack expression KEEPS @res.await in the actual output.
    let cleaned_mod_expr = current::ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_ident(Located {
            txt: lid,
            loc: lid_loc, // Preserve original Longident location
        })),
        pmod_loc: mod_expr.pmod_loc,
        // Keep attributes as-is to match OCaml's actual behavior (not its intended behavior)
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    };

    // OCaml uses e.pmod_loc for pack, constraint, and package type locations
    let pmod_loc = mod_expr.pmod_loc;

    let pack_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_pack(
            arena.push_mod_expr(cleaned_mod_expr),
        )),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    // Create package type: (Lident("__Belt_List__"), [])
    // module_type_lid location is mb.pmb_expr.pmod_loc in OCaml
    let package_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_package(Box::new((
            Located {
                txt: module_type_lid,
                loc: pmod_loc,
            },
            vec![], // No with constraints
        )))),
        ptyp_loc: pmod_loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create constrained expression: (module(Belt.List): __Belt_List__)
    let constrained_pack = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
            arena.push_expr(pack_expr),
            arena.push_core_type(package_type),
        )))),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    // Create Primitive_module.import(constrained_pack)
    let module_str = arena.intern_string("Primitive_module");
    let module_lident = arena.push_lident_from_idx(module_str);
    let import_lid = arena.push_ldot_static(module_lident, "import");

    let import_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: import_lid,
            loc: pmod_loc,
        })),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    let import_apply = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(import_ident),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(constrained_pack))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    // Create Primitive_promise.unsafe_await(import_apply)
    let await_expr = transform_await(import_apply, mod_expr.pmod_loc, arena);

    // Create unpack(await_expr)
    // OCaml: {e with pmod_desc = Pmod_unpack ...} - keeps original pmod_attributes (with @res.await)
    let transformed_mod_expr = current::ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_unpack(arena.push_expr(await_expr))),
        pmod_loc: mod_expr.pmod_loc,
        // OCaml's {e with pmod_desc = ...} keeps the original attributes including @res.await
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    };

    // Create the transformed module binding
    // OCaml: {item with pstr_desc = Pstr_module {mb with pmb_expr = ...}}
    // This preserves original_pstr_loc (from item), not mb.pmb_loc
    let transformed_mb = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_module(Box::new(
            current::ModuleBinding {
                pmb_name: mb.pmb_name.clone(),
                pmb_expr: arena.push_mod_expr(transformed_mod_expr),
                pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena).into(),
                pmb_loc: mb.pmb_loc,
            },
        ))),
        pstr_loc: original_pstr_loc, // Use original structure item location
    };

    Some((module_type_decl, transformed_mb))
}

// ========== Expression Rewriting ==========

/// Check if an expression is a pipe operator application (a -> b)
fn is_pipe_application(expr: &Expression, arena: &mut ParseArena) -> bool {
    if let ExpressionDesc::Pexp_apply(inner) = &*expr.pexp_desc {
        let PexpApply {
            ref funct,
            ref args,
            ..
        } = **inner;
        if args.len() == 2
            && matches!(&args[0].0, ArgLabel::Nolabel)
            && matches!(&args[1].0, ArgLabel::Nolabel)
        {
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(lid) = &*funct_expr.pexp_desc {
                if let Longident::Lident(op_idx) = arena.get_longident(lid.txt) {
                    let op = arena.get_string(*op_idx);
                    return op == "->";
                }
            }
        }
    }
    false
}

/// Check if expression has a template attribute (@res.template or @res.taggedTemplate)
fn has_template_attr(expr: &Expression, arena: &mut ParseArena) -> bool {
    expr.pexp_attributes.iter().any(|(attr_name, _)| {
        let name = arena.get_string(attr_name.txt);
        name == "res.template" || name == "res.taggedTemplate"
    })
}

/// Transform a JavaScript string to escape special characters.
/// This matches OCaml's Ast_utf8_string.transform function.
fn transform_js_string(s: &str) -> String {
    let mut buf = String::with_capacity(s.len() * 2);
    let bytes = s.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        let b = bytes[i];
        match b {
            b'\\' => {
                // Escape sequence - copy verbatim
                buf.push('\\');
                i += 1;
                if i < bytes.len() {
                    let next = bytes[i];
                    buf.push(next as char);
                    i += 1;
                    // Handle unicode escapes
                    match next {
                        b'u' => {
                            if i < bytes.len() && bytes[i] == b'{' {
                                // Unicode codepoint escape \u{...}
                                while i < bytes.len() {
                                    let c = bytes[i];
                                    buf.push(c as char);
                                    i += 1;
                                    if c == b'}' {
                                        break;
                                    }
                                }
                            } else {
                                // Standard \uXXXX
                                for _ in 0..4 {
                                    if i < bytes.len() {
                                        buf.push(bytes[i] as char);
                                        i += 1;
                                    }
                                }
                            }
                        }
                        b'x' => {
                            // Hex escape \xXX
                            for _ in 0..2 {
                                if i < bytes.len() {
                                    buf.push(bytes[i] as char);
                                    i += 1;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            b'"' => {
                buf.push_str("\\\"");
                i += 1;
            }
            b'\n' => {
                buf.push_str("\\n");
                i += 1;
            }
            b'\r' => {
                buf.push_str("\\r");
                i += 1;
            }
            _ if b < 128 => {
                // ASCII character
                buf.push(b as char);
                i += 1;
            }
            _ => {
                // UTF-8 multi-byte character - copy all bytes as raw bytes
                // We need to push the raw bytes, not convert to char
                let start = i;
                // Determine number of continuation bytes
                let width = if b & 0b1111_0000 == 0b1111_0000 {
                    4
                } else if b & 0b1110_0000 == 0b1110_0000 {
                    3
                } else if b & 0b1100_0000 == 0b1100_0000 {
                    2
                } else {
                    1 // Invalid UTF-8, just copy the byte
                };
                let end = std::cmp::min(start + width, bytes.len());
                // Use from_utf8_lossy to properly preserve the UTF-8 bytes
                if let Ok(utf8_str) = std::str::from_utf8(&bytes[start..end]) {
                    buf.push_str(utf8_str);
                } else {
                    // Invalid UTF-8 - just push bytes as-is (shouldn't happen in valid source)
                    for j in start..end {
                        buf.push(bytes[j] as char);
                    }
                }
                i = end;
            }
        }
    }

    buf
}

/// Transform string constant expression with delimiter.
/// Implements OCaml's Ast_utf8_string_interp.transform_exp.
/// Note: In OCaml, this is an early-return case in expr_mapper that uses
/// `{ e with pexp_desc = ... }`, preserving the original expression's attributes
/// without running them through the default mapper's attribute remapping.
/// We match this behavior by cloning attributes directly instead of calling
/// rewrite_attributes.
fn transform_string_exp(
    expr: &Expression,
    s: &str,
    delim: &str,
    arena: &mut ParseArena,
) -> Expression {
    // Check if this is a template string (has @res.template or @res.taggedTemplate)
    let is_template = has_template_attr(expr, arena);

    if delim == "js" {
        if is_template {
            // Template string: just change delimiter to "bq" (back quotes)
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(Constant::String(
                    Cow::Owned(s.to_string()),
                    Some(Cow::Borrowed("bq")),
                )))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        } else {
            // JS string: transform the string and change delimiter to "*j"
            let transformed = transform_js_string(s);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(Constant::String(
                    Cow::Owned(transformed),
                    Some(Cow::Borrowed("*j")),
                )))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
    } else {
        // Unrecognized delimiter - preserve attributes (matching OCaml's { e with ... })
        Expression {
            pexp_desc: expr.pexp_desc.clone(),
            pexp_loc: expr.pexp_loc,
            pexp_attributes: expr.pexp_attributes.clone(),
        }
    }
}

/// Transform string constant pattern with delimiter.
/// Implements OCaml's Ast_utf8_string_interp.transform_pat.
fn transform_string_pat(pat: &Pattern, s: &str, delim: &str) -> Pattern {
    // Note: patterns don't have template attribute check, since templates are only for expressions
    if delim == "js" {
        // JS string: transform the string and change delimiter to "*j"
        let transformed = transform_js_string(s);
        Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_constant(Box::new(Constant::String(
                Cow::Owned(transformed),
                Some(Cow::Borrowed("*j")),
            )))),
            ppat_loc: pat.ppat_loc,
            ppat_attributes: pat.ppat_attributes.clone(),
        }
    } else {
        // Unrecognized delimiter - return unchanged
        pat.clone()
    }
}

/// Rewrite a single attribute, transforming strings in its payload
fn rewrite_attribute(attr: &Attribute, arena: &mut ParseArena) -> Attribute {
    let (name, payload) = attr;
    (name.clone(), rewrite_payload(payload, arena))
}

/// Rewrite a list of attributes
fn rewrite_attributes(attrs: &[Attribute], arena: &mut ParseArena) -> Vec<Attribute> {
    attrs.iter().map(|a| rewrite_attribute(a, arena)).collect()
}

/// Rewrite a payload, transforming strings in expressions and patterns
fn rewrite_payload(payload: &Payload, arena: &mut ParseArena) -> Payload {
    match payload {
        Payload::PStr(items) => Payload::PStr(Box::new(
            items
                .iter()
                .flat_map(|item| rewrite_structure_item(item, arena))
                .collect(),
        )),
        Payload::PSig(items) => Payload::PSig(Box::new(rewrite_signature_items(items, arena))),
        Payload::PTyp(typ) => Payload::PTyp(*typ),
        Payload::PPat(inner) => {
            let (ref pat_idx, ref guard) = **inner;
            let pat = arena.get_pat(*pat_idx).clone();
            let guard_expr = guard.map(|e| arena.get_expr(e).clone());
            let rw_pat = rewrite_pattern(&pat, arena);
            let rewritten_pat = arena.push_pat(rw_pat);
            let rewritten_guard = guard_expr.as_ref().map(|e| {
                let rw = rewrite_expression(e, arena);
                arena.push_expr(rw)
            });
            Payload::PPat(Box::new((rewritten_pat, rewritten_guard)))
        }
    }
}

fn has_this_attr(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs
        .iter()
        .any(|(attr_name, _)| arena.get_string(attr_name.txt) == "this")
}

/// Process @get/@set attributes on object fields and generate setter fields.
/// Mirrors OCaml's Ast_core_type_class_type.typ_mapper for Ptyp_object.
/// When a field has @set, an additional field `name#=` is generated with type `typ -> unit`.
fn rewrite_object_fields(
    fields: &[ObjectField],
    obj_loc: LocIdx,
    arena: &mut ParseArena,
) -> Vec<ObjectField> {
    let mut result: Vec<ObjectField> = Vec::new();

    for field in fields {
        match field {
            ObjectField::Oinherit(typ_idx) => {
                let typ_ct = arena.get_core_type(*typ_idx).clone();
                let rewritten = rewrite_core_type(&typ_ct, arena);
                result.push(ObjectField::Oinherit(arena.push_core_type(rewritten)));
            }
            ObjectField::Otag(name, attrs, typ_idx) => {
                let mut has_get: Option<(bool, bool)> = None;
                let mut has_set = false;
                let mut no_get = false;
                let mut remaining_attrs: Vec<Attribute> = Vec::new();

                for attr in attrs.iter() {
                    let attr_name = arena.get_string(attr.0.txt);
                    match attr_name {
                        "get" => {
                            let mut null = false;
                            let mut undefined = false;
                            if let Payload::PStr(items) = &attr.1 {
                                for item in items.iter() {
                                    if let StructureItemDesc::Pstr_eval(eval_inner) =
                                        &*item.pstr_desc
                                    {
                                        let (expr_idx, _) = &**eval_inner;
                                        let expr = arena.get_expr(*expr_idx);
                                        if let ExpressionDesc::Pexp_record(record_inner) =
                                            &*expr.pexp_desc
                                        {
                                            let (fields, _) = &**record_inner;
                                            for field in fields.iter() {
                                                let field_name = match arena
                                                    .get_longident(field.lid.txt)
                                                {
                                                    Longident::Lident(s) => arena.get_string(*s),
                                                    _ => "",
                                                };
                                                match field_name {
                                                    "null" => null = true,
                                                    "undefined" => undefined = true,
                                                    "nullable" => {
                                                        null = true;
                                                        undefined = true;
                                                    }
                                                    _ => {}
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            has_get = Some((null, undefined));
                        }
                        "set" => {
                            has_set = true;
                            if let Payload::PStr(items) = &attr.1 {
                                for item in items.iter() {
                                    if let StructureItemDesc::Pstr_eval(eval_inner) =
                                        &*item.pstr_desc
                                    {
                                        let (expr_idx, _) = &**eval_inner;
                                        let expr = arena.get_expr(*expr_idx);
                                        if let ExpressionDesc::Pexp_record(record_inner) =
                                            &*expr.pexp_desc
                                        {
                                            let (fields, _) = &**record_inner;
                                            for field in fields.iter() {
                                                let field_name = match arena
                                                    .get_longident(field.lid.txt)
                                                {
                                                    Longident::Lident(s) => arena.get_string(*s),
                                                    _ => "",
                                                };
                                                if field_name == "no_get" {
                                                    no_get = true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        "this" => {}
                        _ => remaining_attrs.push(attr.clone()),
                    }
                }

                if has_get.is_none() && !has_set {
                    let typ_ct = arena.get_core_type(*typ_idx).clone();
                    let rewritten = rewrite_core_type(&typ_ct, arena);
                    result.push(ObjectField::Otag(
                        name.clone(),
                        rewrite_attributes(attrs, arena).into(),
                        arena.push_core_type(rewritten),
                    ));
                    continue;
                }

                if has_set {
                    let setter_name = format!("{}#=", arena.get_string(name.txt));
                    let setter_name_idx = arena.push_string(setter_name);
                    let setter_name_loc = Located {
                        txt: setter_name_idx,
                        loc: name.loc,
                    };

                    let unit_lid = arena.push_lident("unit");
                    let unit_type = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                            Located {
                                txt: unit_lid,
                                loc: obj_loc,
                            },
                            vec![],
                        )))),
                        ptyp_loc: obj_loc,
                        ptyp_attributes: Attributes::new(),
                    };
                    let unit_idx = arena.push_core_type(unit_type);

                    let typ_ct = arena.get_core_type(*typ_idx).clone();
                    let rewritten_inner = rewrite_core_type(&typ_ct, arena);
                    let rewritten_inner_idx = arena.push_core_type(rewritten_inner);

                    let setter_type = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
                            Box::new(TypeArg {
                                attrs: Attributes::new(),
                                lbl: ArgLabel::Nolabel,
                                typ: rewritten_inner_idx,
                            }),
                            unit_idx,
                            arena.push_arity(Some(1)),
                        )))),
                        ptyp_loc: obj_loc,
                        ptyp_attributes: Attributes::new(),
                    };
                    result.push(ObjectField::Otag(
                        setter_name_loc,
                        remaining_attrs.clone().into(),
                        arena.push_core_type(setter_type),
                    ));
                }

                if !no_get {
                    let typ_ct = arena.get_core_type(*typ_idx).clone();
                    let getter_type = if let Some((null, undefined)) = has_get {
                        match (null, undefined) {
                            (false, false) => rewrite_core_type(&typ_ct, arena),
                            (true, false) => {
                                let inner = rewrite_core_type(&typ_ct, arena);
                                wrap_in_js_type(&inner, "Js", "null", arena)
                            }
                            (false, true) => {
                                let inner = rewrite_core_type(&typ_ct, arena);
                                wrap_in_js_type(&inner, "Js", "undefined", arena)
                            }
                            (true, true) => {
                                let inner = rewrite_core_type(&typ_ct, arena);
                                wrap_in_js_type(&inner, "Js", "null_undefined", arena)
                            }
                        }
                    } else {
                        rewrite_core_type(&typ_ct, arena)
                    };
                    result.push(ObjectField::Otag(
                        name.clone(),
                        remaining_attrs.clone().into(),
                        arena.push_core_type(getter_type),
                    ));
                }
            }
        }
    }

    result
}

/// Wrap a type in Js.wrapper<typ> (e.g., Js.null<typ>, Js.undefined<typ>)
fn wrap_in_js_type(
    typ: &CoreType,
    module_name: &str,
    type_name: &str,
    arena: &mut ParseArena,
) -> CoreType {
    let module_lid = arena.push_lident(module_name);
    let full_lid = arena.push_ldot(module_lid, type_name);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: full_lid,
                loc: typ.ptyp_loc,
            },
            vec![arena.push_core_type(typ.clone())],
        )))),
        ptyp_loc: typ.ptyp_loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Rewrite a core type, recursing into nested types and extension payloads.
/// This matches OCaml's default_mapper.typ behavior, ensuring that expressions
/// inside Ptyp_extension payloads get the "js" -> "*j" delimiter transformation.
fn rewrite_core_type_default(typ: &CoreType, arena: &mut ParseArena) -> CoreType {
    let new_desc = match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_extension(ext) => {
            let (name, payload) = &**ext;
            CoreTypeDesc::Ptyp_extension(Box::new((name.clone(), rewrite_payload(payload, arena))))
        }
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, arity) = &**inner;
            // Current Parsetree maps every n-ary argument in source order.
            let source_args = arena.nary_arrow_args(arg, *arity).into_owned();
            let mut rewritten_args = Vec::with_capacity(source_args.len());
            for source_arg in source_args {
                let source_type = arena.get_core_type(source_arg.typ).clone();
                let rewritten_type = rewrite_core_type(&source_type, arena);
                rewritten_args.push(TypeArg {
                    attrs: source_arg.attrs,
                    lbl: source_arg.lbl,
                    typ: arena.push_core_type(rewritten_type),
                });
            }
            let ret_ct = arena.get_core_type(*ret).clone();
            let rw_ret = rewrite_core_type(&ret_ct, arena);
            let ret_idx = arena.push_core_type(rw_ret);
            let first = rewritten_args[0].clone();
            arena.set_nary_arrow_args(*arity, rewritten_args);
            CoreTypeDesc::Ptyp_arrow(Box::new((Box::new(first), ret_idx, *arity)))
        }
        CoreTypeDesc::Ptyp_tuple(types) => {
            let mut rewritten_types = Vec::with_capacity(types.len());
            for t in types.iter() {
                let ct = arena.get_core_type(*t).clone();
                let rw = rewrite_core_type(&ct, arena);
                rewritten_types.push(arena.push_core_type(rw));
            }
            CoreTypeDesc::Ptyp_tuple(Box::new(rewritten_types))
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            let mut rewritten_args = Vec::with_capacity(args.len());
            for t in args.iter() {
                let ct = arena.get_core_type(*t).clone();
                let rw = rewrite_core_type(&ct, arena);
                rewritten_args.push(arena.push_core_type(rw));
            }
            CoreTypeDesc::Ptyp_constr(Box::new((lid.clone(), rewritten_args)))
        }
        CoreTypeDesc::Ptyp_alias(alias_inner) => {
            let (ref ct_idx, ref name) = **alias_inner;
            let ct = arena.get_core_type(*ct_idx).clone();
            let rw = rewrite_core_type(&ct, arena);
            let idx = arena.push_core_type(rw);
            CoreTypeDesc::Ptyp_alias(Box::new((idx, name.clone())))
        }
        CoreTypeDesc::Ptyp_poly(poly_inner) => {
            let (ref vars, ref ct_idx) = **poly_inner;
            let ct = arena.get_core_type(*ct_idx).clone();
            let rw = rewrite_core_type(&ct, arena);
            let idx = arena.push_core_type(rw);
            CoreTypeDesc::Ptyp_poly(Box::new((vars.clone(), idx)))
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            let (ref fields, ref closed) = **inner;
            // OCaml's Ast_core_type_class_type.typ_mapper processes @get/@set
            // on object fields and generates setter fields (`name#=`) for @set.
            let rewritten_fields = rewrite_object_fields(fields, typ.ptyp_loc, arena);
            CoreTypeDesc::Ptyp_object(Box::new((rewritten_fields, *closed)))
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (ref rows, ref closed, ref labels) = **inner;
            let mut rewritten_rows = Vec::with_capacity(rows.len());
            for row in rows.iter() {
                let rewritten_row = match row {
                    RowField::Rtag(label, attrs, empty, types) => {
                        let mut rewritten_types = Vec::with_capacity(types.len());
                        for t in types.iter() {
                            let ct = arena.get_core_type(*t).clone();
                            let rw = rewrite_core_type(&ct, arena);
                            rewritten_types.push(arena.push_core_type(rw));
                        }
                        RowField::Rtag(
                            label.clone(),
                            rewrite_attributes(attrs, arena).into(),
                            *empty,
                            rewritten_types,
                        )
                    }
                    RowField::Rinherit(typ_idx) => {
                        let ct = arena.get_core_type(*typ_idx).clone();
                        let rw = rewrite_core_type(&ct, arena);
                        RowField::Rinherit(arena.push_core_type(rw))
                    }
                };
                rewritten_rows.push(rewritten_row);
            }
            CoreTypeDesc::Ptyp_variant(Box::new((rewritten_rows, *closed, labels.clone())))
        }
        CoreTypeDesc::Ptyp_package(pkg_inner) => {
            let (lid, constraints) = &**pkg_inner;
            let mut rewritten_constraints = Vec::with_capacity(constraints.len());
            for (loc, typ_idx) in constraints.iter() {
                let ct = arena.get_core_type(*typ_idx).clone();
                let rw = rewrite_core_type(&ct, arena);
                rewritten_constraints.push((loc.clone(), arena.push_core_type(rw)));
            }
            CoreTypeDesc::Ptyp_package(Box::new((lid.clone(), rewritten_constraints)))
        }
        // Ptyp_any, Ptyp_var - no nested types to rewrite
        _ => {
            return CoreType {
                ptyp_desc: typ.ptyp_desc.clone(),
                ptyp_loc: typ.ptyp_loc,
                ptyp_attributes: rewrite_attributes(&typ.ptyp_attributes, arena).into(),
            };
        }
    };
    CoreType {
        ptyp_desc: Box::new(new_desc),
        ptyp_loc: typ.ptyp_loc,
        ptyp_attributes: rewrite_attributes(&typ.ptyp_attributes, arena).into(),
    }
}

/// Rewrite core types with the same `@this` callback handling as OCaml's typ_mapper:
/// `@this` on an uncurried arrow wraps the type in `Js_OO.Callback.arityN`.
fn rewrite_core_type(typ: &CoreType, arena: &mut ParseArena) -> CoreType {
    if let CoreTypeDesc::Ptyp_arrow(inner) = &*typ.ptyp_desc {
        let (_arg, _ret, arity) = &**inner;
        if has_this_attr(&typ.ptyp_attributes, arena) {
            let arity_num = arena
                .get_arity(*arity)
                .expect("@this attribute requires an uncurried arrow with arity");
            let meth_type = rewrite_core_type_default(typ, arena);
            let callback = arena.ppx_js_oo_callback_lid();
            let callback_arity =
                arena.push_ldot_tracked(callback, format!("arity{arity_num}").as_str());
            return CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                    Located {
                        txt: callback_arity,
                        loc: typ.ptyp_loc,
                    },
                    vec![arena.push_core_type(meth_type)],
                )))),
                // OCaml's Ast_helper.Typ.constr default location is Location.none (ghost).
                ptyp_loc: arena.none_loc(),
                ptyp_attributes: Attributes::new(),
            };
        }
    }
    rewrite_core_type_default(typ, arena)
}

/// Rewrite a type declaration, transforming strings in all nested attributes and types
fn rewrite_type_declaration(tdcl: &TypeDeclaration, arena: &mut ParseArena) -> TypeDeclaration {
    let ptype_params = tdcl
        .ptype_params
        .iter()
        .map(|(t, v)| {
            let ct = arena.get_core_type(*t).clone();
            let rw = rewrite_core_type(&ct, arena);
            (arena.push_core_type(rw), *v)
        })
        .collect();
    let ptype_manifest = tdcl.ptype_manifest.as_ref().map(|t| {
        let ct = arena.get_core_type(*t).clone();
        let rw = rewrite_core_type(&ct, arena);
        arena.push_core_type(rw)
    });
    TypeDeclaration {
        ptype_name: tdcl.ptype_name.clone(),
        ptype_params,
        ptype_cstrs: tdcl.ptype_cstrs.clone(),
        ptype_kind: rewrite_type_kind(&tdcl.ptype_kind, arena),
        ptype_private: tdcl.ptype_private,
        ptype_manifest,
        ptype_attributes: rewrite_attributes(&tdcl.ptype_attributes, arena).into(),
        ptype_loc: tdcl.ptype_loc,
    }
}

/// Rewrite a type kind, transforming strings in constructor/label attributes
fn rewrite_type_kind(kind: &TypeKind, arena: &mut ParseArena) -> TypeKind {
    match kind {
        TypeKind::Ptype_abstract => TypeKind::Ptype_abstract,
        TypeKind::Ptype_open => TypeKind::Ptype_open,
        TypeKind::Ptype_variant(constructors) => TypeKind::Ptype_variant(
            constructors
                .iter()
                .map(|ctor| rewrite_constructor_declaration(ctor, arena))
                .collect(),
        ),
        TypeKind::Ptype_record(labels) => TypeKind::Ptype_record(
            labels
                .iter()
                .map(|label| rewrite_label_declaration(label, arena))
                .collect(),
        ),
    }
}

/// Rewrite a constructor declaration, transforming strings in attributes
fn rewrite_constructor_declaration(
    ctor: &ConstructorDeclaration,
    arena: &mut ParseArena,
) -> ConstructorDeclaration {
    let pcd_res = ctor.pcd_res.as_ref().map(|t| {
        let ct = arena.get_core_type(*t).clone();
        let rw = rewrite_core_type(&ct, arena);
        arena.push_core_type(rw)
    });
    ConstructorDeclaration {
        pcd_name: ctor.pcd_name.clone(),
        pcd_args: rewrite_constructor_arguments(&ctor.pcd_args, arena),
        pcd_res,
        pcd_loc: ctor.pcd_loc,
        pcd_attributes: rewrite_attributes(&ctor.pcd_attributes, arena).into(),
    }
}

/// Rewrite constructor arguments, transforming strings in nested record labels
fn rewrite_constructor_arguments(
    args: &ConstructorArguments,
    arena: &mut ParseArena,
) -> ConstructorArguments {
    match args {
        ConstructorArguments::Pcstr_tuple(types) => {
            let rewritten = types
                .iter()
                .map(|t| {
                    let ct = arena.get_core_type(*t).clone();
                    let rw = rewrite_core_type(&ct, arena);
                    arena.push_core_type(rw)
                })
                .collect();
            ConstructorArguments::Pcstr_tuple(rewritten)
        }
        ConstructorArguments::Pcstr_record(labels) => ConstructorArguments::Pcstr_record(
            labels
                .iter()
                .map(|label| rewrite_label_declaration(label, arena))
                .collect(),
        ),
    }
}

/// Rewrite a label declaration (record field), transforming strings in attributes and types
fn rewrite_label_declaration(label: &LabelDeclaration, arena: &mut ParseArena) -> LabelDeclaration {
    let label_type = arena.get_core_type(label.pld_type).clone();
    let rewritten_label_type = rewrite_core_type(&label_type, arena);
    let mut pld_name = label.pld_name;
    let mut pld_attributes = rewrite_attributes(&label.pld_attributes, arena);
    if pld_attributes.len() == 1 && arena.get_string(pld_attributes[0].0.txt) == "internal" {
        let capitalized = capitalize_ascii(arena.get_string(pld_name.txt));
        pld_name.txt = arena.push_string(capitalized);
        pld_attributes.clear();
    }
    LabelDeclaration {
        pld_name,
        pld_mutable: label.pld_mutable,
        pld_type: arena.push_core_type(rewritten_label_type),
        pld_loc: label.pld_loc,
        pld_attributes: pld_attributes.into(),
        pld_optional: label.pld_optional,
    }
}

fn capitalize_ascii(s: &str) -> String {
    let mut bytes = s.as_bytes().to_vec();
    if let Some(first) = bytes.first_mut() {
        *first = first.to_ascii_uppercase();
    }
    String::from_utf8(bytes).expect("capitalizing ASCII cannot invalidate UTF-8")
}

// ============================================================================
// Tuple pattern flattening
// ============================================================================
//
// Desugars tuple let-bindings into individual bindings:
//   let (a, b) = (1, 2)        →  let a = 1 and b = 2
//   let (a, b) = M.N.(c, d)    →  let a = M.N.c and b = M.N.d
//
// This mirrors compiler/frontend/ast_tuple_pattern_flatten.ml and
// compiler/frontend/ast_open_cxt.ml from the OCaml codebase.

/// Context for an open expression wrapping a tuple
struct OpenCtx {
    flag: current::OverrideFlag,
    lid: Located<LidentIdx>,
    loc: LocIdx,
    attrs: Vec<Attribute>,
}

/// Check if a pattern is "simple" enough for tuple flattening
fn is_simple_pattern(p: &Pattern, arena: &ParseArena) -> bool {
    match &*p.ppat_desc {
        PatternDesc::Ppat_any => true,
        PatternDesc::Ppat_var(_) => true,
        PatternDesc::Ppat_constraint(inner) => {
            let (ref inner_idx, _) = **inner;
            is_simple_pattern(arena.get_pat(*inner_idx), arena)
        }
        _ => false,
    }
}

/// Destructure an expression through Pexp_open chains to find a tuple.
/// Returns (open_contexts, tuple_elements) if the expression is a
/// (possibly open-wrapped) tuple.
///
/// The open contexts are accumulated in reverse order (innermost first),
/// matching the OCaml implementation.
fn destruct_open_tuple(
    e: &Expression,
    arena: &ParseArena,
) -> Option<(Vec<OpenCtx>, Vec<Expression>)> {
    destruct_open_tuple_inner(e, Vec::new(), arena)
}

fn destruct_open_tuple_inner(
    e: &Expression,
    mut acc: Vec<OpenCtx>,
    arena: &ParseArena,
) -> Option<(Vec<OpenCtx>, Vec<Expression>)> {
    match &*e.pexp_desc {
        ExpressionDesc::Pexp_open(inner) => {
            let (ref flag, ref lid, ref cont) = **inner;
            acc.push(OpenCtx {
                flag: *flag,
                lid: *lid,
                loc: e.pexp_loc,
                attrs: e.pexp_attributes.to_vec(),
            });
            let cont_expr = arena.get_expr(*cont);
            destruct_open_tuple_inner(cont_expr, acc, arena)
        }
        ExpressionDesc::Pexp_tuple(es) => {
            Some((acc, es.iter().map(|e| arena.get_expr(*e).clone()).collect()))
        }
        _ => None,
    }
}

/// Restore open expression wrappers around an expression.
/// The opens list is in reverse order (innermost first), so we fold left
/// to rebuild the nesting correctly.
fn restore_exp(expr: Expression, opens: &[OpenCtx], arena: &mut ParseArena) -> Expression {
    opens.iter().fold(expr, |inner, open| Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_open(Box::new((
            open.flag,
            open.lid,
            arena.push_expr(inner),
        )))),
        pexp_loc: open.loc,
        pexp_attributes: open.attrs.clone().into(),
    })
}

fn rewrite_value_binding_without_flattening(
    vb: &ValueBinding,
    arena: &mut ParseArena,
) -> ValueBinding {
    let vb_pat = arena.get_pat(vb.pvb_pat).clone();
    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
    let pvb_pat = rewrite_pattern(&vb_pat, arena);
    let pvb_expr = rewrite_expression(&vb_expr, arena);
    let pvb_attributes = rewrite_attributes(&vb.pvb_attributes, arena);
    ValueBinding {
        pvb_pat: arena.push_pat(pvb_pat),
        pvb_expr: arena.push_expr(pvb_expr),
        pvb_attributes: pvb_attributes.into(),
        pvb_loc: vb.pvb_loc,
    }
}

fn rewrite_value_bindings_without_flattening(
    bindings: &[ValueBinding],
    arena: &mut ParseArena,
) -> Vec<ValueBinding> {
    bindings
        .iter()
        .map(|vb| rewrite_value_binding_without_flattening(vb, arena))
        .collect()
}

/// Flatten a single value binding into one or more bindings.
/// If the binding is a tuple pattern matched against a tuple expression
/// (possibly wrapped in open expressions), desugar into individual bindings.
fn flatten_value_binding(vb: &ValueBinding, arena: &mut ParseArena) -> Vec<ValueBinding> {
    let vb_pat = arena.get_pat(vb.pvb_pat).clone();
    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
    let pvb_pat = rewrite_pattern(&vb_pat, arena);
    let pvb_expr = rewrite_expression(&vb_expr, arena);
    let pvb_attributes = rewrite_attributes(&vb.pvb_attributes, arena);

    if let PatternDesc::Ppat_tuple(ref pats) = *pvb_pat.ppat_desc {
        if pats
            .iter()
            .all(|p| is_simple_pattern(arena.get_pat(*p), arena))
        {
            if let Some((opens, exprs)) = destruct_open_tuple(&pvb_expr, arena) {
                if exprs.len() == pats.len() {
                    return pats
                        .iter()
                        .zip(exprs.iter())
                        .map(|(pat, expr)| {
                            let restored = restore_exp(expr.clone(), &opens, arena);
                            let restored_idx = arena.push_expr(restored);
                            ValueBinding {
                                pvb_pat: *pat,
                                pvb_expr: restored_idx,
                                pvb_attributes: pvb_attributes.clone().into(),
                                pvb_loc: vb.pvb_loc,
                            }
                        })
                        .collect();
                }
            }
        }
    }

    // OCaml ast_tuple_pattern_flatten:
    // | Ppat_record (lid_pats, _), Pexp_pack {pmod_desc = Pmod_ident id} -> ...
    if let (PatternDesc::Ppat_record(record_inner), ExpressionDesc::Pexp_pack(mod_expr_idx)) =
        (&*pvb_pat.ppat_desc, &*pvb_expr.pexp_desc)
    {
        let (ref lid_pats, _) = **record_inner;
        let mod_expr = arena.get_mod_expr(*mod_expr_idx);
        let module_lid = if let ModuleExprDesc::Pmod_ident(lid) = &*mod_expr.pmod_desc {
            *lid
        } else {
            return vec![ValueBinding {
                pvb_pat: arena.push_pat(pvb_pat),
                pvb_expr: arena.push_expr(pvb_expr),
                pvb_attributes: pvb_attributes.into(),
                pvb_loc: vb.pvb_loc,
            }];
        };
        let module_longident = arena.get_longident(module_lid.txt).clone();
        let mut flattened = Vec::with_capacity(lid_pats.len());

        for field in lid_pats {
            let field_name = match arena.get_longident(field.lid.txt) {
                Longident::Lident(name) => *name,
                _ => {
                    return vec![ValueBinding {
                        pvb_pat: arena.push_pat(pvb_pat.clone()),
                        pvb_expr: arena.push_expr(pvb_expr.clone()),
                        pvb_attributes: pvb_attributes.clone().into(),
                        pvb_loc: vb.pvb_loc,
                    }];
                }
            };

            let projected_lid = arena.push_longident(Longident::Ldot(
                Box::new(module_longident.clone()),
                field_name,
            ));
            let projected_loc = field.lid.loc;

            let pvb_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                    txt: projected_lid,
                    loc: projected_loc,
                })),
                pexp_loc: projected_loc,
                pexp_attributes: Attributes::new(),
            };
            let pat_loc = arena.get_pat(field.pat).ppat_loc;
            flattened.push(ValueBinding {
                pvb_pat: field.pat,
                pvb_expr: arena.push_expr(pvb_expr),
                pvb_attributes: Attributes::new(),
                pvb_loc: pat_loc,
            });
        }

        return flattened;
    }

    vec![ValueBinding {
        pvb_pat: arena.push_pat(pvb_pat),
        pvb_expr: arena.push_expr(pvb_expr),
        pvb_attributes: pvb_attributes.into(),
        pvb_loc: vb.pvb_loc,
    }]
}

/// Flatten a list of value bindings, expanding tuple patterns.
fn flatten_value_bindings(bindings: &[ValueBinding], arena: &mut ParseArena) -> Vec<ValueBinding> {
    bindings
        .iter()
        .flat_map(|vb| flatten_value_binding(vb, arena))
        .collect()
}

/// Rewrite a pattern, transforming string and integer constants.
/// This recursively processes all nested patterns, matching OCaml's default_mapper.pat behavior.
fn rewrite_pattern(pat: &Pattern, arena: &mut ParseArena) -> Pattern {
    let attrs = rewrite_attributes(&pat.ppat_attributes, arena);

    let desc = match &*pat.ppat_desc {
        PatternDesc::Ppat_constant(c) => match &**c {
            // String constant with delimiter: transform js -> *j
            Constant::String(s, Some(delim)) => {
                let base = transform_string_pat(pat, s, delim);
                return Pattern {
                    ppat_attributes: attrs.into(),
                    ..base
                };
            }
            // Strip 'l' suffix from integer literals
            Constant::Integer(s, Some('l')) => {
                PatternDesc::Ppat_constant(Box::new(Constant::Integer(s.clone(), None)))
            }
            // Other constants: no transformation needed
            _ => PatternDesc::Ppat_constant(c.clone()),
        },

        // Alias pattern: recurse into the aliased pattern
        PatternDesc::Ppat_alias(inner_idx, name) => {
            let inner_pat = arena.get_pat(*inner_idx).clone();
            let rw = rewrite_pattern(&inner_pat, arena);
            PatternDesc::Ppat_alias(arena.push_pat(rw), name.clone())
        }

        // Tuple pattern: recurse into all elements
        PatternDesc::Ppat_tuple(pats) => {
            let rewritten_pats = pats
                .iter()
                .map(|p| {
                    let pat = arena.get_pat(*p).clone();
                    let rw = rewrite_pattern(&pat, arena);
                    arena.push_pat(rw)
                })
                .collect();
            PatternDesc::Ppat_tuple(Box::new(rewritten_pats))
        }

        // Constructor pattern: recurse into optional payload
        PatternDesc::Ppat_construct(lid, opt_p) => {
            let cloned = opt_p.map(|p| arena.get_pat(p).clone());
            let rw = cloned.map(|p| {
                let rw = rewrite_pattern(&p, arena);
                arena.push_pat(rw)
            });
            PatternDesc::Ppat_construct(lid.clone(), rw)
        }

        // Variant pattern: recurse into optional payload
        PatternDesc::Ppat_variant(inner) => {
            let (ref label, ref opt_p) = **inner;
            let cloned = opt_p.map(|p| arena.get_pat(p).clone());
            let rw = cloned.map(|p| {
                let rw = rewrite_pattern(&p, arena);
                arena.push_pat(rw)
            });
            PatternDesc::Ppat_variant(Box::new((label.clone(), rw)))
        }

        // Record pattern: recurse into all field patterns
        PatternDesc::Ppat_record(inner) => {
            let (ref fields, ref flag) = **inner;
            PatternDesc::Ppat_record(Box::new((
                fields
                    .iter()
                    .map(|f| {
                        let pat = arena.get_pat(f.pat).clone();
                        let rw_pat = rewrite_pattern(&pat, arena);
                        PatternRecordField {
                            lid: f.lid.clone(),
                            pat: arena.push_pat(rw_pat),
                            opt: f.opt,
                        }
                    })
                    .collect(),
                *flag,
            )))
        }

        // Array pattern: recurse into all elements
        PatternDesc::Ppat_array(pats) => {
            let rewritten_pats = pats
                .iter()
                .map(|p| {
                    let pat = arena.get_pat(*p).clone();
                    let rw = rewrite_pattern(&pat, arena);
                    arena.push_pat(rw)
                })
                .collect();
            PatternDesc::Ppat_array(Box::new(rewritten_pats))
        }

        // Or pattern: recurse into both alternatives
        PatternDesc::Ppat_or(p1, p2) => {
            let p1_pat = arena.get_pat(*p1).clone();
            let p2_pat = arena.get_pat(*p2).clone();
            let rw1 = rewrite_pattern(&p1_pat, arena);
            let rw2 = rewrite_pattern(&p2_pat, arena);
            PatternDesc::Ppat_or(arena.push_pat(rw1), arena.push_pat(rw2))
        }

        // Constraint pattern: recurse into pattern and type
        PatternDesc::Ppat_constraint(inner) => {
            let (ref inner_pat_idx, ref core_type) = **inner;
            let inner_pat = arena.get_pat(*inner_pat_idx).clone();
            let core_type_val = arena.get_core_type(*core_type).clone();
            let rw_pat = rewrite_pattern(&inner_pat, arena);
            let rw_typ = rewrite_core_type(&core_type_val, arena);
            PatternDesc::Ppat_constraint(Box::new((
                arena.push_pat(rw_pat),
                arena.push_core_type(rw_typ),
            )))
        }

        // Exception pattern: recurse into inner pattern
        PatternDesc::Ppat_exception(inner_idx) => {
            let inner_pat = arena.get_pat(*inner_idx).clone();
            let rw = rewrite_pattern(&inner_pat, arena);
            PatternDesc::Ppat_exception(arena.push_pat(rw))
        }

        // Open pattern: recurse into inner pattern
        PatternDesc::Ppat_open(lid, inner_idx) => {
            let inner_pat = arena.get_pat(*inner_idx).clone();
            let rw = rewrite_pattern(&inner_pat, arena);
            PatternDesc::Ppat_open(lid.clone(), arena.push_pat(rw))
        }

        // Patterns without nested patterns: clone as-is
        PatternDesc::Ppat_any => PatternDesc::Ppat_any,
        PatternDesc::Ppat_var(name) => PatternDesc::Ppat_var(name.clone()),
        PatternDesc::Ppat_interval(inner) => PatternDesc::Ppat_interval(inner.clone()),
        PatternDesc::Ppat_type(lid) => PatternDesc::Ppat_type(lid.clone()),
        PatternDesc::Ppat_unpack(name) => PatternDesc::Ppat_unpack(name.clone()),
        PatternDesc::Ppat_extension(ext) => {
            let (ref name, ref payload) = **ext;
            PatternDesc::Ppat_extension(Box::new((name.clone(), rewrite_payload(payload, arena))))
        }
    };

    Pattern {
        ppat_desc: Box::new(desc),
        ppat_loc: pat.ppat_loc,
        ppat_attributes: attrs.into(),
    }
}

/// OCaml async rewriting uses the mapped lhs pattern location, and for
/// `Ppat_var` that location is pointer-identical to `name.loc`. Keep the same
/// identity when arena indices differ but location contents are equal.
fn async_lhs_loc(lhs: &Pattern, _arena: &ParseArena) -> LocIdx {
    if let PatternDesc::Ppat_var(name) = &*lhs.ppat_desc {
        return name.loc;
    }
    lhs.ppat_loc
}

fn split_this_attrs(attrs: &[Attribute], arena: &ParseArena) -> (bool, Vec<Attribute>) {
    let mut has_this = false;
    let mut remaining = Vec::new();
    for attr in attrs {
        if arena.get_string(attr.0.txt) == "this" {
            has_this = true;
        } else {
            remaining.push(attr.clone());
        }
    }
    // OCaml's process_attributes_rev uses fold_left with cons, so non-"this" attrs are reversed.
    remaining.reverse();
    (has_this, remaining)
}

/// Mirrors OCaml's ast_uncurry_gen.to_method_callback for `fun [@this]`.
fn rewrite_method_callback_expression(
    expr: &Expression,
    arg_label: &ArgLabel,
    lhs: PatIdx,
    rhs: ExprIdx,
    is_async: bool,
    filtered_attrs: Vec<Attribute>,
    arena: &mut ParseArena,
) -> Expression {
    let loc = expr.pexp_loc;
    let self_pat = arena.get_pat(lhs).clone();
    let rewritten_self_pat = rewrite_pattern(&self_pat, arena);

    let mut rev_extra_args: Vec<(ArgLabel, Pattern, Vec<Attribute>, bool)> =
        vec![(arg_label.clone(), rewritten_self_pat, vec![], false)];

    let mut current_body = arena.get_expr(rhs).clone();
    let result = loop {
        let (has_this_attr, body_attrs) = split_this_attrs(&current_body.pexp_attributes, arena);
        if has_this_attr {
            break rewrite_expression(&current_body, arena);
        }
        match &*current_body.pexp_desc {
            ExpressionDesc::Pexp_fun(inner) => {
                let PexpFun {
                    arg_label: inner_label,
                    lhs: inner_lhs,
                    rhs: inner_rhs,
                    is_async: inner_async,
                    ..
                } = &**inner;
                let inner_pat = arena.get_pat(*inner_lhs).clone();
                let rewritten_inner_pat = rewrite_pattern(&inner_pat, arena);
                rev_extra_args.push((
                    inner_label.clone(),
                    rewritten_inner_pat,
                    body_attrs,
                    *inner_async,
                ));
                current_body = arena.get_expr(*inner_rhs).clone();
            }
            _ => break rewrite_expression(&current_body, arena),
        }
    };

    let mut method_body = result;
    for (label, pat, attrs, arg_async) in rev_extra_args.iter().rev() {
        method_body = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label: label.clone(),
                default: None,
                lhs: arena.push_pat(pat.clone()),
                rhs: arena.push_expr(method_body),
                arity: arena.static_arity_none(),
                is_async: *arg_async,
            }))),
            pexp_loc: loc,
            pexp_attributes: attrs.clone().into(),
        };
    }

    let total_arity = rev_extra_args.len() as i32;
    if let ExpressionDesc::Pexp_fun(inner) = &*method_body.pexp_desc {
        let PexpFun {
            arg_label: outer_label,
            default: outer_default,
            lhs: outer_lhs,
            rhs: outer_rhs,
            ..
        } = &**inner;
        method_body = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label: outer_label.clone(),
                default: *outer_default,
                lhs: *outer_lhs,
                rhs: *outer_rhs,
                arity: arena.push_arity(Some(total_arity)),
                is_async,
            }))),
            pexp_loc: method_body.pexp_loc,
            pexp_attributes: method_body.pexp_attributes.clone(),
        };
    }

    if is_async {
        let async_loc = match &*method_body.pexp_desc {
            ExpressionDesc::Pexp_fun(inner) => {
                let lhs_pat = arena.get_pat(inner.lhs).clone();
                async_lhs_loc(&lhs_pat, arena)
            }
            _ => loc,
        };
        method_body = add_promise_to_fun_body(&method_body, async_loc, arena);
    }

    let js_oo = arena.ppx_js_oo_lident();
    let unsafe_to_method = arena.push_ldot_tracked_static(js_oo, "unsafe_to_method");
    let callback = arena.ppx_js_oo_callback_lid();
    let callback_arity = arena.push_ldot_tracked(callback, format!("arity{total_arity}").as_str());

    let hidden_field_name = format!("I{total_arity}");
    let hidden_field = arena.push_lident(hidden_field_name.as_str());
    let method_record = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((
            vec![ExpressionRecordField {
                lid: Located {
                    txt: hidden_field,
                    loc,
                },
                expr: arena.push_expr(method_body),
                opt: false,
            }],
            None,
        )))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    let callback_any_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: callback_arity,
                loc,
            },
            vec![arena.push_core_type(CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            })],
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    };

    let constrained_method = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
            arena.push_expr(method_record),
            arena.push_core_type(callback_any_type),
        )))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                    txt: unsafe_to_method,
                    loc,
                })),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(constrained_method))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: filtered_attrs.into(),
    }
}

/// Rewrite an expression, desugaring pipe operators
fn rewrite_expression(expr: &Expression, arena: &mut ParseArena) -> Expression {
    // Handle string constant transformations first
    if let ExpressionDesc::Pexp_constant(c) = &*expr.pexp_desc {
        if let Constant::String(s, Some(delim)) = &**c {
            return transform_string_exp(expr, s, delim, arena);
        }
    }

    // Handle integer literal suffix stripping ('l' suffix)
    // OCaml: {e with pexp_desc = Pexp_constant (Pconst_integer (s, None))}
    // This is an early-return case that preserves attributes without remapping.
    if let ExpressionDesc::Pexp_constant(c) = &*expr.pexp_desc {
        if let Constant::Integer(s, Some('l')) = &**c {
            return Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(Constant::Integer(
                    s.clone(),
                    None,
                )))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            };
        }
    }

    // First check if this is a pipe or #= application
    if let ExpressionDesc::Pexp_apply(inner) = &*expr.pexp_desc {
        let PexpApply {
            ref funct,
            ref args,
            ..
        } = **inner;
        // Check if this is a binary op: -> or #= with two args
        if args.len() == 2
            && matches!(&args[0].0, ArgLabel::Nolabel)
            && matches!(&args[1].0, ArgLabel::Nolabel)
        {
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(lid) = &*funct_expr.pexp_desc {
                if let Longident::Lident(op_idx) = arena.get_longident(lid.txt) {
                    let op = arena.get_string(*op_idx);
                    if op == "->" {
                        // This is a pipe: a -> f
                        // First recursively rewrite both arguments
                        let a_expr = arena.get_expr(args[0].1).clone();
                        let f_expr = arena.get_expr(args[1].1).clone();
                        let a = rewrite_expression(&a_expr, arena);
                        let f = rewrite_expression(&f_expr, arena);

                        // Now desugar based on what f is
                        return desugar_pipe(expr, a, f, arena);
                    }
                    if op == "#=" {
                        // This is a setter: obj["prop"] = value
                        // OCaml transforms: Pexp_apply("#=", [Pexp_send(obj, name), value])
                        // Into: Pexp_constraint(Box::new((Pexp_apply(Pexp_send(obj, name^"#="), [value]), unit)))
                        let obj_expr = arena.get_expr(args[0].1).clone();
                        let value_expr = arena.get_expr(args[1].1).clone();
                        return desugar_hash_set(expr, &obj_expr, &value_expr, arena);
                    }
                }
            }
        }
    }

    // Not a pipe or #= - recursively rewrite sub-expressions
    rewrite_expression_generic(expr, arena)
}

/// Desugar #= setter: obj["prop"] = value
///
/// Transforms `Pexp_apply("#=", [obj_expr, value])` where obj_expr is:
/// - `Pexp_send(Box::new((obj, {txt=name})))`: becomes
///   `Pexp_constraint(Box::new((Pexp_apply(Pexp_send(obj, name^"#="), [value]), unit)))`
///
/// This matches OCaml's `ast_exp_apply.ml` gen_assignment.
fn desugar_hash_set(
    expr: &Expression,
    obj_expr: &Expression,
    value_expr: &Expression,
    arena: &mut ParseArena,
) -> Expression {
    let loc = expr.pexp_loc;

    match &*obj_expr.pexp_desc {
        ExpressionDesc::Pexp_send(inner) => {
            let (ref obj_idx, ref method_loc) = **inner;
            let obj_expr_cloned = arena.get_expr(*obj_idx).clone();
            let obj = rewrite_expression(&obj_expr_cloned, arena);
            let value = rewrite_expression(value_expr, arena);

            // Concatenate name with "#=" suffix
            let setter_name = format!("{}#=", method_loc.txt);

            // Create Pexp_send(Box::new((obj, "name#="))) with the outer loc
            let send_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_send(Box::new((
                    arena.push_expr(obj),
                    Located::new(Cow::Owned(setter_name), loc),
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            };

            // Create Pexp_apply(send_expr, [(Nolabel, value)]) with the outer loc
            let apply_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                    funct: arena.push_expr(send_expr),
                    args: vec![(ArgLabel::Nolabel, arena.push_expr(value))],
                    partial: false,
                    transformed_jsx: false,
                }))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            };

            // Reuse static Lident("unit") to mirror OCaml's Ast_literal.Lid.type_unit sharing.
            let unit_lid_idx = arena.push_lident_static("unit");
            let unit_type = CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                    Located::new(unit_lid_idx, loc),
                    vec![],
                )))),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            };

            // Wrap in Pexp_constraint
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    arena.push_expr(apply_expr),
                    arena.push_core_type(unit_type),
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        _ => {
            // Fallback: just rewrite sub-expressions generically
            rewrite_expression_generic(expr, arena)
        }
    }
}

/// Check if an expression doesn't need to be bound in a let-binding
/// (i.e., it's a simple identifier or a constraint on a simple identifier).
/// Matches OCaml's `no_need_bound` in ast_exp_apply.ml.
fn no_need_bound(exp: &Expression, arena: &ParseArena) -> bool {
    match &*exp.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => {
            matches!(arena.get_longident(lid.txt), Longident::Lident(_))
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref e_idx, _) = **inner;
            no_need_bound(arena.get_expr(*e_idx), arena)
        }
        _ => false,
    }
}

/// Apply a pipe-to-tuple distribution.
/// If `a` is a simple ident, use it directly in each tuple element.
/// Otherwise, bind it: `let __tuple_internal_obj = a in (f1(obj), f2(obj), ...)`
/// Matches OCaml's `bound` function in ast_exp_apply.ml.
fn pipe_tuple_bound(
    a: Expression,
    xs: &[ExprIdx],
    f: &Expression,
    arena: &mut ParseArena,
) -> Expression {
    if no_need_bound(&a, arena) {
        pipe_tuple_map(a, xs, f, arena)
    } else {
        // Create: let __tuple_internal_obj = a in (mapped tuple)
        let obj_name = arena.intern("__tuple_internal_obj");
        let obj_lid = arena.push_lident_from_idx(obj_name);
        let obj_loc = a.pexp_loc;

        // The identifier expression for the bound variable
        let obj_ident_expr = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: obj_lid,
                loc: obj_loc,
            })),
            pexp_loc: obj_loc,
            pexp_attributes: Attributes::new(),
        };

        let mapped = pipe_tuple_map(obj_ident_expr, xs, f, arena);

        let pat = Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                txt: obj_name,
                loc: obj_loc,
            })),
            ppat_loc: obj_loc,
            ppat_attributes: Attributes::new(),
        };
        let pat_idx = arena.push_pat(pat);
        let a_idx = arena.push_expr(a);
        let mapped_idx = arena.push_expr(mapped);

        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                RecFlag::Nonrecursive,
                vec![ValueBinding {
                    pvb_pat: pat_idx,
                    pvb_expr: a_idx,
                    pvb_attributes: Attributes::new(),
                    pvb_loc: obj_loc,
                }],
                mapped_idx,
            )))),
            pexp_loc: obj_loc,
            pexp_attributes: Attributes::new(),
        }
    }
}

/// Map each tuple element to apply the piped argument.
/// For each element fn in the tuple:
/// - Pexp_construct(ctor, None) -> Pexp_construct(ctor, Some(a))
/// - Pexp_apply(fn1, args) -> Pexp_apply(fn1, (Nolabel, a) :: args)
/// - otherwise -> fn(a) = Pexp_apply(fn, [(Nolabel, a)])
/// Matches OCaml's Ext_list.map in ast_exp_apply.ml lines 105-128.
fn pipe_tuple_map(
    a: Expression,
    xs: &[ExprIdx],
    f: &Expression,
    arena: &mut ParseArena,
) -> Expression {
    let mapped: Vec<ExprIdx> = xs
        .iter()
        .map(|fn_expr_idx| {
            let fn_expr = arena.get_expr(*fn_expr_idx).clone();
            let result = match &*fn_expr.pexp_desc {
                ExpressionDesc::Pexp_construct(ctor, None) => {
                    let a_idx = arena.push_expr(a.clone());
                    Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                            ctor.clone(),
                            Some(a_idx),
                        )),
                        pexp_loc: fn_expr.pexp_loc,
                        pexp_attributes: fn_expr.pexp_attributes.clone(),
                    }
                }
                ExpressionDesc::Pexp_apply(inner) => {
                    let PexpApply {
                        ref funct,
                        ref args,
                        transformed_jsx,
                        ..
                    } = **inner;
                    let mut new_args = Vec::with_capacity(args.len() + 1);
                    let a_idx = arena.push_expr(a.clone());
                    new_args.push((ArgLabel::Nolabel, a_idx));
                    new_args.extend(args.iter().map(|(lbl, e)| (lbl.clone(), *e)));
                    let funct_loc = arena.get_expr(*funct).pexp_loc;
                    Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                            funct: *funct,
                            args: new_args,
                            partial: false,
                            transformed_jsx,
                        }))),
                        pexp_loc: funct_loc,
                        pexp_attributes: Attributes::new(),
                    }
                }
                _ => {
                    let fn_expr_idx_for_funct = arena.push_expr(fn_expr.clone());
                    let a_idx = arena.push_expr(a.clone());
                    Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                            funct: fn_expr_idx_for_funct,
                            args: vec![(ArgLabel::Nolabel, a_idx)],
                            partial: false,
                            transformed_jsx: false,
                        }))),
                        pexp_loc: fn_expr.pexp_loc,
                        pexp_attributes: Attributes::new(),
                    }
                }
            };
            arena.push_expr(result)
        })
        .collect();

    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_tuple(Box::new(mapped))),
        pexp_attributes: f.pexp_attributes.clone(),
        pexp_loc: f.pexp_loc,
    }
}

/// Desugar pipe expression: a -> f
/// Transforms based on what f is:
/// - f is Pexp_variant(Box::new((label, None))): becomes Pexp_variant(Box::new((label, Some(a))))
/// - f is Pexp_construct(ctor, None): becomes Pexp_construct(ctor, Some(a))
/// - f is Pexp_apply(fn1, args): becomes Pexp_apply(fn1, (Nolabel, a) :: args)
/// - f is Pexp_tuple(Box::new(xs)): binds a and maps each element
/// - otherwise: becomes f(a) = Pexp_apply(f, [(Nolabel, a)])
fn desugar_pipe(
    original: &Expression,
    a: Expression,
    f: Expression,
    arena: &mut ParseArena,
) -> Expression {
    match &*f.pexp_desc {
        // a -> `Variant becomes `Variant(a)
        ExpressionDesc::Pexp_variant(inner) => {
            let (ref label, ref _none) = **inner;
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_variant(Box::new((
                    label.clone(),
                    Some(arena.push_expr(a)),
                )))),
                pexp_loc: original.pexp_loc,
                pexp_attributes: original.pexp_attributes.clone(),
            }
        }

        // a -> Constructor becomes Constructor(a)
        ExpressionDesc::Pexp_construct(ctor, None) => Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                ctor.clone(),
                Some(arena.push_expr(a)),
            )),
            pexp_loc: original.pexp_loc,
            pexp_attributes: original.pexp_attributes.clone(),
        },

        // a -> f(b, c) becomes f(a, b, c)
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ref partial,
                ref transformed_jsx,
            } = **inner;
            let mut new_args = Vec::with_capacity(args.len() + 1);
            new_args.push((ArgLabel::Nolabel, arena.push_expr(a)));
            new_args.extend(args.iter().map(|(lbl, e)| (lbl.clone(), *e)));

            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                    funct: *funct,
                    args: new_args,
                    partial: *partial,
                    transformed_jsx: *transformed_jsx,
                }))),
                pexp_loc: original.pexp_loc,
                // Combine attributes from original and f
                pexp_attributes: {
                    let mut attrs = original.pexp_attributes.clone();
                    attrs.extend(f.pexp_attributes.iter().cloned());
                    attrs
                },
            }
        }

        // a -> (x, y) distributes the pipe: becomes (x(a), y(a))
        // If `a` is not a simple identifier, bind it first to avoid multiple evaluation:
        //   let __tuple_internal_obj = a in (x(__tuple_internal_obj), y(__tuple_internal_obj))
        // Matches OCaml's ast_exp_apply.ml lines 100-131
        ExpressionDesc::Pexp_tuple(xs) => pipe_tuple_bound(a, xs, &f, arena),

        // Default: a -> f becomes f(a)
        _ => Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: arena.push_expr(f),
                args: vec![(ArgLabel::Nolabel, arena.push_expr(a))],
                partial: false,
                transformed_jsx: false,
            }))),
            pexp_loc: original.pexp_loc,
            pexp_attributes: original.pexp_attributes.clone(),
        },
    }
}

/// Generic expression rewriting - recurses into sub-expressions
fn rewrite_expression_generic(expr: &Expression, arena: &mut ParseArena) -> Expression {
    arena.mark_rewritten_expr_loc(expr.pexp_loc);

    let new_desc = match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue => {
            // Even for simple expressions, we need to rewrite attributes
            // to transform strings (e.g., "js" -> "*j" in @warning("-3"))
            // This matches OCaml's default_mapper which always maps attrs.
            return Expression {
                pexp_desc: expr.pexp_desc.clone(),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena).into(),
            };
        }

        ExpressionDesc::Pexp_let(inner) => {
            let (ref rec_flag, ref bindings, ref body) = **inner;
            // Check for record pattern destructuring: convert to match expression
            // OCaml's bs_builtin_ppx.ml (lines 295-319) converts:
            //   let {field1, field2} = expr in body
            // to:
            //   match expr with {field1, field2} -> body
            if *rec_flag == RecFlag::Nonrecursive && bindings.len() == 1 {
                let vb = &bindings[0];
                if has_unwrap_attr(&vb.pvb_attributes, arena) {
                    // OCaml bs_builtin_ppx: rewrite supported let? forms into a match with
                    // an early-return case and a continuation case.
                    if !matches!(
                        &*arena.get_expr(vb.pvb_expr).pexp_desc,
                        ExpressionDesc::Pexp_pack(_)
                    ) {
                        let vb_pat = arena.get_pat(vb.pvb_pat);
                        if let Some((variant, var_name)) =
                            classify_let_unwrap_pattern(vb_pat, arena)
                        {
                            let loc = arena.mk_ghost_loc(vb_pat.ppat_loc);
                            let var_name_idx = arena.intern(&var_name);
                            let var_lid = arena.push_lident_from_idx(var_name_idx);

                            let (early_ctor_name, early_ctor_payload) = match variant {
                                LetUnwrapVariant::ResultOk => ("Error", true),
                                LetUnwrapVariant::ResultError => ("Ok", true),
                                LetUnwrapVariant::OptionSome => ("None", false),
                                LetUnwrapVariant::OptionNone => ("Some", true),
                            };
                            let early_ctor_idx = arena.intern(early_ctor_name);
                            let early_ctor_lid = arena.push_lident_from_idx(early_ctor_idx);
                            let early_ctor_payload_pat = if early_ctor_payload {
                                Some(arena.push_pat(Pattern {
                                    ppat_desc: Box::new(PatternDesc::Ppat_any),
                                    ppat_loc: loc,
                                    ppat_attributes: Attributes::new(),
                                }))
                            } else {
                                None
                            };
                            let early_ctor_pat = Pattern {
                                ppat_desc: Box::new(PatternDesc::Ppat_construct(
                                    Located {
                                        txt: early_ctor_lid,
                                        loc,
                                    },
                                    early_ctor_payload_pat,
                                )),
                                ppat_loc: loc,
                                ppat_attributes: Attributes::new(),
                            };
                            let early_ctor_pat_idx = arena.push_pat(early_ctor_pat);
                            let early_case = Case {
                                pc_bar: None,
                                pc_lhs: arena.push_pat(Pattern {
                                    ppat_desc: Box::new(PatternDesc::Ppat_alias(
                                        early_ctor_pat_idx,
                                        Located {
                                            txt: var_name_idx,
                                            loc,
                                        },
                                    )),
                                    ppat_loc: arena.none_loc(),
                                    ppat_attributes: Attributes::new(),
                                }),
                                pc_guard: None,
                                pc_rhs: arena.push_expr(Expression {
                                    pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                                        txt: var_lid,
                                        loc,
                                    })),
                                    pexp_loc: loc,
                                    pexp_attributes: Attributes::new(),
                                }),
                            };
                            let cont_case = Case {
                                pc_bar: None,
                                pc_lhs: vb.pvb_pat,
                                pc_guard: None,
                                pc_rhs: *body,
                            };

                            let mut attrs = expr.pexp_attributes.clone();
                            attrs.extend(vb.pvb_attributes.iter().cloned());
                            let rewritten = Expression {
                                pexp_desc: Box::new(ExpressionDesc::Pexp_match(Box::new((
                                    vb.pvb_expr,
                                    vec![early_case, cont_case],
                                )))),
                                pexp_loc: expr.pexp_loc,
                                pexp_attributes: attrs,
                            };
                            return rewrite_expression_generic(&rewritten, arena);
                        }
                    }
                }
                let is_record_pat = match &*arena.get_pat(vb.pvb_pat).ppat_desc {
                    PatternDesc::Ppat_record(..) => true,
                    PatternDesc::Ppat_alias(inner, _) => {
                        matches!(
                            &*arena.get_pat(*inner).ppat_desc,
                            PatternDesc::Ppat_record(..)
                        )
                    }
                    _ => false,
                };
                // Don't convert if the expression is Pexp_pack (module unpacking)
                let is_pack = matches!(
                    &*arena.get_expr(vb.pvb_expr).pexp_desc,
                    ExpressionDesc::Pexp_pack(_)
                );
                if is_record_pat && !is_pack {
                    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
                    let vb_pat = arena.get_pat(vb.pvb_pat).clone();
                    let rewritten_expr = rewrite_expression(&vb_expr, arena);
                    let rewritten_pat = rewrite_pattern(&vb_pat, arena);
                    let body_expr_inner = arena.get_expr(*body).clone();
                    let rewritten_body = rewrite_expression(&body_expr_inner, arena);
                    // Merge attributes: expression attrs + binding attrs
                    let mut attrs = expr.pexp_attributes.clone();
                    attrs.extend(vb.pvb_attributes.iter().cloned());
                    let attrs = rewrite_attributes(&attrs, arena);
                    return Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_match(Box::new((
                            arena.push_expr(rewritten_expr),
                            vec![Case {
                                pc_bar: None,
                                pc_lhs: arena.push_pat(rewritten_pat),
                                pc_guard: None,
                                pc_rhs: arena.push_expr(rewritten_body),
                            }],
                        )))),
                        pexp_loc: expr.pexp_loc,
                        pexp_attributes: attrs.into(),
                    };
                }
            }

            let new_bindings = if *rec_flag == RecFlag::Recursive {
                rewrite_value_bindings_without_flattening(bindings, arena)
            } else {
                flatten_value_bindings(bindings, arena)
            };
            let body_expr = arena.get_expr(*body).clone();
            let rw_body = rewrite_expression(&body_expr, arena);
            ExpressionDesc::Pexp_let(Box::new((
                *rec_flag,
                new_bindings,
                arena.push_expr(rw_body),
            )))
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
            let (has_this_attr, filtered_attrs) = split_this_attrs(&expr.pexp_attributes, arena);
            if has_this_attr {
                return rewrite_method_callback_expression(
                    expr,
                    arg_label,
                    *lhs,
                    *rhs,
                    *is_async,
                    filtered_attrs,
                    arena,
                );
            }
            // First, recursively rewrite the complete n-ary function shape.
            let source_params = arena.nary_fun_params(inner).into_owned();
            let mut rewritten_params = Vec::with_capacity(source_params.len());
            for source in source_params {
                let rewritten_default = source.p_default.map(|e| {
                    let de = arena.get_expr(e).clone();
                    let rw = rewrite_expression(&de, arena);
                    arena.push_expr(rw)
                });
                let source_pattern = arena.get_pat(source.p_pat).clone();
                let rewritten_pattern = rewrite_pattern(&source_pattern, arena);
                rewritten_params.push(FunParam {
                    p_attrs: source.p_attrs,
                    p_lbl: source.p_lbl,
                    p_default: rewritten_default,
                    p_pat: arena.push_pat(rewritten_pattern),
                });
            }
            let rewritten_pattern_loc =
                async_lhs_loc(arena.get_pat(rewritten_params[0].p_pat), arena);
            let body = arena.nary_fun_body(inner);
            let rhs_expr = arena.get_expr(body).clone();
            let rw_rhs = rewrite_expression(&rhs_expr, arena);
            let rewritten_rhs = arena.push_expr(rw_rhs);
            let first = rewritten_params[0].clone();
            let unknown_arity = arena.nary_fun_unknown_arity(inner);
            arena.set_nary_fun_params(*arity, rewritten_params, unknown_arity);

            // Create the rewritten fun expression
            let mut rewritten_fun = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: first.p_lbl,
                    default: first.p_default,
                    lhs: first.p_pat,
                    rhs: rewritten_rhs,
                    arity: *arity,
                    is_async: *is_async,
                }))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena).into(),
            };

            // If this is an async function, wrap the innermost body with unsafe_async
            // OCaml: Ast_async.make_function_async
            if *is_async {
                // OCaml takes the location from the mapped lhs pattern.
                rewritten_fun =
                    add_promise_to_fun_body(&rewritten_fun, rewritten_pattern_loc, arena);
            }

            return rewritten_fun;
        }

        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ref partial,
                ref transformed_jsx,
            } = **inner;
            let funct_expr = arena.get_expr(*funct).clone();
            let rw_funct = rewrite_expression(&funct_expr, arena);
            ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: arena.push_expr(rw_funct),
                args: args
                    .iter()
                    .map(|(lbl, e)| {
                        let arg_expr = arena.get_expr(*e).clone();
                        let rw = rewrite_expression(&arg_expr, arena);
                        (lbl.clone(), arena.push_expr(rw))
                    })
                    .collect(),
                partial: *partial,
                transformed_jsx: *transformed_jsx,
            }))
        }

        ExpressionDesc::Pexp_match(inner) => {
            let (ref scrutinee, ref cases) = **inner;
            // Boolean match → if-then-else conversion
            // OCaml's bs_builtin_ppx.ml (lines 138-167) converts:
            //   switch b { | true => t | false => f }
            // to:
            //   if b { t } else { f }
            if cases.len() == 2 && cases[0].pc_guard.is_none() && cases[1].pc_guard.is_none() {
                let is_true = |pat: &Pattern| -> bool {
                    if let PatternDesc::Ppat_construct(lid, None) = &*pat.ppat_desc {
                        matches!(arena.get_longident(lid.txt), Longident::Lident(s) if arena.get_string(*s) == "true")
                    } else {
                        false
                    }
                };
                let is_false = |pat: &Pattern| -> bool {
                    if let PatternDesc::Ppat_construct(lid, None) = &*pat.ppat_desc {
                        matches!(arena.get_longident(lid.txt), Longident::Lident(s) if arena.get_string(*s) == "false")
                    } else {
                        false
                    }
                };
                let (t_exp, f_exp) = if is_true(arena.get_pat(cases[0].pc_lhs))
                    && is_false(arena.get_pat(cases[1].pc_lhs))
                {
                    (Some(&cases[0].pc_rhs), Some(&cases[1].pc_rhs))
                } else if is_false(arena.get_pat(cases[0].pc_lhs))
                    && is_true(arena.get_pat(cases[1].pc_lhs))
                {
                    (Some(&cases[1].pc_rhs), Some(&cases[0].pc_rhs))
                } else {
                    (None, None)
                };
                if let (Some(t_exp), Some(f_exp)) = (t_exp, f_exp) {
                    let scrutinee_expr = arena.get_expr(*scrutinee).clone();
                    let t_expr = arena.get_expr(*t_exp).clone();
                    let f_expr = arena.get_expr(*f_exp).clone();
                    let rw_scrutinee = rewrite_expression(&scrutinee_expr, arena);
                    let rw_t = rewrite_expression(&t_expr, arena);
                    let rw_f = rewrite_expression(&f_expr, arena);
                    return Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_ifthenelse(Box::new((
                            arena.push_expr(rw_scrutinee),
                            arena.push_expr(rw_t),
                            Some(arena.push_expr(rw_f)),
                        )))),
                        pexp_loc: expr.pexp_loc,
                        pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena).into(),
                    };
                }
            }

            let scrutinee_expr = arena.get_expr(*scrutinee).clone();
            let rw_scrutinee = rewrite_expression(&scrutinee_expr, arena);
            let rw_cases = rewrite_cases(cases, arena);
            ExpressionDesc::Pexp_match(Box::new((arena.push_expr(rw_scrutinee), rw_cases)))
        }

        ExpressionDesc::Pexp_try(inner) => {
            let (ref body, ref cases) = **inner;
            let body_expr = arena.get_expr(*body).clone();
            let rw_body = rewrite_expression(&body_expr, arena);
            let rw_cases = rewrite_cases(cases, arena);
            ExpressionDesc::Pexp_try(Box::new((arena.push_expr(rw_body), rw_cases)))
        }

        ExpressionDesc::Pexp_tuple(exprs) => ExpressionDesc::Pexp_tuple(Box::new(
            exprs
                .iter()
                .map(|e| {
                    let tuple_expr = arena.get_expr(*e).clone();
                    let rw = rewrite_expression(&tuple_expr, arena);
                    arena.push_expr(rw)
                })
                .collect(),
        )),

        ExpressionDesc::Pexp_construct(ctor, arg) => {
            let rw_arg = arg.map(|e| {
                let inner_e = arena.get_expr(e).clone();
                let rw = rewrite_expression(&inner_e, arena);
                arena.push_expr(rw)
            });
            ExpressionDesc::Pexp_construct(ctor.clone(), rw_arg)
        }

        ExpressionDesc::Pexp_variant(inner) => {
            let (ref label, ref arg) = **inner;
            let rw_arg = arg.map(|e| {
                let inner_e = arena.get_expr(e).clone();
                let rw = rewrite_expression(&inner_e, arena);
                arena.push_expr(rw)
            });
            ExpressionDesc::Pexp_variant(Box::new((label.clone(), rw_arg)))
        }

        ExpressionDesc::Pexp_record(inner) => {
            let (ref fields, ref spread) = **inner;
            let new_fields = fields
                .iter()
                .map(|f| current::ExpressionRecordField {
                    lid: f.lid.clone(),
                    expr: {
                        let field_expr = arena.get_expr(f.expr).clone();
                        let rw = rewrite_expression(&field_expr, arena);
                        arena.push_expr(rw)
                    },
                    opt: f.opt,
                })
                .collect();
            let rw_spread = spread.map(|e| {
                let inner_e = arena.get_expr(e).clone();
                let rw = rewrite_expression(&inner_e, arena);
                arena.push_expr(rw)
            });
            ExpressionDesc::Pexp_record(Box::new((new_fields, rw_spread)))
        }

        ExpressionDesc::Pexp_field(e, lid) => {
            let field_expr = arena.get_expr(*e).clone();
            let rw = rewrite_expression(&field_expr, arena);
            ExpressionDesc::Pexp_field(arena.push_expr(rw), lid.clone())
        }

        ExpressionDesc::Pexp_setfield(inner) => {
            let (ref e1, ref lid, ref e2) = **inner;
            let e1_expr = arena.get_expr(*e1).clone();
            let e2_expr = arena.get_expr(*e2).clone();
            let rw1 = rewrite_expression(&e1_expr, arena);
            let rw2 = rewrite_expression(&e2_expr, arena);
            ExpressionDesc::Pexp_setfield(Box::new((
                arena.push_expr(rw1),
                lid.clone(),
                arena.push_expr(rw2),
            )))
        }

        ExpressionDesc::Pexp_array(exprs) => ExpressionDesc::Pexp_array(Box::new(
            exprs
                .iter()
                .map(|e| {
                    let array_expr = arena.get_expr(*e).clone();
                    let rw = rewrite_expression(&array_expr, arena);
                    arena.push_expr(rw)
                })
                .collect(),
        )),

        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (ref cond, ref then_branch, ref else_branch) = **inner;
            let cond_expr = arena.get_expr(*cond).clone();
            let then_expr = arena.get_expr(*then_branch).clone();
            let rw_cond = rewrite_expression(&cond_expr, arena);
            let rw_then = rewrite_expression(&then_expr, arena);
            let rw_else = else_branch.map(|e| {
                let else_expr = arena.get_expr(e).clone();
                let rw = rewrite_expression(&else_expr, arena);
                arena.push_expr(rw)
            });
            ExpressionDesc::Pexp_ifthenelse(Box::new((
                arena.push_expr(rw_cond),
                arena.push_expr(rw_then),
                rw_else,
            )))
        }

        ExpressionDesc::Pexp_sequence(e1, e2) => {
            let e1_expr = arena.get_expr(*e1).clone();
            let e2_expr = arena.get_expr(*e2).clone();
            let rw1 = rewrite_expression(&e1_expr, arena);
            let rw2 = rewrite_expression(&e2_expr, arena);
            ExpressionDesc::Pexp_sequence(arena.push_expr(rw1), arena.push_expr(rw2))
        }

        ExpressionDesc::Pexp_while(cond, body) => {
            let cond_expr = arena.get_expr(*cond).clone();
            let body_expr = arena.get_expr(*body).clone();
            let rw_cond = rewrite_expression(&cond_expr, arena);
            let rw_body = rewrite_expression(&body_expr, arena);
            ExpressionDesc::Pexp_while(arena.push_expr(rw_cond), arena.push_expr(rw_body))
        }

        ExpressionDesc::Pexp_for(inner) => {
            let (ref pat, ref e1, ref e2, ref dir, ref body) = **inner;
            let e1_expr = arena.get_expr(*e1).clone();
            let e2_expr = arena.get_expr(*e2).clone();
            let body_expr = arena.get_expr(*body).clone();
            let pat_expr = arena.get_pat(*pat).clone();
            let rw_pat = rewrite_pattern(&pat_expr, arena);
            let rw1 = rewrite_expression(&e1_expr, arena);
            let rw2 = rewrite_expression(&e2_expr, arena);
            let rw_body = rewrite_expression(&body_expr, arena);
            ExpressionDesc::Pexp_for(Box::new((
                arena.push_pat(rw_pat),
                arena.push_expr(rw1),
                arena.push_expr(rw2),
                *dir,
                arena.push_expr(rw_body),
            )))
        }

        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            let (ref pat, ref iterable, ref body) = **inner;
            let iterable_expr = arena.get_expr(*iterable).clone();
            let body_expr = arena.get_expr(*body).clone();
            let pat_expr = arena.get_pat(*pat).clone();
            let rw_pat = rewrite_pattern(&pat_expr, arena);
            let rw_iterable = rewrite_expression(&iterable_expr, arena);
            let rw_body = rewrite_expression(&body_expr, arena);
            let new_inner = Box::new((
                arena.push_pat(rw_pat),
                arena.push_expr(rw_iterable),
                arena.push_expr(rw_body),
            ));
            match &*expr.pexp_desc {
                ExpressionDesc::Pexp_for_of(_) => ExpressionDesc::Pexp_for_of(new_inner),
                _ => ExpressionDesc::Pexp_for_await_of(new_inner),
            }
        }

        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref e, ref ty) = **inner;
            let e_expr = arena.get_expr(*e).clone();
            let ty_ct = arena.get_core_type(*ty).clone();
            let rw_e = rewrite_expression(&e_expr, arena);
            let rw_ty = rewrite_core_type(&ty_ct, arena);
            ExpressionDesc::Pexp_constraint(Box::new((
                arena.push_expr(rw_e),
                arena.push_core_type(rw_ty),
            )))
        }

        ExpressionDesc::Pexp_coerce(inner) => {
            let (ref e, ref ty1, ref ty2) = **inner;
            let e_expr = arena.get_expr(*e).clone();
            let ty2_ct = arena.get_core_type(*ty2).clone();
            let rw_e = rewrite_expression(&e_expr, arena);
            let rw_ty1 = ty1.as_ref().map(|t| {
                let t_ct = arena.get_core_type(*t).clone();
                let rw = rewrite_core_type(&t_ct, arena);
                arena.push_core_type(rw)
            });
            let rw_ty2 = rewrite_core_type(&ty2_ct, arena);
            ExpressionDesc::Pexp_coerce(Box::new((
                arena.push_expr(rw_e),
                rw_ty1,
                arena.push_core_type(rw_ty2),
            )))
        }

        ExpressionDesc::Pexp_send(inner) => {
            let (ref e, ref method) = **inner;
            let e_expr = arena.get_expr(*e).clone();
            let rw = rewrite_expression(&e_expr, arena);
            ExpressionDesc::Pexp_send(Box::new((arena.push_expr(rw), method.clone())))
        }

        ExpressionDesc::Pexp_assert(e) => {
            let e_expr = arena.get_expr(*e).clone();
            let rw = rewrite_expression(&e_expr, arena);
            ExpressionDesc::Pexp_assert(arena.push_expr(rw))
        }

        ExpressionDesc::Pexp_await(e) => {
            // Transform: await expr -> Primitive_promise.unsafe_await(expr)
            // OCaml's create_await_expression uses the inner expression's pexp_loc
            // (not the Pexp_await node's loc) for the ghost location
            // OCaml creates a NEW expression with empty attributes, discarding any
            // attributes on the Pexp_await node (like @res.braces)
            let e_expr = arena.get_expr(*e).clone();
            let e_loc = e_expr.pexp_loc;
            let rewritten_inner = rewrite_expression(&e_expr, arena);
            return transform_await(rewritten_inner, e_loc, arena);
        }

        ExpressionDesc::Pexp_pack(mod_expr_idx) => {
            // Module expressions - don't recurse for now
            let me = arena.get_mod_expr(*mod_expr_idx).clone();
            ExpressionDesc::Pexp_pack(arena.push_mod_expr(me))
        }

        ExpressionDesc::Pexp_letmodule(inner) => {
            let (ref name, ref mod_expr, ref body) = **inner;
            let mod_expr_val = arena.get_mod_expr(*mod_expr).clone();
            // Check for expression-level await: module M = @res.await ME
            // OCaml: bs_builtin_ppx.ml lines 327-363
            //
            // Case 1: Pmod_ident with @res.await
            //   module M = @res.await Belt.List
            //   -> module M = unpack(...) using __Belt_List__
            //
            // Case 2: Pmod_constraint(Pmod_ident, Pmty_ident mtyp_lid) with @res.await
            //   module M = @res.await (Belt.List: BeltList)
            //   -> module M = unpack(...) using BeltList

            // Check Case 1: Pmod_ident with await
            if let ModuleExprDesc::Pmod_ident(located_lid) = &*mod_expr_val.pmod_desc {
                if has_await_attribute(&mod_expr_val.pmod_attributes, arena) {
                    // Generate module type name: __Belt_List__
                    let module_type_name = local_module_type_name(located_lid.txt, arena);
                    // OCaml builds this name independently in expression mapper and
                    // structure spelunking paths, so keep a fresh string identity here.
                    let module_type_lid_idx = arena.push_lident(&module_type_name);
                    // OCaml uses me.pmod_loc for this generated lid.
                    let module_type_lid = Located {
                        txt: module_type_lid_idx,
                        loc: mod_expr_val.pmod_loc,
                    };

                    let transformed_mod_expr =
                        create_await_module_expression(&mod_expr_val, module_type_lid, arena);

                    // OCaml: {e with pexp_desc = Pexp_letmodule(Box::new((lid, transformed, self.expr self expr)))}
                    let body_expr = arena.get_expr(*body).clone();
                    let rw_body = rewrite_expression(&body_expr, arena);
                    return Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_letmodule(Box::new((
                            name.clone(),
                            arena.push_mod_expr(transformed_mod_expr),
                            arena.push_expr(rw_body),
                        )))),
                        pexp_loc: expr.pexp_loc,
                        pexp_attributes: expr.pexp_attributes.clone(),
                    };
                }
            }

            // Check Case 2: Pmod_constraint(Pmod_ident, Pmty_ident mtyp_lid) with await
            if let ModuleExprDesc::Pmod_constraint(inner_mod_idx, mty_idx) =
                &*mod_expr_val.pmod_desc
            {
                let inner_mod = arena.get_mod_expr(*inner_mod_idx).clone();
                let mty = arena.get_mod_type(*mty_idx).clone();
                if let ModuleExprDesc::Pmod_ident(_) = &*inner_mod.pmod_desc {
                    if let ModuleTypeDesc::Pmty_ident(mtyp_lid) = &*mty.pmty_desc {
                        let mtyp_lid_copy = mtyp_lid.clone();
                        let inner_has_await =
                            has_await_attribute(&inner_mod.pmod_attributes, arena);
                        let outer_has_await =
                            has_await_attribute(&mod_expr_val.pmod_attributes, arena);
                        // Check for @res.await on either the inner module or the constraint
                        if inner_has_await || outer_has_await {
                            // Use the existing module type identifier with its location
                            let transformed_mod_expr =
                                create_await_module_expression(&mod_expr_val, mtyp_lid_copy, arena);

                            let body_expr = arena.get_expr(*body).clone();
                            let rw_body = rewrite_expression(&body_expr, arena);
                            return Expression {
                                pexp_desc: Box::new(ExpressionDesc::Pexp_letmodule(Box::new((
                                    name.clone(),
                                    arena.push_mod_expr(transformed_mod_expr),
                                    arena.push_expr(rw_body),
                                )))),
                                pexp_loc: expr.pexp_loc,
                                pexp_attributes: expr.pexp_attributes.clone(),
                            };
                        }
                    }
                }
            }

            // Default: no await transformation needed, but DO recurse into module structure
            // to handle externals inside the module
            let body_expr = arena.get_expr(*body).clone();
            let rw_mod = rewrite_module_expr(&mod_expr_val, arena);
            let rw_body = rewrite_expression(&body_expr, arena);
            ExpressionDesc::Pexp_letmodule(Box::new((
                name.clone(),
                arena.push_mod_expr(rw_mod),
                arena.push_expr(rw_body),
            )))
        }

        ExpressionDesc::Pexp_letexception(inner) => {
            let (ref exn, ref body) = **inner;
            let body_expr = arena.get_expr(*body).clone();
            let rw_body = rewrite_expression(&body_expr, arena);
            ExpressionDesc::Pexp_letexception(Box::new((exn.clone(), arena.push_expr(rw_body))))
        }

        ExpressionDesc::Pexp_open(inner) => {
            let (ref override_flag, ref mod_name, ref body) = **inner;
            let body_expr = arena.get_expr(*body).clone();
            let rw_body = rewrite_expression(&body_expr, arena);
            ExpressionDesc::Pexp_open(Box::new((
                *override_flag,
                mod_name.clone(),
                arena.push_expr(rw_body),
            )))
        }

        // Pexp_newtype is an early-return case in OCaml's expr_mapper:
        // {e with pexp_desc = Pexp_newtype (s, self.expr self body)}
        // It preserves the original expression's attributes without remapping.
        ExpressionDesc::Pexp_newtype(inner) => {
            let (ref name, ref body) = **inner;
            let body_expr = arena.get_expr(*body).clone();
            let rw_body = rewrite_expression(&body_expr, arena);
            return Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_newtype(Box::new((
                    name.clone(),
                    arena.push_expr(rw_body),
                )))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            };
        }

        // Extensions - handle %raw, others just clone
        ExpressionDesc::Pexp_extension(ext) => {
            return handle_extension(expr, ext, arena);
        }

        // JSX - recurse into children and props
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            ExpressionDesc::Pexp_jsx_element(Box::new(rewrite_jsx_element(jsx, arena)))
        }
        ExpressionDesc::Pexp_inline_for(inner) => {
            let (ref pat, ref collection, ref body) = **inner;
            let coll_expr = arena.get_expr(*collection).clone();
            let body_expr = arena.get_expr(*body).clone();
            let rw_collection = rewrite_expression_generic(&coll_expr, arena);
            let rw_body = rewrite_expression_generic(&body_expr, arena);
            ExpressionDesc::Pexp_inline_for(Box::new((
                *pat,
                arena.push_expr(rw_collection),
                arena.push_expr(rw_body),
            )))
        }
        ExpressionDesc::Pexp_comptime_typeinfo(_) | ExpressionDesc::Pexp_comptime_typename(_) => {
            // Pass through as-is (no sub-expressions to rewrite)
            (*expr.pexp_desc).clone()
        }
        ExpressionDesc::Pexp_comptime_field(inner) => {
            let (ref value, ref field) = **inner;
            let val_expr = arena.get_expr(*value).clone();
            let field_expr = arena.get_expr(*field).clone();
            let rw_value = rewrite_expression_generic(&val_expr, arena);
            let rw_field = rewrite_expression_generic(&field_expr, arena);
            ExpressionDesc::Pexp_comptime_field(Box::new((
                arena.push_expr(rw_value),
                arena.push_expr(rw_field),
            )))
        }
        ExpressionDesc::Pexp_comptime_compile_error(expr_idx) => {
            let inner_expr = arena.get_expr(*expr_idx).clone();
            let rw = rewrite_expression_generic(&inner_expr, arena);
            ExpressionDesc::Pexp_comptime_compile_error(arena.push_expr(rw))
        }
        ExpressionDesc::Pexp_comptime_record(inner) => {
            let (ref ct, ref fields_expr) = **inner;
            let inner_expr = arena.get_expr(*fields_expr).clone();
            let rw = rewrite_expression_generic(&inner_expr, arena);
            ExpressionDesc::Pexp_comptime_record(Box::new((*ct, arena.push_expr(rw))))
        }
        ExpressionDesc::Pexp_comptime_variant(inner) => {
            let (ref ct, ref expr_idx, ref opt_expr_idx) = **inner;
            let inner_expr = arena.get_expr(*expr_idx).clone();
            let rw_expr = rewrite_expression_generic(&inner_expr, arena);
            let new_expr = arena.push_expr(rw_expr);
            let new_opt = opt_expr_idx.map(|e| {
                let oe = arena.get_expr(e).clone();
                let rw = rewrite_expression_generic(&oe, arena);
                arena.push_expr(rw)
            });
            ExpressionDesc::Pexp_comptime_variant(Box::new((*ct, new_expr, new_opt)))
        }
        ExpressionDesc::Pexp_comptime_build_variant(e) => {
            let ie = arena.get_expr(*e).clone();
            let rw = rewrite_expression_generic(&ie, arena);
            ExpressionDesc::Pexp_comptime_build_variant(arena.push_expr(rw))
        }
        ExpressionDesc::Pexp_comptime_variant_case(e) => {
            let ie = arena.get_expr(*e).clone();
            let rw = rewrite_expression_generic(&ie, arena);
            ExpressionDesc::Pexp_comptime_variant_case(arena.push_expr(rw))
        }
        ExpressionDesc::Pexp_comptime_build_record(e) => {
            let ie = arena.get_expr(*e).clone();
            let rw = rewrite_expression_generic(&ie, arena);
            ExpressionDesc::Pexp_comptime_build_record(arena.push_expr(rw))
        }
        ExpressionDesc::Pexp_comptime_record_field(e) => {
            let ie = arena.get_expr(*e).clone();
            let rw = rewrite_expression_generic(&ie, arena);
            ExpressionDesc::Pexp_comptime_record_field(arena.push_expr(rw))
        }
    };

    Expression {
        pexp_desc: Box::new(new_desc),
        pexp_loc: expr.pexp_loc,
        pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena).into(),
    }
}

/// Rewrite cases for match/try expressions
fn rewrite_cases(cases: &[Case], arena: &mut ParseArena) -> Vec<Case> {
    cases
        .iter()
        .map(|c| {
            let lhs_pat = arena.get_pat(c.pc_lhs).clone();
            let rw_lhs = rewrite_pattern(&lhs_pat, arena);
            let rw_guard = c.pc_guard.as_ref().map(|e| {
                let guard_expr = arena.get_expr(*e).clone();
                let rw = rewrite_expression(&guard_expr, arena);
                arena.push_expr(rw)
            });
            let rhs_expr = arena.get_expr(c.pc_rhs).clone();
            let rw_rhs = rewrite_expression(&rhs_expr, arena);
            Case {
                pc_bar: c.pc_bar,
                pc_lhs: arena.push_pat(rw_lhs),
                pc_guard: rw_guard,
                pc_rhs: arena.push_expr(rw_rhs),
            }
        })
        .collect()
}

/// Rewrite a JSX element, recursing into children and props
fn rewrite_jsx_element(jsx: &JsxElement, arena: &mut ParseArena) -> JsxElement {
    match jsx {
        JsxElement::Fragment(frag) => JsxElement::Fragment(JsxFragment {
            opening: frag.opening,
            children: rewrite_jsx_children(&frag.children, arena),
            closing: frag.closing,
        }),
        JsxElement::Unary(elem) => JsxElement::Unary(JsxUnaryElement {
            tag_name: elem.tag_name.clone(),
            props: rewrite_jsx_props(&elem.props, arena),
        }),
        JsxElement::Container(elem) => JsxElement::Container(JsxContainerElement {
            tag_name_start: elem.tag_name_start.clone(),
            opening_end: elem.opening_end,
            props: rewrite_jsx_props(&elem.props, arena),
            children: rewrite_jsx_children(&elem.children, arena),
            closing_tag: elem.closing_tag.clone(),
        }),
    }
}

/// Rewrite JSX children (list of expressions)
fn rewrite_jsx_children(children: &[ExprIdx], arena: &mut ParseArena) -> Vec<ExprIdx> {
    children
        .iter()
        .map(|e| {
            let child_expr = arena.get_expr(*e).clone();
            let rw = rewrite_expression(&child_expr, arena);
            arena.push_expr(rw)
        })
        .collect()
}

/// Rewrite JSX props
fn rewrite_jsx_props(props: &[JsxProp], arena: &mut ParseArena) -> Vec<JsxProp> {
    props
        .iter()
        .map(|prop| match prop {
            JsxProp::Punning { optional, name } => JsxProp::Punning {
                optional: *optional,
                name: name.clone(),
            },
            JsxProp::Value {
                name,
                optional,
                value,
            } => JsxProp::Value {
                name: name.clone(),
                optional: *optional,
                value: {
                    let value_expr = arena.get_expr(*value).clone();
                    let rw = rewrite_expression(&value_expr, arena);
                    arena.push_expr(rw)
                },
            },
            JsxProp::Spreading { loc, expr } => JsxProp::Spreading {
                loc: *loc,
                expr: {
                    let spread_expr = arena.get_expr(*expr).clone();
                    let rw = rewrite_expression(&spread_expr, arena);
                    arena.push_expr(rw)
                },
            },
        })
        .collect()
}

// ========== @deriving PPX Transformation ==========

/// Actions that can be derived from @deriving attribute
#[derive(Debug, Clone, PartialEq)]
enum DeriveAction {
    Accessors,
    JsConverter { new_type: bool },
    Abstract { light: bool },
}

struct DeriveActionConfig {
    name: String,
    name_loc: LocIdx,
    config: Option<ExprIdx>,
}

fn expr_lident_name(expr_idx: ExprIdx, arena: &ParseArena) -> Option<String> {
    let expr = arena.get_expr(expr_idx);
    let ExpressionDesc::Pexp_ident(lid_loc) = &*expr.pexp_desc else {
        return None;
    };
    let Longident::Lident(name_idx) = arena.get_longident(lid_loc.txt) else {
        return None;
    };
    Some(arena.get_string(*name_idx).to_string())
}

fn record_field_action_config(
    field: &ExpressionRecordField,
    arena: &ParseArena,
) -> PpxResult<DeriveActionConfig> {
    let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) else {
        return Err(PpxError::at_loc(
            field.lid.loc,
            "Qualified label is not allowed",
        ));
    };
    let name = arena.get_string(*name_idx).to_string();
    let config = if expr_lident_name(field.expr, arena).as_deref() == Some(name.as_str()) {
        None
    } else {
        Some(field.expr)
    };
    Ok(DeriveActionConfig {
        name,
        name_loc: field.lid.loc,
        config,
    })
}

fn collect_deriving_expr_actions(
    expr_idx: ExprIdx,
    arena: &ParseArena,
    actions: &mut Vec<DeriveActionConfig>,
) -> PpxResult<()> {
    let expr = arena.get_expr(expr_idx);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid_loc) => {
            let Longident::Lident(name_idx) = arena.get_longident(lid_loc.txt) else {
                return Ok(());
            };
            actions.push(DeriveActionConfig {
                name: arena.get_string(*name_idx).to_string(),
                name_loc: lid_loc.loc,
                config: None,
            });
            Ok(())
        }
        ExpressionDesc::Pexp_tuple(exprs) => {
            for expr_idx in exprs.iter() {
                collect_deriving_expr_actions(*expr_idx, arena, actions)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, _base) = &**inner;
            for field in fields {
                actions.push(record_field_action_config(field, arena)?);
            }
            Ok(())
        }
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply { funct, args, .. } = &**inner;
            let Some(name) = expr_lident_name(*funct, arena) else {
                return Ok(());
            };
            let name_loc = arena.get_expr(*funct).pexp_loc;
            actions.push(DeriveActionConfig {
                name,
                name_loc,
                config: args.first().map(|(_, expr_idx)| *expr_idx),
            });
            Ok(())
        }
        _ => Ok(()),
    }
}

fn validate_js_converter_config(expr_idx: ExprIdx, arena: &ParseArena) -> PpxResult<()> {
    let expr = arena.get_expr(expr_idx);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid_loc) => {
            let Longident::Lident(name_idx) = arena.get_longident(lid_loc.txt) else {
                return Err(PpxError::at_loc(
                    expr.pexp_loc,
                    "such configuration is not supported",
                ));
            };
            if arena.get_string(*name_idx) == "newType" {
                Ok(())
            } else {
                Err(PpxError::at_loc(
                    expr.pexp_loc,
                    "such configuration is not supported",
                ))
            }
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, _base) = &**inner;
            let Some(field) = fields.first() else {
                return Err(PpxError::at_loc(
                    expr.pexp_loc,
                    "such configuration is not supported",
                ));
            };
            if fields.len() != 1 {
                return Err(PpxError::at_loc(
                    expr.pexp_loc,
                    "such configuration is not supported",
                ));
            }
            let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) else {
                return Err(PpxError::at_loc(
                    expr.pexp_loc,
                    "such configuration is not supported",
                ));
            };
            if arena.get_string(*name_idx) != "newType" {
                return Err(PpxError::at_loc(
                    expr.pexp_loc,
                    "such configuration is not supported",
                ));
            }
            let value = arena.get_expr(field.expr);
            match &*value.pexp_desc {
                ExpressionDesc::Pexp_ident(lid_loc) => {
                    let Longident::Lident(name_idx) = arena.get_longident(lid_loc.txt) else {
                        return Err(PpxError::at_loc(
                            expr.pexp_loc,
                            "such configuration is not supported",
                        ));
                    };
                    if arena.get_string(*name_idx) == "newType" {
                        Ok(())
                    } else {
                        Err(PpxError::at_loc(
                            expr.pexp_loc,
                            "such configuration is not supported",
                        ))
                    }
                }
                ExpressionDesc::Pexp_construct(ctor_lid, None) => {
                    let Longident::Lident(name_idx) = arena.get_longident(ctor_lid.txt) else {
                        return Err(PpxError::at_loc(
                            expr.pexp_loc,
                            "such configuration is not supported",
                        ));
                    };
                    match arena.get_string(*name_idx) {
                        "true" | "false" => Ok(()),
                        _ => Err(PpxError::at_loc(
                            expr.pexp_loc,
                            "such configuration is not supported",
                        )),
                    }
                }
                _ => Err(PpxError::at_loc(
                    expr.pexp_loc,
                    "such configuration is not supported",
                )),
            }
        }
        _ => Err(PpxError::at_loc(
            expr.pexp_loc,
            "such configuration is not supported",
        )),
    }
}

fn validate_deriving_attr_payload(payload: &Payload, arena: &ParseArena) -> PpxResult<()> {
    let Some(items) = payload_str_items(payload) else {
        return Ok(());
    };
    let mut actions = Vec::new();
    for item in items {
        if let StructureItemDesc::Pstr_eval(eval_inner) = &*item.pstr_desc {
            let (expr_idx, _) = &**eval_inner;
            collect_deriving_expr_actions(*expr_idx, arena, &mut actions)?;
        }
    }

    if actions.iter().any(|action| action.name == "abstract") && actions.len() > 1 {
        if let Some(action) = actions.iter().find(|action| action.name == "abstract") {
            return Err(PpxError::at_loc(
                action.name_loc,
                "deriving abstract does not work with any other deriving",
            ));
        }
    }

    for action in actions {
        match action.name.as_str() {
            "accessors" => {
                if let Some(config) = action.config {
                    return Err(PpxError::at_loc(
                        arena.get_expr(config).pexp_loc,
                        "such configuration is not supported",
                    ));
                }
            }
            "jsConverter" => {
                if let Some(config) = action.config {
                    validate_js_converter_config(config, arena)?;
                }
            }
            "abstract" => {
                if let Some(config) = action.config {
                    if expr_lident_name(config, arena).as_deref() != Some("light") {
                        return Err(PpxError::at_loc(
                            action.name_loc,
                            "invalid config for abstract",
                        ));
                    }
                }
            }
            name => {
                return Err(PpxError::at_loc(
                    action.name_loc,
                    format!("{name} is not supported"),
                ));
            }
        }
    }

    Ok(())
}

#[derive(Clone, Copy)]
enum DerivingExpansionContext {
    StructureItem,
    SignatureItem,
}

impl DerivingExpansionContext {
    fn runs_structure_gen(self) -> bool {
        matches!(self, DerivingExpansionContext::StructureItem)
    }

    fn runs_signature_gen(self) -> bool {
        true
    }
}

fn push_deriving_not_applicable_warning(
    loc: LocIdx,
    deriving_name: &str,
    warnings: &mut Vec<PpxWarning>,
) {
    warnings.push(PpxWarning {
        loc,
        warning: Warning::BsDeriveWarning {
            message: format!("{deriving_name} not applicable to this type"),
        },
    });
}

fn push_deriving_not_applicable_warnings(
    loc: LocIdx,
    deriving_name: &str,
    warnings: &mut Vec<PpxWarning>,
    context: DerivingExpansionContext,
) {
    // OCaml Ast_derive.gen_structure_signature invokes both structure_gen and
    // signature_gen. Ast_derive.gen_signature invokes only signature_gen.
    if context.runs_structure_gen() {
        push_deriving_not_applicable_warning(loc, deriving_name, warnings);
    }
    if context.runs_signature_gen() {
        push_deriving_not_applicable_warning(loc, deriving_name, warnings);
    }
}

fn accessors_not_applicable(tdcl: &TypeDeclaration) -> bool {
    matches!(
        tdcl.ptype_kind,
        TypeKind::Ptype_abstract | TypeKind::Ptype_open
    )
}

fn js_converter_not_applicable(tdcl: &TypeDeclaration, arena: &ParseArena) -> bool {
    match tdcl.ptype_kind {
        TypeKind::Ptype_record(_) => false,
        TypeKind::Ptype_abstract => is_enum_polyvar(tdcl, arena).is_none(),
        TypeKind::Ptype_variant(_) | TypeKind::Ptype_open => true,
    }
}

fn collect_deriving_not_applicable_warnings(
    tdcls: &[TypeDeclaration],
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
    context: DerivingExpansionContext,
) {
    if validate_deriving_accessors_for_tdcls(tdcls, arena).is_err() {
        return;
    }
    let Some(last_tdcl) = tdcls.last() else {
        return;
    };
    let (actions, _remaining_attrs) = parse_deriving_actions(&last_tdcl.ptype_attributes, arena);
    for action in actions {
        match action {
            DeriveAction::Accessors => {
                for tdcl in tdcls {
                    if accessors_not_applicable(tdcl) {
                        push_deriving_not_applicable_warnings(
                            tdcl.ptype_loc,
                            "accessors",
                            warnings,
                            context,
                        );
                    }
                }
            }
            DeriveAction::JsConverter { .. } => {
                for tdcl in tdcls {
                    if js_converter_not_applicable(tdcl, arena) {
                        push_deriving_not_applicable_warnings(
                            tdcl.ptype_loc,
                            "jsConverter",
                            warnings,
                            context,
                        );
                    }
                }
            }
            DeriveAction::Abstract { .. } => {}
        }
    }
}

/// Parse @deriving attribute to extract derive actions
fn parse_deriving_actions(
    attrs: &[Attribute],
    arena: &ParseArena,
) -> (Vec<DeriveAction>, Vec<Attribute>) {
    let mut actions = vec![];
    let mut remaining_attrs = vec![];

    for attr in attrs {
        let (name_loc, payload) = attr;
        let name = arena.get_string(name_loc.txt);

        if name == "deriving" {
            // Parse the payload to extract actions
            if let Some(items) = payload_str_items(payload) {
                // @deriving(accessors) or @deriving({jsConverter: newType})
                for item in items {
                    if let StructureItemDesc::Pstr_eval(eval_inner) = &*item.pstr_desc {
                        let (ref expr, _) = **eval_inner;
                        let expr_desc = arena.get_expr(*expr).pexp_desc.clone();
                        parse_deriving_expr(&expr_desc, &mut actions, arena);
                    }
                }
            }
        } else {
            remaining_attrs.push(attr.clone());
        }
    }

    // OCaml's Ast_attributes.process_derive_type uses fold_left with attr :: acc,
    // so non-deriving attrs are reversed after @deriving is removed.
    remaining_attrs.reverse();

    (actions, remaining_attrs)
}

/// Parse a deriving expression to extract actions
fn parse_deriving_expr(
    expr_desc: &ExpressionDesc,
    actions: &mut Vec<DeriveAction>,
    arena: &ParseArena,
) {
    match expr_desc {
        // Simple identifier: @deriving(accessors)
        ExpressionDesc::Pexp_ident(lid_loc) => {
            let lid = arena.get_longident(lid_loc.txt);
            if let Longident::Lident(s) = lid {
                let name = arena.get_string(*s);
                match name {
                    "accessors" => actions.push(DeriveAction::Accessors),
                    "jsConverter" => actions.push(DeriveAction::JsConverter { new_type: false }),
                    "abstract" => actions.push(DeriveAction::Abstract { light: false }),
                    _ => {}
                }
            }
        }
        // Tuple of identifiers: @deriving(accessors, jsConverter)
        ExpressionDesc::Pexp_tuple(exprs) => {
            for expr in exprs.iter() {
                let expr_desc = arena.get_expr(*expr).pexp_desc.clone();
                parse_deriving_expr(&expr_desc, actions, arena);
            }
        }
        // Record: @deriving({jsConverter: newType})
        ExpressionDesc::Pexp_record(inner) => {
            let (ref fields, ref _none) = **inner;
            for field in fields {
                let lid = arena.get_longident(field.lid.txt);
                if let Longident::Lident(s) = lid {
                    let field_name = arena.get_string(*s);
                    match field_name {
                        "jsConverter" => {
                            // Check if value is `newType` or `{newType: true/false}`
                            let field_expr = arena.get_expr(field.expr).clone();
                            let new_type = check_new_type_config(&field_expr, arena);
                            actions.push(DeriveAction::JsConverter { new_type });
                        }
                        "abstract" => {
                            let field_expr = arena.get_expr(field.expr).clone();
                            let light = check_abstract_light_config(&field_expr, arena);
                            actions.push(DeriveAction::Abstract { light });
                        }
                        "accessors" => {
                            actions.push(DeriveAction::Accessors);
                        }
                        _ => {}
                    }
                }
            }
        }
        // Constructor application for polymorphic variants like @deriving(jsConverter)
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **inner;
            // Check if it's a simple ident being applied
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(lid_loc) = &*funct_expr.pexp_desc {
                let lid = arena.get_longident(lid_loc.txt);
                if let Longident::Lident(s) = lid {
                    let name = arena.get_string(*s);
                    if name == "jsConverter" && !args.is_empty() {
                        // @deriving(jsConverter({newType: true}))
                        let (_, arg_expr) = &args[0];
                        let cfg_expr = arena.get_expr(*arg_expr).clone();
                        let new_type = check_new_type_config(&cfg_expr, arena);
                        actions.push(DeriveAction::JsConverter { new_type });
                    }
                }
            }
        }
        _ => {}
    }
}

/// Check if abstract config is `light` in @deriving({abstract: light})
fn check_abstract_light_config(expr: &Expression, arena: &ParseArena) -> bool {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid_loc) => {
            let lid = arena.get_longident(lid_loc.txt);
            if let Longident::Lident(s) = lid {
                arena.get_string(*s) == "light"
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if an expression configures newType to true
fn check_new_type_config(expr: &Expression, arena: &ParseArena) -> bool {
    match &*expr.pexp_desc {
        // {newType: true} or just `newType`
        ExpressionDesc::Pexp_ident(lid_loc) => {
            let lid = arena.get_longident(lid_loc.txt);
            if let Longident::Lident(s) = lid {
                let name = arena.get_string(*s);
                return name == "newType";
            }
            false
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (ref fields, _) = **inner;
            for field in fields {
                let lid = arena.get_longident(field.lid.txt);
                if let Longident::Lident(s) = lid {
                    let field_name = arena.get_string(*s);
                    if field_name == "newType" {
                        // Check if value is `true`
                        if let ExpressionDesc::Pexp_construct(ctor_lid, None) =
                            &*arena.get_expr(field.expr).pexp_desc
                        {
                            let ctor = arena.get_longident(ctor_lid.txt);
                            if let Longident::Lident(s) = ctor {
                                return arena.get_string(*s) == "true";
                            }
                        }
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Set the arity of the outermost Pexp_fun
fn set_outermost_arity(expr: Expression, arity: i32, arena: &mut ParseArena) -> Expression {
    if let ExpressionDesc::Pexp_fun(inner) = *expr.pexp_desc {
        let PexpFun {
            arg_label,
            default,
            lhs,
            rhs,
            is_async,
            arity: _,
            ..
        } = *inner;
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label,
                default,
                lhs,
                rhs,
                is_async,
                arity: arena.push_arity(Some(arity)),
            }))),
            pexp_loc: expr.pexp_loc,
            pexp_attributes: expr.pexp_attributes,
        }
    } else {
        expr
    }
}

/// Generate a core type representing the type declaration
fn core_type_of_type_declaration(tdcl: &TypeDeclaration, arena: &mut ParseArena) -> CoreType {
    // OCaml: Typ.constr ~attrs {txt = Lident txt; loc} (Ext_list.map ptype_params fst)
    // - ptype_name = {txt; loc} -- so longident uses ptype_name.loc
    // - Typ.constr has optional ~loc (defaults to !default_loc = ghost)
    // - ptype_attributes = attrs -- but we don't include attrs here (see core_type_of_type_declaration_with_attrs)
    let name_loc = tdcl.ptype_name.loc; // Longident uses the type name's location
    let ptyp_loc = arena.none_loc(); // ptyp_loc defaults to ghost
    let name_lid = arena.push_longident(Longident::Lident(tdcl.ptype_name.txt));

    if tdcl.ptype_params.is_empty() {
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                Located {
                    txt: name_lid,
                    loc: name_loc,
                },
                vec![],
            )))),
            ptyp_loc,
            ptyp_attributes: Attributes::new(),
        }
    } else {
        // Type has parameters: 'a t -> t<'a>
        let type_args: Vec<CoreTypeIdx> = tdcl
            .ptype_params
            .iter()
            .map(|(core_type, _)| core_type.clone())
            .collect();
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                Located {
                    txt: name_lid,
                    loc: name_loc,
                },
                type_args,
            )))),
            ptyp_loc,
            ptyp_attributes: Attributes::new(),
        }
    }
}

/// Uncapitalize the first character of a string
fn uncapitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_lowercase().chain(chars).collect(),
    }
}

// ========== @deriving(jsConverter) Implementation ==========
// This implements the OCaml `ast_derive_js_mapper.ml` transformation.
// For polyvariant types, it generates:
// - _eraseType: %identity primitive
// - _index: @get_index primitive
// - _map: %raw JSON object mapping variant tags to string values
// - _revMap: %raw JSON object mapping string values to variant tags
// - <type>ToJs: function using _index(_map, param)
// - <type>FromJs: function using _index(_revMap, param)

/// Check if a type declaration is an enum polyvariant (all nullary tags)
fn is_enum_polyvar<'a>(tdcl: &'a TypeDeclaration, arena: &'a ParseArena) -> Option<&'a [RowField]> {
    if let Some(manifest) = &tdcl.ptype_manifest {
        if let CoreTypeDesc::Ptyp_variant(var_inner) = &*arena.get_core_type(*manifest).ptyp_desc {
            let (ref row_fields, ref closed_flag, ref labels) = **var_inner;
            if labels.is_none() && *closed_flag == current::ClosedFlag::Closed {
                // Check all tags are nullary (empty type list)
                // RowField::Rtag(name_loc, attrs, is_constant, types)
                let all_nullary = row_fields.iter().all(|rf| match rf {
                    RowField::Rtag(_name_loc, _attrs, is_constant, types) => {
                        *is_constant && types.is_empty()
                    }
                    _ => false,
                });
                if all_nullary {
                    return Some(row_fields);
                }
            }
        }
    }
    None
}

/// Get @as value from attributes (used for polyvariant tag string mapping)
fn get_as_string_value(attrs: &[Attribute], arena: &ParseArena) -> Option<String> {
    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        if name == "as" {
            if let Some(items) = payload_str_items(payload) {
                if let Some(item) = items.first() {
                    if let StructureItemDesc::Pstr_eval(eval_inner) = &*item.pstr_desc {
                        let (ref expr, _) = **eval_inner;
                        // Constant::String(txt_str, delim)
                        if let ExpressionDesc::Pexp_constant(c) = &*arena.get_expr(*expr).pexp_desc
                        {
                            if let Constant::String(txt_str, _delim) = &**c {
                                return Some(txt_str.to_string());
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

/// Build the JSON map string like `{"Red":"Red","Green":"Green","Blue":"Blue"}`
fn build_js_converter_map(row_fields: &[RowField], arena: &ParseArena) -> (String, String, bool) {
    let mut map_buf = String::from("{");
    let mut rev_map_buf = String::from("{");
    let mut has_bs_as = false;

    let entries: Vec<(String, String)> = row_fields
        .iter()
        .filter_map(|rf| {
            match rf {
                // RowField::Rtag(name_loc, attrs, is_constant, types)
                // name_loc.txt is a String (Label = String)
                RowField::Rtag(name_loc, attrs, _, _) => {
                    let tag_name = name_loc.txt.to_string();
                    let js_name = match get_as_string_value(attrs, arena) {
                        Some(name) => {
                            has_bs_as = true;
                            name
                        }
                        None => tag_name.clone(),
                    };
                    Some((tag_name, js_name))
                }
                _ => None,
            }
        })
        .collect();

    for (i, (tag_name, js_name)) in entries.iter().enumerate() {
        let last = i == entries.len() - 1;
        // map: {"Red":"Red", ...}
        map_buf.push('"');
        map_buf.push_str(tag_name);
        map_buf.push_str("\":\"");
        map_buf.push_str(js_name);
        map_buf.push('"');
        if !last {
            map_buf.push(',');
        }

        // rev_map: {"Red":"Red", ...}
        rev_map_buf.push('"');
        rev_map_buf.push_str(js_name);
        rev_map_buf.push_str("\":\"");
        rev_map_buf.push_str(tag_name);
        rev_map_buf.push('"');
        if !last {
            rev_map_buf.push(',');
        }
    }

    map_buf.push('}');
    rev_map_buf.push('}');

    (map_buf, rev_map_buf, has_bs_as)
}

/// Create the _eraseType primitive: external _eraseType: 'a => 'a = "%identity"
fn create_erase_type_str(arena: &mut ParseArena) -> StructureItem {
    let none_loc = arena.none_loc();
    let erase_type_name = arena.intern_string("_eraseType");

    // Type: 'a => 'a (Ptyp_any => Ptyp_any)
    let any_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let arrow_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(any_type.clone()),
            }),
            arena.push_core_type(any_type),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let val_desc = ValueDescription {
        pval_name: Located {
            txt: erase_type_name,
            loc: none_loc,
        },
        pval_type: arena.push_core_type(arrow_type),
        pval_prim: vec![prim_str(arena, "%identity")],
        pval_attributes: Attributes::new(),
        pval_loc: none_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(val_desc))),
        pstr_loc: none_loc,
    }
}

/// Create the _index primitive: external _index: 'a => 'b => 'c = "" (with @get_index attr)
fn create_unsafe_index_get_str(arena: &mut ParseArena) -> StructureItem {
    let none_loc = arena.none_loc();
    let index_name = arena.intern_string("_index");

    // Type: ('a, 'b) => 'c
    let any_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };
    let args = vec![
        TypeArg {
            attrs: Attributes::new(),
            lbl: ArgLabel::Nolabel,
            typ: arena.push_core_type(any_type.clone()),
        },
        TypeArg {
            attrs: Attributes::new(),
            lbl: ArgLabel::Nolabel,
            typ: arena.push_core_type(any_type.clone()),
        },
    ];
    let arrow_type = make_arrows_type(&args, &any_type, arena);

    // Encode the FFI with @get_index
    // OCaml uses Param_number when all params are (Nothing, Arg_empty)
    // The return_wrapper is Return_unset (not Return_identity) for @get_index externals
    let ffi = FfiType::FfiBs {
        params: Params::ParamNumber(2),
        return_wrapper: ReturnWrapper::ReturnUnset,
        external_spec: ExternalSpec::JsGetIndex {
            js_get_index_scopes: vec![],
        },
    };
    let encoded = encode_ffi_type(&ffi);

    let val_desc = ValueDescription {
        pval_name: Located {
            txt: index_name,
            loc: none_loc,
        },
        pval_type: arena.push_core_type(arrow_type),
        pval_prim: vec![arena.prim_empty_js_mapper(), prim_str(arena, encoded)],
        pval_attributes: Attributes::new(),
        pval_loc: none_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(val_desc))),
        pstr_loc: none_loc,
    }
}

/// Create _map or _revMap binding using %raw extension
/// let _map = %raw(`{"Red":"Red","Green":"Green"}`)
fn create_map_binding(
    var_name: &str,
    json_str: &str,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> StructureItem {
    let none_loc = arena.none_loc();
    let var_name_idx = arena.intern_string(var_name);
    let module_name_idx = arena.intern_string("J");
    let unsafe_expr_idx = arena.intern_string("unsafe_expr");

    // Create the module structure with external unsafe_expr: 'a => 'a = "#raw_expr"
    let any_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };
    let arrow_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(any_type.clone()),
            }),
            arena.push_core_type(any_type),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let unsafe_expr_prim = ValueDescription {
        pval_name: Located {
            txt: unsafe_expr_idx,
            loc,
        },
        pval_type: arena.push_core_type(arrow_type),
        pval_prim: vec![arena.prim_raw_expr()],
        pval_attributes: Attributes::new(),
        pval_loc: loc,
    };

    let module_structure = vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(
            unsafe_expr_prim,
        ))),
        pstr_loc: loc,
    }];

    let module_expr = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(module_structure))),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    // Create J.unsafe_expr(json_str) application
    let j_unsafe_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: arena.push_longident(Longident::Ldot(
                Box::new(Longident::Lident(module_name_idx)),
                unsafe_expr_idx,
            )),
            loc,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // Constant::String(txt_string, delim_option)
    let json_const = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(Constant::String(
            Cow::Owned(json_str.to_string()),
            None,
        )))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    let apply_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(j_unsafe_expr),
            args: vec![(ArgLabel::Nolabel, arena.push_expr(json_const))],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // Create let module J = struct ... end in J.unsafe_expr(json_str)
    // Pexp_letmodule(Box::new((StringLoc, ModuleExpr, ExprIdx)))
    // StringLoc is Located<StrIdx>
    let letmodule_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_letmodule(Box::new((
            Located {
                txt: module_name_idx,
                loc,
            },
            arena.push_mod_expr(module_expr),
            arena.push_expr(apply_expr),
        )))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    // Create let _map = ...
    // OCaml: Pat.var {loc; txt = map} - the variable name location is the type decl loc
    // But pattern wrapper location is ghost (Pat.var has no ~loc parameter)
    let binding = ValueBinding {
        pvb_pat: arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                txt: var_name_idx,
                loc,
            })),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        }),
        pvb_expr: arena.push_expr(letmodule_expr),
        pvb_attributes: Attributes::new(),
        pvb_loc: none_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
            RecFlag::Nonrecursive,
            vec![binding],
        )))),
        pstr_loc: none_loc,
    }
}

/// Create _revMap that references _map (when no @as attributes)
fn create_rev_map_ref_binding(loc: LocIdx, arena: &mut ParseArena) -> StructureItem {
    let none_loc = arena.none_loc();
    let rev_map_name = arena.intern_string("_revMap");
    let map_name = arena.intern_string("_map");

    let map_ref = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: arena.push_longident(Longident::Lident(map_name)),
            loc,
        })),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    let binding = ValueBinding {
        pvb_pat: arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                txt: rev_map_name,
                loc,
            })), // OCaml: {loc; txt = rev_map}
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        }),
        pvb_expr: arena.push_expr(map_ref),
        pvb_attributes: Attributes::new(),
        pvb_loc: none_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
            RecFlag::Nonrecursive,
            vec![binding],
        )))),
        pstr_loc: none_loc,
    }
}

/// Create typeToJs function: let colorToJs = (param: color) => _index(_map, param)
fn create_to_js_function(
    fn_name_idx: StrIdx,
    core_type: &CoreType,
    has_bs_as: bool,
    loc: LocIdx,
    param_name: StrIdx,
    param_lid: LidentIdx,
    map_lid: LidentIdx,
    index_lid: LidentIdx,
    erase_type_lid: LidentIdx,
    arena: &mut ParseArena,
) -> StructureItem {
    let none_loc = arena.none_loc();

    // If has_bs_as, body is: _index(_map, param)
    // Otherwise, body is: _eraseType(param)
    let body_expr = if has_bs_as {
        // _index(_map, param)
        let index_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: index_lid,
                loc: none_loc,
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        let map_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located { txt: map_lid, loc })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        let param_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: param_lid,
                loc,
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: arena.push_expr(index_ident),
                args: vec![
                    (ArgLabel::Nolabel, arena.push_expr(map_ident)),
                    (ArgLabel::Nolabel, arena.push_expr(param_ident)),
                ],
                partial: false,
                transformed_jsx: false,
            }))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        // _eraseType(param)
        let erase_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: erase_type_lid,
                loc: none_loc,
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        let param_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: param_lid,
                loc,
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: arena.push_expr(erase_ident),
                args: vec![(ArgLabel::Nolabel, arena.push_expr(param_ident))],
                partial: false,
                transformed_jsx: false,
            }))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        }
    };

    // Pattern: (param: color)
    let param_pat = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
            arena.push_pat(Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                    txt: param_name,
                    loc,
                })),
                ppat_loc: none_loc,
                ppat_attributes: Attributes::new(),
            }),
            arena.push_core_type(core_type.clone()),
        )))),
        ppat_loc: none_loc,
        ppat_attributes: Attributes::new(),
    };

    let fun_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: ArgLabel::Nolabel,
            default: None,
            lhs: arena.push_pat(param_pat),
            rhs: arena.push_expr(body_expr),
            is_async: false,
            arity: arena.static_ppx_arity_1(),
        }))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    let binding = ValueBinding {
        pvb_pat: arena.push_pat(Pattern {
            // OCaml uses tdcl.ptype_loc for function name pattern variable
            ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                txt: fn_name_idx,
                loc,
            })),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        }),
        pvb_expr: arena.push_expr(fun_expr),
        pvb_attributes: Attributes::new(),
        pvb_loc: none_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
            RecFlag::Nonrecursive,
            vec![binding],
        )))),
        pstr_loc: none_loc,
    }
}

/// Create typeFromJs function: let colorFromJs = param => _index(_revMap, param)
fn create_from_js_function(
    fn_name_idx: StrIdx,
    create_type: bool,
    loc: LocIdx,
    param_name: StrIdx,
    param_lid: LidentIdx,
    rev_map_lid: LidentIdx,
    index_lid: LidentIdx,
    arena: &mut ParseArena,
) -> StructureItem {
    let none_loc = arena.none_loc();

    // _index(_revMap, param)
    let index_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: index_lid,
            loc: none_loc,
        })),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };
    let rev_map_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: rev_map_lid,
            loc,
        })),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };
    let param_ident = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: param_lid,
            loc,
        })),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    let result_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: arena.push_expr(index_ident),
            args: vec![
                (ArgLabel::Nolabel, arena.push_expr(rev_map_ident)),
                (ArgLabel::Nolabel, arena.push_expr(param_ident)),
            ],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };
    // OCaml ast_derive_js_mapper.ml:
    // let result = _index(_revMap, param) in
    // if create_type then Primitive_util.raiseWhenNotFound result else result
    let body_expr = if create_type {
        let util_lid = arena.intern_string("Primitive_util");
        let raise_when_not_found = arena.intern_string("raiseWhenNotFound");
        let raise_when_not_found_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: arena.push_longident(Longident::Ldot(
                    Box::new(Longident::Lident(util_lid)),
                    raise_when_not_found,
                )),
                loc: none_loc,
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: arena.push_expr(raise_when_not_found_ident),
                args: vec![(ArgLabel::Nolabel, arena.push_expr(result_expr))],
                partial: false,
                transformed_jsx: false,
            }))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        result_expr
    };

    let param_pat = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
            txt: param_name,
            loc,
        })),
        ppat_loc: none_loc,
        ppat_attributes: Attributes::new(),
    };

    let fun_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: ArgLabel::Nolabel,
            default: None,
            lhs: arena.push_pat(param_pat),
            rhs: arena.push_expr(body_expr),
            is_async: false,
            arity: arena.static_ppx_arity_1(),
        }))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    let binding = ValueBinding {
        pvb_pat: arena.push_pat(Pattern {
            // OCaml uses tdcl.ptype_loc for function name pattern variable
            ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                txt: fn_name_idx,
                loc,
            })),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        }),
        pvb_expr: arena.push_expr(fun_expr),
        pvb_attributes: Attributes::new(),
        pvb_loc: none_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
            RecFlag::Nonrecursive,
            vec![binding],
        )))),
        pstr_loc: none_loc,
    }
}

/// Create toJs signature: val colorToJs: color => <ret_type>
fn create_to_js_sig(
    fn_name_idx: StrIdx,
    core_type: &CoreType,
    ret_type: CoreType,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> SignatureItem {
    let none_loc = arena.none_loc();

    let arrow_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(core_type.clone()),
            }),
            arena.push_core_type(ret_type),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let val_desc = ValueDescription {
        pval_name: Located {
            txt: fn_name_idx,
            loc,
        },
        pval_type: arena.push_core_type(arrow_type),
        pval_prim: vec![],
        pval_attributes: Attributes::new(),
        pval_loc: none_loc,
    };

    SignatureItem {
        psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(val_desc))),
        psig_loc: none_loc,
    }
}

/// Create fromJs signature: val colorFromJs: <arg_type> => <ret_type>
fn create_from_js_sig(
    fn_name_idx: StrIdx,
    arg_type: CoreType,
    ret_type: CoreType,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> SignatureItem {
    let none_loc = arena.none_loc();

    let arrow_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(arg_type),
            }),
            arena.push_core_type(ret_type),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let val_desc = ValueDescription {
        pval_name: Located {
            txt: fn_name_idx,
            loc,
        },
        pval_type: arena.push_core_type(arrow_type),
        pval_prim: vec![],
        pval_attributes: Attributes::new(),
        pval_loc: none_loc,
    };

    SignatureItem {
        psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(val_desc))),
        psig_loc: none_loc,
    }
}

/// Generate jsConverter structure/signature for polyvariant types
fn generate_js_converter_polyvar(
    tdcl: &TypeDeclaration,
    row_fields: &[RowField],
    create_type: bool,
    inner_loc: LocIdx,
    arena: &mut ParseArena,
) -> (Vec<StructureItem>, Vec<SignatureItem>) {
    // Clone type_name to avoid borrow issues
    let type_name = arena.get_string(tdcl.ptype_name.txt).to_string();
    let (map_json, rev_map_json, has_bs_as) = build_js_converter_map(row_fields, arena);

    // OCaml builds fresh `core_type` values independently in structure_gen and
    // signature_gen. Recreate that split so marshal sharing matches pointer identity.
    let core_type_structure = core_type_of_type_declaration_with_attrs(tdcl, arena);
    let core_type_signature = core_type_of_type_declaration_with_attrs(tdcl, arena);

    // Shared structure-level identifiers (OCaml reuses these bindings across generated
    // toJs/fromJs expressions inside one type declaration).
    let to_js_name_structure = arena.push_string(format!("{}ToJs", type_name));
    let from_js_name_structure = arena.push_string(format!("{}FromJs", type_name));
    let param_name = arena.push_string("param".to_string());
    let param_lid = arena.push_lident_from_idx(param_name);
    let map_name = arena.intern_string("_map");
    let rev_map_name = arena.intern_string("_revMap");
    let index_name = arena.intern_string("_index");
    let erase_type_name = arena.intern_string("_eraseType");
    let map_lid = arena.push_longident(Longident::Lident(map_name));
    let rev_map_lid = arena.push_longident(Longident::Lident(rev_map_name));
    let index_lid = arena.push_longident(Longident::Lident(index_name));
    let erase_type_lid = arena.push_longident(Longident::Lident(erase_type_name));

    // Build structure items
    let mut structure_items = vec![];

    // _eraseType
    structure_items.push(create_erase_type_str(arena));

    // _index
    structure_items.push(create_unsafe_index_get_str(arena));

    // _map
    structure_items.push(create_map_binding("_map", &map_json, inner_loc, arena));

    // _revMap (either same as _map or new %raw)
    if has_bs_as {
        structure_items.push(create_map_binding(
            "_revMap",
            &rev_map_json,
            inner_loc,
            arena,
        ));
    } else {
        structure_items.push(create_rev_map_ref_binding(inner_loc, arena));
    }

    // colorToJs
    structure_items.push(create_to_js_function(
        to_js_name_structure,
        &core_type_structure,
        has_bs_as,
        inner_loc,
        param_name,
        param_lid,
        map_lid,
        index_lid,
        erase_type_lid,
        arena,
    ));

    // colorFromJs
    structure_items.push(create_from_js_function(
        from_js_name_structure,
        create_type,
        inner_loc,
        param_name,
        param_lid,
        rev_map_lid,
        index_lid,
        arena,
    ));

    // If create_type is true, prepend the new abstract type
    if create_type {
        let new_type_str = create_new_type_declaration(tdcl, &type_name, arena);
        structure_items.insert(0, new_type_str);
    }

    // Build signature items
    let mut signature_items = vec![];
    let to_js_name_signature = arena.push_string(format!("{}ToJs", type_name));
    let from_js_name_signature = arena.push_string(format!("{}FromJs", type_name));
    let none_loc = arena.none_loc();
    let string_name = arena.push_string("string".to_string());
    let string_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: arena.push_longident(Longident::Lident(string_name)),
                loc: none_loc,
            },
            vec![],
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };
    let new_type_ref = create_new_type_ref(tdcl, &type_name, arena);
    let to_js_ret_type = if create_type {
        new_type_ref.clone()
    } else {
        string_type.clone()
    };
    let from_js_arg_type = if create_type {
        new_type_ref
    } else {
        string_type
    };
    let from_js_ret_type = if create_type {
        core_type_signature.clone()
    } else {
        let core_type_sig_idx = arena.push_core_type(core_type_signature.clone());
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                Located {
                    txt: arena.predef_option_lident(),
                    loc: none_loc,
                },
                vec![core_type_sig_idx],
            )))),
            ptyp_loc: none_loc,
            ptyp_attributes: Attributes::new(),
        }
    };

    if create_type {
        signature_items.push(create_new_type_sig_declaration(tdcl, &type_name, arena));
    }
    signature_items.push(create_to_js_sig(
        to_js_name_signature,
        &core_type_signature,
        to_js_ret_type,
        inner_loc,
        arena,
    ));
    signature_items.push(create_from_js_sig(
        from_js_name_signature,
        from_js_arg_type,
        from_js_ret_type,
        inner_loc,
        arena,
    ));

    (structure_items, signature_items)
}

/// Generate jsConverter structure/signature for record types
fn generate_js_converter_record(
    tdcl: &TypeDeclaration,
    labels: &[LabelDeclaration],
    create_type: bool,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> (Vec<StructureItem>, Vec<SignatureItem>) {
    let type_name = arena.get_string(tdcl.ptype_name.txt).to_string();
    let core_type = core_type_of_type_declaration_with_attrs(tdcl, arena);
    let none_loc = arena.none_loc();

    // For records, we generate:
    // - _eraseType (if create_type)
    // - abs_<name> type (if create_type)
    // - <name>ToJs: converts record to JS object using %obj extension
    // - <name>FromJs: converts JS object back to record

    let mut structure_items = vec![];
    let mut signature_items = vec![];

    if create_type {
        // _eraseType
        structure_items.push(create_erase_type_str(arena));

        // Abstract type: type abs_<name><params> = abstract
        structure_items.push(create_new_type_declaration(tdcl, &type_name, arena));
    }

    // <name>ToJs function
    let to_js_fn = create_record_to_js_function(tdcl, labels, &core_type, create_type, loc, arena);
    structure_items.push(to_js_fn);

    // <name>FromJs function
    let from_js_fn =
        create_record_from_js_function(tdcl, labels, &core_type, create_type, loc, arena);
    structure_items.push(from_js_fn);

    // Signature items
    signature_items.push(create_record_to_js_sig(
        tdcl,
        &type_name,
        labels,
        &core_type,
        create_type,
        loc,
        arena,
    ));
    signature_items.push(create_record_from_js_sig(
        tdcl,
        &type_name,
        labels,
        &core_type,
        create_type,
        loc,
        arena,
    ));

    // If create_type, prepend the new type to signature as well
    if create_type {
        let sig_new_type = create_new_type_sig_declaration(tdcl, &type_name, arena);
        signature_items.insert(0, sig_new_type);
    }

    (structure_items, signature_items)
}

/// Create a new abstract type declaration for jsConverter newType
/// type abs_<name><params>
fn create_new_type_declaration(
    tdcl: &TypeDeclaration,
    type_name: &str,
    arena: &mut ParseArena,
) -> StructureItem {
    let none_loc = arena.none_loc();
    let new_name = format!("abs_{}", type_name);
    let new_name_idx = arena.intern_string(&new_name);

    // Create new type declaration matching OCaml's new_type_of_type_declaration
    let new_tdcl = TypeDeclaration {
        ptype_name: Located {
            txt: new_name_idx,
            loc: tdcl.ptype_name.loc,
        },
        ptype_params: tdcl.ptype_params.clone(),
        ptype_cstrs: vec![],
        ptype_kind: TypeKind::Ptype_abstract,
        ptype_private: PrivateFlag::Public,
        ptype_manifest: None,
        ptype_attributes: Attributes::new(),
        ptype_loc: tdcl.ptype_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_type(Box::new((
            RecFlag::Nonrecursive,
            vec![new_tdcl],
        )))),
        pstr_loc: none_loc,
    }
}

/// Create a new abstract type signature declaration for jsConverter newType
fn create_new_type_sig_declaration(
    tdcl: &TypeDeclaration,
    type_name: &str,
    arena: &mut ParseArena,
) -> SignatureItem {
    let none_loc = arena.none_loc();
    let new_name = format!("abs_{}", type_name);
    let new_name_idx = arena.intern_string(&new_name);

    let new_tdcl = TypeDeclaration {
        ptype_name: Located {
            txt: new_name_idx,
            loc: tdcl.ptype_name.loc,
        },
        ptype_params: tdcl.ptype_params.clone(),
        ptype_cstrs: vec![],
        ptype_kind: TypeKind::Ptype_abstract,
        ptype_private: PrivateFlag::Public,
        ptype_manifest: None,
        ptype_attributes: Attributes::new(),
        ptype_loc: tdcl.ptype_loc,
    };

    SignatureItem {
        psig_desc: Box::new(SignatureItemDesc::Psig_type(Box::new((
            RecFlag::Nonrecursive,
            vec![new_tdcl],
        )))),
        psig_loc: none_loc,
    }
}

/// Create the <name>ToJs function for records
/// let sourceToJs = (param: source[@deriving...]) => %obj({...})
fn create_record_to_js_function(
    tdcl: &TypeDeclaration,
    labels: &[LabelDeclaration],
    core_type: &CoreType,
    create_type: bool,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> StructureItem {
    let none_loc = arena.none_loc();
    let type_name = arena.get_string(tdcl.ptype_name.txt).to_string();
    let to_js_name = format!("{}ToJs", type_name);
    let to_js_name_idx = arena.intern_string(&to_js_name);
    let param_str = arena.intern_string("param");

    // Pattern: (param: <core_type>)
    let param_pat = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
            arena.push_pat(Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                    txt: param_str,
                    loc,
                })),
                ppat_loc: none_loc,
                ppat_attributes: Attributes::new(),
            }),
            arena.push_core_type(core_type.clone()),
        )))),
        ppat_loc: none_loc,
        ppat_attributes: Attributes::new(),
    };

    // Build record expression for %obj extension: { field: param.field, ... }
    // OCaml: label uses pld_name.loc, param ident uses tdcl.ptype_loc, expressions use default_loc (ghost)
    let type_loc = loc; // loc is already tdcl.ptype_loc from the caller
    let record_fields: Vec<ExpressionRecordField> = labels
        .iter()
        .map(|label| {
            let field_name = label.pld_name.txt;
            let field_loc = label.pld_name.loc; // OCaml: {pld_name = {loc; txt}}
            let lid = Located {
                txt: arena.push_longident(Longident::Lident(field_name)),
                loc: field_loc, // OCaml: {Asttypes.loc; txt = Lident txt} where loc = pld_name.loc
            };

            // param.field (Pexp_field uses field_loc for the label, none_loc for expressions)
            let param_lid = arena.push_lident_from_idx(param_str);
            let param_ident = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                    txt: param_lid,
                    loc: type_loc,
                })),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };
            let param_idx = arena.push_expr(param_ident);
            let field_access = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_field(param_idx, lid.clone())),
                pexp_loc: none_loc, // Exp.field uses !default_loc (ghost)
                pexp_attributes: Attributes::new(),
            };

            ExpressionRecordField {
                lid,
                expr: arena.push_expr(field_access),
                opt: false,
            }
        })
        .collect();

    let record_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((record_fields, None)))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    // Transform %obj extension using handle_obj
    // This creates a Pexp_letmodule with the proper FFI structure
    let obj_ext_name = Located {
        txt: arena.intern_string("obj"),
        loc,
    };
    let obj_payload = Payload::PStr(Box::new(vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((
            arena.push_expr(record_expr.clone()),
            Attributes::new(),
        ))))
        .into(),
        pstr_loc: none_loc,
    }]));

    // Create a dummy expression with the extension
    let dummy_ext_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_extension(Box::new((
            obj_ext_name.clone(),
            obj_payload.clone(),
        )))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    // Transform via handle_obj to get the Pexp_letmodule structure
    let obj_extension = handle_obj(&dummy_ext_expr, &obj_payload, arena);

    // If create_type, wrap with constraint and erase_type
    let body = if create_type {
        // Create new type reference: abs_<name><params>
        let new_type = create_new_type_ref(tdcl, &type_name, arena);

        // erase_type(obj_extension) :> new_type
        let erase_type_ident = arena.intern_string("_eraseType");
        let erase_lid = arena.push_longident(Longident::Lident(erase_type_ident));
        let erase_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: erase_lid,
                loc: none_loc,
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        let erase_funct_idx = arena.push_expr(erase_ident);
        let erase_app = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: erase_funct_idx,
                args: vec![(ArgLabel::Nolabel, arena.push_expr(obj_extension))],
                partial: false,
                transformed_jsx: false,
            }))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };

        // Constraint to new type
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                arena.push_expr(erase_app),
                arena.push_core_type(new_type),
            )))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        obj_extension
    };

    // Function: fun param => body
    let fun_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: ArgLabel::Nolabel,
            default: None,
            lhs: arena.push_pat(param_pat),
            rhs: arena.push_expr(body),
            is_async: false,
            arity: arena.static_ppx_arity_1(),
        }))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    // Value binding: let <name>ToJs = fun param => body
    let binding = ValueBinding {
        pvb_pat: arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                txt: to_js_name_idx,
                loc,
            })),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        }),
        pvb_expr: arena.push_expr(fun_expr),
        pvb_attributes: Attributes::new(),
        pvb_loc: none_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
            RecFlag::Nonrecursive,
            vec![binding],
        )))),
        pstr_loc: none_loc,
    }
}

/// Create the <name>FromJs function for records
fn create_record_from_js_function(
    tdcl: &TypeDeclaration,
    labels: &[LabelDeclaration],
    core_type: &CoreType,
    create_type: bool,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> StructureItem {
    let none_loc = arena.none_loc();
    let type_name = arena.get_string(tdcl.ptype_name.txt).to_string();
    let from_js_name = format!("{}FromJs", type_name);
    let from_js_name_idx = arena.intern_string(&from_js_name);
    let param_str = arena.intern_string("param");

    // Pattern: param (no constraint for fromJs)
    let param_pat = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
            txt: param_str,
            loc,
        })),
        ppat_loc: none_loc,
        ppat_attributes: Attributes::new(),
    };

    // Build record expression: { field: ##param.field, ... }
    // OCaml: label uses pld_name.loc, param ident uses tdcl.ptype_loc, expressions use default_loc (ghost)
    let type_loc = loc; // loc is already tdcl.ptype_loc from the caller
    let record_fields: Vec<ExpressionRecordField> = labels
        .iter()
        .map(|label| {
            let field_name = label.pld_name.txt;
            let field_loc = label.pld_name.loc; // OCaml: {pld_name = {loc; txt}}
            let lid = Located {
                txt: arena.push_longident(Longident::Lident(field_name)),
                loc: field_loc, // OCaml: {Asttypes.loc; txt = Lident txt} where loc = pld_name.loc
            };

            // ##param.field (Pexp_send) - js_field function
            // OCaml: js_field uses o.pexp_loc for ## ident, and label loc comes from the label parameter
            let field_name_str = arena.get_string(field_name).to_string();
            let param_lid2 = arena.push_lident_from_idx(param_str);
            let param_ident2 = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                    txt: param_lid2,
                    loc: type_loc,
                })),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };
            let param_idx2 = arena.push_expr(param_ident2);
            let js_field = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_send(Box::new((
                    param_idx2,
                    Located {
                        txt: Cow::Owned(field_name_str),
                        loc: none_loc,
                    }, // Exp.ident m uses !default_loc
                )))),
                pexp_loc: none_loc, // js_field result uses !default_loc (ghost)
                pexp_attributes: Attributes::new(),
            };

            ExpressionRecordField {
                lid,
                expr: arena.push_expr(js_field),
                opt: false,
            }
        })
        .collect();

    let record_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((record_fields, None)))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    // Constrain to core_type
    let constrained_record = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
            arena.push_expr(record_expr),
            arena.push_core_type(core_type.clone()),
        )))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    // If create_type, wrap param with let binding
    let body = if create_type {
        let new_type = create_new_type_ref(tdcl, &type_name, arena);
        let erase_type_ident = arena.intern_string("_eraseType");

        // erase_type (param :> new_type)
        let cp_lid = arena.push_lident_from_idx(param_str);
        let cp_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located { txt: cp_lid, loc })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        let cp_idx = arena.push_expr(cp_ident);
        let constrained_param = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                cp_idx,
                arena.push_core_type(new_type),
            )))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };

        let erase_lid2 = arena.push_longident(Longident::Lident(erase_type_ident));
        let erase_ident2 = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: erase_lid2,
                loc: none_loc,
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        let erase_funct_idx2 = arena.push_expr(erase_ident2);
        let erase_app = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                funct: erase_funct_idx2,
                args: vec![(ArgLabel::Nolabel, arena.push_expr(constrained_param))],
                partial: false,
                transformed_jsx: false,
            }))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };

        // let param = erase_type(...) in constrained_record
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                RecFlag::Nonrecursive,
                vec![ValueBinding {
                    pvb_pat: arena.push_pat(Pattern {
                        ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                            txt: param_str,
                            loc,
                        })),
                        ppat_loc: none_loc,
                        ppat_attributes: Attributes::new(),
                    }),
                    pvb_expr: arena.push_expr(erase_app),
                    pvb_attributes: Attributes::new(),
                    pvb_loc: none_loc,
                }],
                arena.push_expr(constrained_record),
            )))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        constrained_record
    };

    // Function: fun param => body
    let fun_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: ArgLabel::Nolabel,
            default: None,
            lhs: arena.push_pat(param_pat),
            rhs: arena.push_expr(body),
            is_async: false,
            arity: arena.static_ppx_arity_1(),
        }))),
        pexp_loc: none_loc,
        pexp_attributes: Attributes::new(),
    };

    // Value binding
    let binding = ValueBinding {
        pvb_pat: arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                txt: from_js_name_idx,
                loc,
            })),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        }),
        pvb_expr: arena.push_expr(fun_expr),
        pvb_attributes: Attributes::new(),
        pvb_loc: none_loc,
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
            RecFlag::Nonrecursive,
            vec![binding],
        )))),
        pstr_loc: none_loc,
    }
}

/// Create a core type reference for the new abstract type: abs_<name><params>
fn create_new_type_ref(
    tdcl: &TypeDeclaration,
    type_name: &str,
    arena: &mut ParseArena,
) -> CoreType {
    let none_loc = arena.none_loc();
    let new_name = format!("abs_{}", type_name);
    let new_name_idx = arena.intern_string(&new_name);

    // Create type arguments from params
    let type_args: Vec<CoreTypeIdx> = tdcl.ptype_params.iter().map(|(ct, _)| ct.clone()).collect();

    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: arena.push_longident(Longident::Lident(new_name_idx)),
                loc: tdcl.ptype_name.loc,
            },
            type_args,
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Create signature for record toJs function
fn create_record_to_js_sig(
    tdcl: &TypeDeclaration,
    type_name: &str,
    labels: &[LabelDeclaration],
    core_type: &CoreType,
    create_type: bool,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> SignatureItem {
    let none_loc = arena.none_loc();
    let to_js_name = format!("{}ToJs", type_name);
    let fn_name_idx = arena.intern_string(&to_js_name);

    // Return type: abs_<name> if create_type, else object type
    let ret_type = if create_type {
        // Use the new abstract type: abs_<name><params>
        create_new_type_ref(tdcl, type_name, arena)
    } else {
        // Object type from labels
        let fields: Vec<ObjectField> = labels
            .iter()
            .map(|label| {
                ObjectField::Otag(
                    label.pld_name.clone(),
                    Attributes::new(),
                    label.pld_type.clone(),
                )
            })
            .collect();
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_object(Box::new((
                fields,
                current::ClosedFlag::Closed,
            )))),
            ptyp_loc: none_loc,
            ptyp_attributes: Attributes::new(),
        }
    };

    let arrow_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(core_type.clone()),
            }),
            arena.push_core_type(ret_type),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let val_desc = ValueDescription {
        pval_name: Located {
            txt: fn_name_idx,
            loc,
        }, // OCaml: pat_to_js uses tdcl.ptype_loc
        pval_type: arena.push_core_type(arrow_type),
        pval_prim: vec![],
        pval_attributes: Attributes::new(),
        pval_loc: none_loc,
    };

    SignatureItem {
        psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(val_desc))),
        psig_loc: none_loc,
    }
}

/// Create signature for record fromJs function
fn create_record_from_js_sig(
    tdcl: &TypeDeclaration,
    type_name: &str,
    labels: &[LabelDeclaration],
    core_type: &CoreType,
    create_type: bool,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> SignatureItem {
    let none_loc = arena.none_loc();
    let from_js_name = format!("{}FromJs", type_name);
    let fn_name_idx = arena.intern_string(&from_js_name);

    // Arg type: abs_<name> if create_type, else open object type
    let arg_type = if create_type {
        // Use the new abstract type: abs_<name><params>
        create_new_type_ref(tdcl, type_name, arena)
    } else {
        let fields: Vec<ObjectField> = labels
            .iter()
            .map(|label| {
                ObjectField::Otag(
                    label.pld_name.clone(),
                    Attributes::new(),
                    label.pld_type.clone(),
                )
            })
            .collect();
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_object(Box::new((
                fields,
                current::ClosedFlag::Open,
            )))),
            ptyp_loc: none_loc,
            ptyp_attributes: Attributes::new(),
        }
    };

    let arrow_type = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(arg_type),
            }),
            arena.push_core_type(core_type.clone()),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let val_desc = ValueDescription {
        pval_name: Located {
            txt: fn_name_idx,
            loc,
        }, // OCaml: pat_from_js uses tdcl.ptype_loc
        pval_type: arena.push_core_type(arrow_type),
        pval_prim: vec![],
        pval_attributes: Attributes::new(),
        pval_loc: none_loc,
    };

    SignatureItem {
        psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(val_desc))),
        psig_loc: none_loc,
    }
}

/// Build `include (struct ... end : sig ... end)` with the provided loc.
fn build_structure_signature_include(
    structure_items: Vec<StructureItem>,
    signature_items: Vec<SignatureItem>,
    outer_loc: LocIdx,
    arena: &mut ParseArena,
) -> StructureItem {
    let inner_mod = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(structure_items))),
        pmod_loc: outer_loc,
        pmod_attributes: Attributes::new(),
    };

    let sig_mod_type = ModuleType {
        pmty_desc: Box::new(ModuleTypeDesc::Pmty_signature(Box::new(signature_items))),
        pmty_loc: outer_loc,
        pmty_attributes: Attributes::new(),
    };

    let constrained_mod = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_constraint(
            arena.push_mod_expr(inner_mod),
            arena.push_mod_type(sig_mod_type),
        )),
        pmod_loc: outer_loc,
        pmod_attributes: Attributes::new(),
    };

    let include_decl = IncludeDeclaration {
        pincl_mod: arena.push_mod_expr(constrained_mod),
        pincl_loc: outer_loc,
        pincl_attributes: Attributes::new(),
    };

    StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_include(Box::new(include_decl))),
        pstr_loc: outer_loc,
    }
}

/// Generate jsConverter include for a type declaration group.
///
/// OCaml `Ast_derive.gen_structure_signature` builds exactly one include per deriving action
/// over the full `tdcls` list (not one include per type declaration).
/// Keep that grouping so typedtree module-constraint shapes match.
fn generate_js_converter_include(
    tdcls: &[TypeDeclaration],
    create_type: bool,
    pstr_loc: LocIdx,
    arena: &mut ParseArena,
) -> StructureItem {
    // OCaml uses:
    // - pstr_loc (from gen_structure_signature ~loc) for the outer include wrapper
    // - each tdcl.ptype_loc for inner generated code (bindings, functions)
    let outer_loc = pstr_loc;
    let mut structure_items: Vec<StructureItem> = vec![];
    let mut signature_items: Vec<SignatureItem> = vec![];

    for tdcl in tdcls {
        let inner_loc = tdcl.ptype_loc;
        let (mut tdcl_structure_items, mut tdcl_signature_items) = match &tdcl.ptype_kind {
            // Record types: generate toJs/fromJs with object conversion
            TypeKind::Ptype_record(label_declarations) => generate_js_converter_record(
                tdcl,
                label_declarations,
                create_type,
                inner_loc,
                arena,
            ),
            // Abstract types: check if it's an enum polyvariant
            TypeKind::Ptype_abstract => {
                if let Some(row_fields) = is_enum_polyvar(tdcl, arena).map(|rf| rf.to_vec()) {
                    generate_js_converter_polyvar(tdcl, &row_fields, create_type, inner_loc, arena)
                } else {
                    // Abstract without polyvariant manifest: empty
                    (vec![], vec![])
                }
            }
            // Variant and open types: not applicable, generate empty
            TypeKind::Ptype_variant(_) | TypeKind::Ptype_open => (vec![], vec![]),
        };
        structure_items.append(&mut tdcl_structure_items);
        signature_items.append(&mut tdcl_signature_items);
    }

    build_structure_signature_include(structure_items, signature_items, outer_loc, arena)
}

/// Handle @deriving for type declarations
///
/// OCaml transforms `@deriving(accessors) type t = { x: int }` into:
/// ```rescript
/// include (struct
///   type t = { x: int }   // @deriving stripped
///   include (struct
///     let x = (param: t[@deriving(accessors)]) => param.x
///   end : sig
///     val x: t[@deriving(accessors)] -> int
///   end)
/// end)
/// ```
fn handle_deriving_type(
    item: &StructureItem,
    rec_flag: RecFlag,
    tdcls: &[TypeDeclaration],
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    if tdcls.is_empty() {
        return vec![item.clone()];
    }

    // Get the last type declaration's attributes (where @deriving should be)
    let last_tdcl = tdcls.last().unwrap();
    let (actions, new_attrs) = parse_deriving_actions(&last_tdcl.ptype_attributes, arena);

    if actions.is_empty() {
        // No @deriving, but still rewrite type declarations for string transformations in attributes
        let rewritten_tdcls: Vec<TypeDeclaration> = tdcls
            .iter()
            .map(|tdcl| rewrite_type_declaration(tdcl, arena))
            .collect();
        return vec![StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_type(Box::new((
                rec_flag,
                rewritten_tdcls,
            )))),
            pstr_loc: item.pstr_loc,
        }];
    }

    let loc = item.pstr_loc;

    // Check if this is @deriving(abstract) - it requires completely different handling
    let abstract_action = actions.iter().find_map(|a| {
        if let DeriveAction::Abstract { light } = a {
            Some(*light)
        } else {
            None
        }
    });

    // Step 1: Create type declaration with @deriving stripped from last tdcl
    // Also rewrite all type declarations for string transformations in attributes
    let new_tdcls: Vec<TypeDeclaration> = tdcls
        .iter()
        .enumerate()
        .map(|(i, tdcl)| {
            let mut rewritten = rewrite_type_declaration(tdcl, arena);
            if i == tdcls.len() - 1 {
                // Last type declaration: replace ptype_attributes with new_attrs (without @deriving)
                rewritten.ptype_attributes = rewrite_attributes(&new_attrs, arena).into();
            }
            rewritten
        })
        .collect();

    if let Some(light) = abstract_action {
        // @deriving(abstract) has special structure:
        // include (struct
        //   include (struct <type_decl> end : sig end)
        //   type t  -- abstract
        //   external t: ... -- maker
        //   external fieldGet: ... -- getters
        //   ...
        // end)
        return handle_deriving_abstract(&new_tdcls, rec_flag, &new_tdcls, light, loc, arena);
    }

    let type_str_item = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_type(Box::new((
            rec_flag, new_tdcls,
        )))),
        pstr_loc: loc,
    };

    // Step 2: Generate accessor includes for each action
    let mut include_items: Vec<StructureItem> = vec![];

    for action in &actions {
        match action {
            DeriveAction::Accessors => {
                // OCaml emits one include per action across the full tdcls group.
                include_items.push(generate_accessor_include(tdcls, loc, arena));
            }
            DeriveAction::JsConverter { new_type } => {
                // OCaml emits one include per action across the full tdcls group.
                include_items.push(generate_js_converter_include(tdcls, *new_type, loc, arena));
            }
            DeriveAction::Abstract { light: _ } => {
                // Handled above
            }
        }
    }

    // Step 3: Wrap everything in `include (struct <type_decl> <includes> end)`
    let mut inner_structure = vec![type_str_item];
    inner_structure.extend(include_items);

    let mod_expr = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(inner_structure))),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    let include_decl = current::IncludeDeclaration {
        pincl_mod: arena.push_mod_expr(mod_expr),
        pincl_loc: loc,
        pincl_attributes: Attributes::new(),
    };

    vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_include(Box::new(include_decl))),
        pstr_loc: loc,
    }]
}

fn validate_deriving_accessors_for_tdcls(
    tdcls: &[TypeDeclaration],
    arena: &ParseArena,
) -> PpxResult<()> {
    let Some(last_tdcl) = tdcls.last() else {
        return Ok(());
    };
    for tdcl in tdcls {
        let mut seen_deriving = false;
        for (attr_name, payload) in &tdcl.ptype_attributes {
            if arena.get_string(attr_name.txt) == "deriving" {
                if seen_deriving {
                    return Err(PpxError::at_loc(
                        attr_name.loc,
                        "duplicate @deriving attribute",
                    ));
                }
                seen_deriving = true;
                validate_deriving_attr_payload(payload, arena)?;
            }
        }
    }

    let (actions, _remaining_attrs) = parse_deriving_actions(&last_tdcl.ptype_attributes, arena);
    if !actions
        .iter()
        .any(|action| matches!(action, DeriveAction::Accessors))
    {
        return Ok(());
    }

    for tdcl in tdcls {
        if let TypeKind::Ptype_variant(constructors) = &tdcl.ptype_kind {
            for constructor in constructors {
                if matches!(constructor.pcd_args, ConstructorArguments::Pcstr_record(_)) {
                    return Err(PpxError::at_loc(
                        constructor.pcd_loc,
                        ACCESSORS_VARIANT_RECORD_ARG_ERROR,
                    ));
                }
            }
        }
    }

    Ok(())
}

fn validate_payload_deriving_errors(payload: &Payload, arena: &mut ParseArena) -> PpxResult<()> {
    match payload {
        Payload::PStr(items) => validate_structure_deriving_errors(items, arena),
        Payload::PSig(items) => validate_signature_deriving_errors(items, arena),
        Payload::PTyp(_) | Payload::PPat(_) => Ok(()),
    }
}

fn validate_structure_deriving_errors(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                validate_deriving_accessors_for_tdcls(tdcls, arena)?;
            }
            StructureItemDesc::Pstr_module(mb) => {
                let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                validate_module_expr_deriving_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                for mb in mbs.iter() {
                    let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                    validate_module_expr_deriving_errors(&mod_expr, arena)?;
                }
            }
            StructureItemDesc::Pstr_modtype(mtd) => {
                if let Some(mod_type_idx) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type_idx).clone();
                    validate_module_type_deriving_errors(&mod_type, arena)?;
                }
            }
            StructureItemDesc::Pstr_include(incl) => {
                let mod_expr = arena.get_mod_expr(incl.pincl_mod).clone();
                validate_module_expr_deriving_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_attribute(attr) => {
                validate_payload_deriving_errors(&attr.1, arena)?;
            }
            StructureItemDesc::Pstr_extension(inner) => {
                let (extension, _attrs) = &**inner;
                validate_payload_deriving_errors(&extension.1, arena)?;
            }
            StructureItemDesc::Pstr_eval(_)
            | StructureItemDesc::Pstr_value(_)
            | StructureItemDesc::Pstr_primitive(_)
            | StructureItemDesc::Pstr_typext(_)
            | StructureItemDesc::Pstr_exception(_)
            | StructureItemDesc::Pstr_open(_) => {}
        }
    }

    Ok(())
}

fn validate_signature_deriving_errors(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in signature {
        match &*item.psig_desc {
            SignatureItemDesc::Psig_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                validate_deriving_accessors_for_tdcls(tdcls, arena)?;
            }
            SignatureItemDesc::Psig_module(md) => {
                let mod_type = arena.get_mod_type(md.pmd_type).clone();
                validate_module_type_deriving_errors(&mod_type, arena)?;
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                for md in mds.iter() {
                    let mod_type = arena.get_mod_type(md.pmd_type).clone();
                    validate_module_type_deriving_errors(&mod_type, arena)?;
                }
            }
            SignatureItemDesc::Psig_modtype(mtd) => {
                if let Some(mod_type_idx) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type_idx).clone();
                    validate_module_type_deriving_errors(&mod_type, arena)?;
                }
            }
            SignatureItemDesc::Psig_include(incl) => {
                let mod_type = arena.get_mod_type(incl.pincl_mod).clone();
                validate_module_type_deriving_errors(&mod_type, arena)?;
            }
            SignatureItemDesc::Psig_attribute(attr) => {
                validate_payload_deriving_errors(&attr.1, arena)?;
            }
            SignatureItemDesc::Psig_extension(inner) => {
                let (extension, _attrs) = &**inner;
                validate_payload_deriving_errors(&extension.1, arena)?;
            }
            SignatureItemDesc::Psig_value(_)
            | SignatureItemDesc::Psig_typext(_)
            | SignatureItemDesc::Psig_exception(_)
            | SignatureItemDesc::Psig_open(_) => {}
        }
    }

    Ok(())
}

fn validate_module_expr_deriving_errors(
    mod_expr: &current::ModuleExpr,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => validate_structure_deriving_errors(items, arena),
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_name, param_type, body) = &**inner;
            if let Some(param_type_idx) = *param_type {
                let mod_type = arena.get_mod_type(param_type_idx).clone();
                validate_module_type_deriving_errors(&mod_type, arena)?;
            }
            let body_expr = arena.get_mod_expr(*body).clone();
            validate_module_expr_deriving_errors(&body_expr, arena)
        }
        ModuleExprDesc::Pmod_apply(left, right) => {
            let left_expr = arena.get_mod_expr(*left).clone();
            validate_module_expr_deriving_errors(&left_expr, arena)?;
            let right_expr = arena.get_mod_expr(*right).clone();
            validate_module_expr_deriving_errors(&right_expr, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, mod_type_idx) => {
            let inner_expr = arena.get_mod_expr(*inner).clone();
            validate_module_expr_deriving_errors(&inner_expr, arena)?;
            let mod_type = arena.get_mod_type(*mod_type_idx).clone();
            validate_module_type_deriving_errors(&mod_type, arena)
        }
        ModuleExprDesc::Pmod_extension(extension) => {
            validate_payload_deriving_errors(&extension.1, arena)
        }
        ModuleExprDesc::Pmod_ident(_) | ModuleExprDesc::Pmod_unpack(_) => Ok(()),
    }
}

fn validate_module_type_deriving_errors(
    mod_type: &ModuleType,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*mod_type.pmty_desc {
        ModuleTypeDesc::Pmty_signature(items) => validate_signature_deriving_errors(items, arena),
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_name, param_type, result_type) = &**inner;
            if let Some(param_type_idx) = *param_type {
                let param_type = arena.get_mod_type(param_type_idx).clone();
                validate_module_type_deriving_errors(&param_type, arena)?;
            }
            let result_type = arena.get_mod_type(*result_type).clone();
            validate_module_type_deriving_errors(&result_type, arena)
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (mod_type_idx, _constraints) = &**inner;
            let inner_type = arena.get_mod_type(*mod_type_idx).clone();
            validate_module_type_deriving_errors(&inner_type, arena)
        }
        ModuleTypeDesc::Pmty_typeof(mod_expr_idx) => {
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_deriving_errors(&mod_expr, arena)
        }
        ModuleTypeDesc::Pmty_extension(extension) => {
            validate_payload_deriving_errors(&extension.1, arena)
        }
        ModuleTypeDesc::Pmty_ident(_) | ModuleTypeDesc::Pmty_alias(_) => Ok(()),
    }
}

fn is_builtin_rank0_type_name(name: &str) -> bool {
    matches!(
        name,
        "int" | "char" | "float" | "bool" | "unit" | "exn" | "string"
    )
}

fn validate_type_declaration_builtin_type_redefinition_error(
    tdcl: &TypeDeclaration,
    arena: &ParseArena,
) -> PpxResult<()> {
    let name = arena.get_string(tdcl.ptype_name.txt);
    if is_builtin_rank0_type_name(name) {
        return Err(PpxError::at_loc(
            tdcl.ptype_loc,
            format!("built-in type `{name}` can not be redefined "),
        ));
    }
    Ok(())
}

fn core_type_get_uncurry_arity_aux(typ_idx: CoreTypeIdx, acc: i32, arena: &ParseArena) -> i32 {
    let typ = arena.get_core_type(typ_idx);
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (_arg, ret, _arity) = &**inner;
            core_type_get_uncurry_arity_aux(*ret, acc + 1, arena)
        }
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (_vars, typ_idx) = &**inner;
            core_type_get_uncurry_arity_aux(*typ_idx, acc, arena)
        }
        _ => acc,
    }
}

fn core_type_get_curry_arity(typ_idx: CoreTypeIdx, arena: &ParseArena) -> i32 {
    let typ = arena.get_core_type(typ_idx);
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (_arg, _ret, arity) = &**inner;
            arena
                .get_arity(*arity)
                .unwrap_or_else(|| core_type_get_uncurry_arity_aux(typ_idx, 0, arena))
        }
        _ => core_type_get_uncurry_arity_aux(typ_idx, 0, arena),
    }
}

fn core_type_is_arity_one(typ_idx: CoreTypeIdx, arena: &ParseArena) -> bool {
    core_type_get_curry_arity(typ_idx, arena) == 1
}

fn validate_value_description_identity_arity_error(
    vd: &ValueDescription,
    arena: &ParseArena,
) -> PpxResult<()> {
    let [byte_name] = vd.pval_prim.as_slice() else {
        return Ok(());
    };
    if arena.get_string(*byte_name) == "%identity" && !core_type_is_arity_one(vd.pval_type, arena) {
        return Err(PpxError::at_loc(
            vd.pval_loc,
            "%identity expects a function type of the form 'a => 'b (arity 1)",
        ));
    }
    Ok(())
}

fn validate_with_constraint_builtin_type_redefinition_errors(
    constraint: &WithConstraint,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match constraint {
        WithConstraint::Pwith_type(_, tdcl) | WithConstraint::Pwith_typesubst(_, tdcl) => {
            validate_type_declaration_builtin_type_redefinition_error(tdcl, arena)
        }
        WithConstraint::Pwith_module(_, _) | WithConstraint::Pwith_modsubst(_, _) => Ok(()),
    }
}

fn validate_payload_builtin_type_redefinition_errors(
    payload: &Payload,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match payload {
        Payload::PStr(items) => validate_structure_builtin_type_redefinition_errors(items, arena),
        Payload::PSig(items) => validate_signature_builtin_type_redefinition_errors(items, arena),
        Payload::PTyp(_) | Payload::PPat(_) => Ok(()),
    }
}

fn validate_structure_builtin_type_redefinition_errors(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                for tdcl in tdcls {
                    validate_type_declaration_builtin_type_redefinition_error(tdcl, arena)?;
                }
            }
            StructureItemDesc::Pstr_module(mb) => {
                let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                validate_module_expr_builtin_type_redefinition_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                for mb in mbs.iter() {
                    let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                    validate_module_expr_builtin_type_redefinition_errors(&mod_expr, arena)?;
                }
            }
            StructureItemDesc::Pstr_modtype(mtd) => {
                if let Some(mod_type_idx) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type_idx).clone();
                    validate_module_type_builtin_type_redefinition_errors(&mod_type, arena)?;
                }
            }
            StructureItemDesc::Pstr_include(incl) => {
                let mod_expr = arena.get_mod_expr(incl.pincl_mod).clone();
                validate_module_expr_builtin_type_redefinition_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_attribute(attr) => {
                validate_payload_builtin_type_redefinition_errors(&attr.1, arena)?;
            }
            StructureItemDesc::Pstr_extension(inner) => {
                let (extension, _attrs) = &**inner;
                validate_payload_builtin_type_redefinition_errors(&extension.1, arena)?;
            }
            StructureItemDesc::Pstr_primitive(vd) => {
                validate_value_description_identity_arity_error(vd, arena)?;
            }
            StructureItemDesc::Pstr_eval(inner) => {
                let (expr_idx, _attrs) = &**inner;
                validate_expression_builtin_type_redefinition_errors(*expr_idx, arena)?;
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (_rec_flag, bindings) = &**inner;
                for binding in bindings {
                    validate_expression_builtin_type_redefinition_errors(binding.pvb_expr, arena)?;
                }
            }
            StructureItemDesc::Pstr_typext(_)
            | StructureItemDesc::Pstr_exception(_)
            | StructureItemDesc::Pstr_open(_) => {}
        }
    }
    Ok(())
}

fn validate_signature_builtin_type_redefinition_errors(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in signature {
        match &*item.psig_desc {
            SignatureItemDesc::Psig_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                for tdcl in tdcls {
                    validate_type_declaration_builtin_type_redefinition_error(tdcl, arena)?;
                }
            }
            SignatureItemDesc::Psig_module(md) => {
                let mod_type = arena.get_mod_type(md.pmd_type).clone();
                validate_module_type_builtin_type_redefinition_errors(&mod_type, arena)?;
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                for md in mds.iter() {
                    let mod_type = arena.get_mod_type(md.pmd_type).clone();
                    validate_module_type_builtin_type_redefinition_errors(&mod_type, arena)?;
                }
            }
            SignatureItemDesc::Psig_modtype(mtd) => {
                if let Some(mod_type_idx) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type_idx).clone();
                    validate_module_type_builtin_type_redefinition_errors(&mod_type, arena)?;
                }
            }
            SignatureItemDesc::Psig_include(incl) => {
                let mod_type = arena.get_mod_type(incl.pincl_mod).clone();
                validate_module_type_builtin_type_redefinition_errors(&mod_type, arena)?;
            }
            SignatureItemDesc::Psig_attribute(attr) => {
                validate_payload_builtin_type_redefinition_errors(&attr.1, arena)?;
            }
            SignatureItemDesc::Psig_extension(inner) => {
                let (extension, _attrs) = &**inner;
                validate_payload_builtin_type_redefinition_errors(&extension.1, arena)?;
            }
            SignatureItemDesc::Psig_value(vd) => {
                validate_value_description_identity_arity_error(vd, arena)?;
            }
            SignatureItemDesc::Psig_typext(_)
            | SignatureItemDesc::Psig_exception(_)
            | SignatureItemDesc::Psig_open(_) => {}
        }
    }
    Ok(())
}

fn validate_module_expr_builtin_type_redefinition_errors(
    mod_expr: &ModuleExpr,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => {
            validate_structure_builtin_type_redefinition_errors(items, arena)
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_name, param_type, body) = &**inner;
            if let Some(param_type_idx) = *param_type {
                let param_type = arena.get_mod_type(param_type_idx).clone();
                validate_module_type_builtin_type_redefinition_errors(&param_type, arena)?;
            }
            let body = arena.get_mod_expr(*body).clone();
            validate_module_expr_builtin_type_redefinition_errors(&body, arena)
        }
        ModuleExprDesc::Pmod_apply(left, right) => {
            let left = arena.get_mod_expr(*left).clone();
            validate_module_expr_builtin_type_redefinition_errors(&left, arena)?;
            let right = arena.get_mod_expr(*right).clone();
            validate_module_expr_builtin_type_redefinition_errors(&right, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, mod_type_idx) => {
            let inner = arena.get_mod_expr(*inner).clone();
            validate_module_expr_builtin_type_redefinition_errors(&inner, arena)?;
            let mod_type = arena.get_mod_type(*mod_type_idx).clone();
            validate_module_type_builtin_type_redefinition_errors(&mod_type, arena)
        }
        ModuleExprDesc::Pmod_extension(extension) => {
            validate_payload_builtin_type_redefinition_errors(&extension.1, arena)
        }
        ModuleExprDesc::Pmod_unpack(expr_idx) => {
            validate_expression_builtin_type_redefinition_errors(*expr_idx, arena)
        }
        ModuleExprDesc::Pmod_ident(_) => Ok(()),
    }
}

fn validate_expression_builtin_type_redefinition_errors(
    expr_idx: ExprIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let expr = arena.get_expr(expr_idx).clone();
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_let(inner) => {
            let (_rec_flag, bindings, body) = &**inner;
            for binding in bindings {
                validate_expression_builtin_type_redefinition_errors(binding.pvb_expr, arena)?;
            }
            validate_expression_builtin_type_redefinition_errors(*body, arena)
        }
        ExpressionDesc::Pexp_fun(fun) => {
            if let Some(default) = fun.default {
                validate_expression_builtin_type_redefinition_errors(default, arena)?;
            }
            validate_expression_builtin_type_redefinition_errors(fun.rhs, arena)
        }
        ExpressionDesc::Pexp_apply(apply) => {
            validate_expression_builtin_type_redefinition_errors(apply.funct, arena)?;
            for (_label, arg) in &apply.args {
                validate_expression_builtin_type_redefinition_errors(*arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*scrutinee, arena)?;
            for case in cases {
                if let Some(guard) = case.pc_guard {
                    validate_expression_builtin_type_redefinition_errors(guard, arena)?;
                }
                validate_expression_builtin_type_redefinition_errors(case.pc_rhs, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            for item in items.iter() {
                validate_expression_builtin_type_redefinition_errors(*item, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_construct(_, arg) => {
            if let Some(arg) = arg {
                validate_expression_builtin_type_redefinition_errors(*arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_variant(inner) => {
            let (_label, arg) = &**inner;
            if let Some(arg) = arg {
                validate_expression_builtin_type_redefinition_errors(*arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, spread) = &**inner;
            for field in fields {
                validate_expression_builtin_type_redefinition_errors(field.expr, arena)?;
            }
            if let Some(spread) = spread {
                validate_expression_builtin_type_redefinition_errors(*spread, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_field(owner, _)
        | ExpressionDesc::Pexp_assert(owner)
        | ExpressionDesc::Pexp_await(owner)
        | ExpressionDesc::Pexp_comptime_compile_error(owner)
        | ExpressionDesc::Pexp_comptime_build_variant(owner)
        | ExpressionDesc::Pexp_comptime_variant_case(owner)
        | ExpressionDesc::Pexp_comptime_build_record(owner)
        | ExpressionDesc::Pexp_comptime_record_field(owner) => {
            validate_expression_builtin_type_redefinition_errors(*owner, arena)
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (owner, _field, value) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*owner, arena)?;
            validate_expression_builtin_type_redefinition_errors(*value, arena)
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (condition, then_expr, else_expr) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*condition, arena)?;
            validate_expression_builtin_type_redefinition_errors(*then_expr, arena)?;
            if let Some(else_expr) = else_expr {
                validate_expression_builtin_type_redefinition_errors(*else_expr, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_sequence(first, second) => {
            validate_expression_builtin_type_redefinition_errors(*first, arena)?;
            validate_expression_builtin_type_redefinition_errors(*second, arena)
        }
        ExpressionDesc::Pexp_while(condition, body) => {
            validate_expression_builtin_type_redefinition_errors(*condition, arena)?;
            validate_expression_builtin_type_redefinition_errors(*body, arena)
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (_pat, start, stop, _direction, body) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*start, arena)?;
            validate_expression_builtin_type_redefinition_errors(*stop, arena)?;
            validate_expression_builtin_type_redefinition_errors(*body, arena)
        }
        ExpressionDesc::Pexp_for_of(inner)
        | ExpressionDesc::Pexp_for_await_of(inner)
        | ExpressionDesc::Pexp_inline_for(inner) => {
            let (_pat, iterable, body) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*iterable, arena)?;
            validate_expression_builtin_type_redefinition_errors(*body, arena)
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (inner_expr, _typ) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*inner_expr, arena)
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (inner_expr, _from_typ, _to_typ) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*inner_expr, arena)
        }
        ExpressionDesc::Pexp_send(inner) => {
            let (owner, _method) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*owner, arena)
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_name, mod_expr_idx, body) = &**inner;
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_builtin_type_redefinition_errors(&mod_expr, arena)?;
            validate_expression_builtin_type_redefinition_errors(*body, arena)
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (_extension, body) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*body, arena)
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (_name, body) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*body, arena)
        }
        ExpressionDesc::Pexp_pack(mod_expr_idx) => {
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_builtin_type_redefinition_errors(&mod_expr, arena)
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (_override_flag, _lid, body) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*body, arena)
        }
        ExpressionDesc::Pexp_extension(extension) => {
            validate_payload_builtin_type_redefinition_errors(&extension.1, arena)
        }
        ExpressionDesc::Pexp_comptime_field(inner) => {
            let (value, field) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*value, arena)?;
            validate_expression_builtin_type_redefinition_errors(*field, arena)
        }
        ExpressionDesc::Pexp_comptime_record(inner) => {
            let (_typ, fields) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*fields, arena)
        }
        ExpressionDesc::Pexp_comptime_variant(inner) => {
            let (_typ, constructor, payload) = &**inner;
            validate_expression_builtin_type_redefinition_errors(*constructor, arena)?;
            if let Some(payload) = payload {
                validate_expression_builtin_type_redefinition_errors(*payload, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue
        | ExpressionDesc::Pexp_jsx_element(_)
        | ExpressionDesc::Pexp_comptime_typeinfo(_)
        | ExpressionDesc::Pexp_comptime_typename(_) => Ok(()),
    }
}

fn validate_module_type_builtin_type_redefinition_errors(
    mod_type: &ModuleType,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*mod_type.pmty_desc {
        ModuleTypeDesc::Pmty_signature(items) => {
            validate_signature_builtin_type_redefinition_errors(items, arena)
        }
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_name, param_type, result_type) = &**inner;
            if let Some(param_type_idx) = *param_type {
                let param_type = arena.get_mod_type(param_type_idx).clone();
                validate_module_type_builtin_type_redefinition_errors(&param_type, arena)?;
            }
            let result_type = arena.get_mod_type(*result_type).clone();
            validate_module_type_builtin_type_redefinition_errors(&result_type, arena)
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (mod_type_idx, constraints) = &**inner;
            let mod_type = arena.get_mod_type(*mod_type_idx).clone();
            validate_module_type_builtin_type_redefinition_errors(&mod_type, arena)?;
            for constraint in constraints {
                validate_with_constraint_builtin_type_redefinition_errors(constraint, arena)?;
            }
            Ok(())
        }
        ModuleTypeDesc::Pmty_typeof(mod_expr_idx) => {
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_builtin_type_redefinition_errors(&mod_expr, arena)
        }
        ModuleTypeDesc::Pmty_extension(extension) => {
            validate_payload_builtin_type_redefinition_errors(&extension.1, arena)
        }
        ModuleTypeDesc::Pmty_ident(_) | ModuleTypeDesc::Pmty_alias(_) => Ok(()),
    }
}

fn validate_method_attribute_config_names<F>(
    payload: &Payload,
    arena: &ParseArena,
    mut validate_name: F,
) -> PpxResult<()>
where
    F: FnMut(&str, LocIdx, Option<ExprIdx>) -> PpxResult<()>,
{
    let Payload::PStr(items) = payload else {
        return Ok(());
    };
    if items.len() != 1 {
        return Ok(());
    }
    let StructureItemDesc::Pstr_eval(inner) = &*items[0].pstr_desc else {
        return Ok(());
    };
    let (expr_idx, _) = &**inner;
    let expr = arena.get_expr(*expr_idx);
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => {
            if let Longident::Lident(name_idx) = arena.get_longident(lid.txt) {
                validate_name(arena.get_string(*name_idx), lid.loc, None)?;
            }
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, with_obj) = &**inner;
            if with_obj.is_some() {
                return Ok(());
            }
            for field in fields {
                let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) else {
                    return Err(PpxError::at_loc(
                        expr.pexp_loc,
                        "Qualified label is not allowed",
                    ));
                };
                let name = arena.get_string(*name_idx);
                let field_expr = arena.get_expr(field.expr);
                let is_punned = match &*field_expr.pexp_desc {
                    ExpressionDesc::Pexp_ident(value_lid) => {
                        matches!(
                            arena.get_longident(value_lid.txt),
                            Longident::Lident(value_name_idx)
                                if arena.get_string(*value_name_idx) == name
                        )
                    }
                    _ => false,
                };
                let opt_expr = if is_punned { None } else { Some(field.expr) };
                validate_name(name, field.lid.loc, opt_expr)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn validate_method_attribute_bool_payload(
    opt_expr: Option<ExprIdx>,
    arena: &ParseArena,
) -> PpxResult<()> {
    let Some(expr_idx) = opt_expr else {
        return Ok(());
    };
    let expr = arena.get_expr(expr_idx);
    let is_bool_literal = match &*expr.pexp_desc {
        ExpressionDesc::Pexp_construct(lid, None) => {
            matches!(
                arena.get_longident(lid.txt),
                Longident::Lident(name_idx)
                    if matches!(arena.get_string(*name_idx), "true" | "false")
            )
        }
        _ => false,
    };
    if is_bool_literal {
        Ok(())
    } else {
        Err(PpxError::at_loc(
            expr.pexp_loc,
            "expect `true` or `false` in this field",
        ))
    }
}

fn validate_object_field_method_attrs(attrs: &[Attribute], arena: &ParseArena) -> PpxResult<()> {
    for (attr_name, payload) in attrs {
        match arena.get_string(attr_name.txt) {
            "get" => {
                validate_method_attribute_config_names(payload, arena, |name, loc, opt_expr| {
                    match name {
                        "null" | "undefined" | "nullable" => {
                            validate_method_attribute_bool_payload(opt_expr, arena)
                        }
                        _ => Err(PpxError::at_loc(loc, "unsupported predicates")),
                    }
                })?;
            }
            "set" => {
                validate_method_attribute_config_names(payload, arena, |name, loc, opt_expr| {
                    match name {
                        "no_get" => validate_method_attribute_bool_payload(opt_expr, arena),
                        _ => Err(PpxError::at_loc(loc, "unsupported predicates")),
                    }
                })?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_core_type_method_attribute_errors(
    typ: &CoreType,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, _arity) = &**inner;
            let arg_type = arena.get_core_type(arg.typ).clone();
            validate_core_type_method_attribute_errors(&arg_type, arena)?;
            let ret_type = arena.get_core_type(*ret).clone();
            validate_core_type_method_attribute_errors(&ret_type, arena)
        }
        CoreTypeDesc::Ptyp_tuple(types) => {
            for typ_idx in types.iter() {
                let child = arena.get_core_type(*typ_idx).clone();
                validate_core_type_method_attribute_errors(&child, arena)?;
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (_lid, types) = &**inner;
            for typ_idx in types.iter() {
                let child = arena.get_core_type(*typ_idx).clone();
                validate_core_type_method_attribute_errors(&child, arena)?;
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            let (fields, _closed) = &**inner;
            for field in fields {
                match field {
                    ObjectField::Otag(_name, attrs, typ_idx) => {
                        validate_object_field_method_attrs(attrs, arena)?;
                        let child = arena.get_core_type(*typ_idx).clone();
                        validate_core_type_method_attribute_errors(&child, arena)?;
                    }
                    ObjectField::Oinherit(typ_idx) => {
                        let child = arena.get_core_type(*typ_idx).clone();
                        validate_core_type_method_attribute_errors(&child, arena)?;
                    }
                }
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (typ_idx, _name) = &**inner;
            let child = arena.get_core_type(*typ_idx).clone();
            validate_core_type_method_attribute_errors(&child, arena)
        }
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (_vars, typ_idx) = &**inner;
            let child = arena.get_core_type(*typ_idx).clone();
            validate_core_type_method_attribute_errors(&child, arena)
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (rows, _closed, _labels) = &**inner;
            for row in rows {
                match row {
                    RowField::Rtag(_label, _attrs, _empty, types) => {
                        for typ_idx in types {
                            let child = arena.get_core_type(*typ_idx).clone();
                            validate_core_type_method_attribute_errors(&child, arena)?;
                        }
                    }
                    RowField::Rinherit(typ_idx) => {
                        let child = arena.get_core_type(*typ_idx).clone();
                        validate_core_type_method_attribute_errors(&child, arena)?;
                    }
                }
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_package(pkg) => {
            let (_lid, constraints) = &**pkg;
            for (_lid, typ_idx) in constraints {
                let child = arena.get_core_type(*typ_idx).clone();
                validate_core_type_method_attribute_errors(&child, arena)?;
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_extension(extension) => {
            validate_payload_method_attribute_errors(&extension.1, arena)
        }
        CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => Ok(()),
    }
}

fn validate_constructor_args_method_attribute_errors(
    args: &ConstructorArguments,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match args {
        ConstructorArguments::Pcstr_tuple(types) => {
            for typ_idx in types {
                let typ = arena.get_core_type(*typ_idx).clone();
                validate_core_type_method_attribute_errors(&typ, arena)?;
            }
        }
        ConstructorArguments::Pcstr_record(labels) => {
            for label in labels {
                let typ = arena.get_core_type(label.pld_type).clone();
                validate_core_type_method_attribute_errors(&typ, arena)?;
            }
        }
    }
    Ok(())
}

fn validate_type_declaration_method_attribute_errors(
    tdcl: &TypeDeclaration,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for (param, _) in &tdcl.ptype_params {
        let typ = arena.get_core_type(*param).clone();
        validate_core_type_method_attribute_errors(&typ, arena)?;
    }
    for (left, right, _loc) in &tdcl.ptype_cstrs {
        let left = arena.get_core_type(*left).clone();
        validate_core_type_method_attribute_errors(&left, arena)?;
        let right = arena.get_core_type(*right).clone();
        validate_core_type_method_attribute_errors(&right, arena)?;
    }
    if let Some(manifest) = tdcl.ptype_manifest {
        let typ = arena.get_core_type(manifest).clone();
        validate_core_type_method_attribute_errors(&typ, arena)?;
    }
    match &tdcl.ptype_kind {
        TypeKind::Ptype_record(labels) => {
            for label in labels {
                let typ = arena.get_core_type(label.pld_type).clone();
                validate_core_type_method_attribute_errors(&typ, arena)?;
            }
        }
        TypeKind::Ptype_variant(constructors) => {
            for constructor in constructors {
                validate_constructor_args_method_attribute_errors(&constructor.pcd_args, arena)?;
                if let Some(res) = constructor.pcd_res {
                    let typ = arena.get_core_type(res).clone();
                    validate_core_type_method_attribute_errors(&typ, arena)?;
                }
            }
        }
        TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
    }
    Ok(())
}

fn validate_type_extension_method_attribute_errors(
    ext: &TypeExtension,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for (param, _) in &ext.ptyext_params {
        let typ = arena.get_core_type(*param).clone();
        validate_core_type_method_attribute_errors(&typ, arena)?;
    }
    for constructor in &ext.ptyext_constructors {
        validate_extension_constructor_method_attribute_errors(constructor, arena)?;
    }
    Ok(())
}

fn validate_extension_constructor_method_attribute_errors(
    ext: &ExtensionConstructor,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &ext.pext_kind {
        ExtensionConstructorKind::Pext_decl(args, res) => {
            validate_constructor_args_method_attribute_errors(args, arena)?;
            if let Some(res) = res {
                let typ = arena.get_core_type(*res).clone();
                validate_core_type_method_attribute_errors(&typ, arena)?;
            }
        }
        ExtensionConstructorKind::Pext_rebind(_) => {}
    }
    Ok(())
}

fn validate_payload_method_attribute_errors(
    payload: &Payload,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match payload {
        Payload::PStr(items) => validate_structure_method_attribute_errors(items, arena),
        Payload::PSig(items) => validate_signature_method_attribute_errors(items, arena),
        Payload::PTyp(typ_idx) => {
            let typ = arena.get_core_type(*typ_idx).clone();
            validate_core_type_method_attribute_errors(&typ, arena)
        }
        Payload::PPat(inner) => {
            let (pat_idx, guard) = &**inner;
            validate_pattern_idx_method_attribute_errors(*pat_idx, arena)?;
            if let Some(guard) = guard {
                validate_expression_idx_method_attribute_errors(*guard, arena)?;
            }
            Ok(())
        }
    }
}

fn validate_expression_extension_payload_error(
    extension: &current::Extension,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let (ext_name, payload) = extension;
    let name = arena.get_string(ext_name.txt);
    match name {
        "debugger" if !payload_is_empty_str(payload) => Err(PpxError::at_loc(
            ext_name.loc,
            "%debugger extension doesn't accept arguments",
        )),
        "raw" if payload_single_string_literal(payload, arena).is_none() => Err(PpxError::at_loc(
            ext_name.loc,
            "%raw extension can only be applied to a string",
        )),
        "re" => match payload_single_string_literal_with_loc(payload, arena) {
            None => Err(PpxError::at_loc(
                ext_name.loc,
                "%re extension can only be applied to a string",
            )),
            Some((code, loc)) if !is_js_regex_literal(code) && !is_js_regex_like_literal(code) => {
                Err(PpxError::at_loc(
                    loc,
                    "Syntax error: a valid JS regex literal expected",
                ))
            }
            Some(_) => Ok(()),
        },
        "ffi" => match payload_single_string_literal_info(payload, arena) {
            Some((code, payload_loc, first_line_offset)) => {
                let code = code.to_string();
                if is_js_function(&code) {
                    Ok(())
                } else {
                    let err = PpxError::at_loc(
                        ext_name.loc,
                        "%ffi extension can only be applied to a string containing a JavaScript function such as \"(x) => ...\"",
                    );
                    if let Some(warning) = raw_js_expression_parse_warning(
                        &code,
                        payload_loc,
                        first_line_offset,
                        arena,
                    ) {
                        Err(err.with_warning(
                            warning.loc,
                            Warning::BsFfiWarning {
                                message: warning.message,
                            },
                        ))
                    } else {
                        Err(err)
                    }
                }
            }
            None => Err(PpxError::at_loc(
                ext_name.loc,
                "%ffi extension can only be applied to a string containing a JavaScript function such as \"(x) => ...\"",
            )),
        },
        "obj" => validate_obj_extension_payload_error(payload, ext_name.loc, arena),
        _ => Ok(()),
    }
}

fn validate_obj_extension_payload_error(
    payload: &Payload,
    ext_loc: LocIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let Some(fields) = payload_single_record_fields_without_spread(payload, arena) else {
        return Err(PpxError::at_loc(ext_loc, "Expect a record expression here"));
    };
    for field in fields {
        let lid = arena.get_longident(field.lid.txt);
        if !matches!(lid, Longident::Lident(_)) {
            return Err(PpxError::at_loc(field.lid.loc, "invalid js label "));
        }
    }
    Ok(())
}

fn validate_structure_extension_payload_error(
    extension: &current::Extension,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let (ext_name, payload) = extension;
    let name = arena.get_string(ext_name.txt);
    if name == "raw" && payload_single_string_literal(payload, arena).is_none() {
        Err(PpxError::at_loc(
            ext_name.loc,
            "%%raw extension can only be applied to a string",
        ))
    } else {
        Ok(())
    }
}

fn validate_structure_method_attribute_errors(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(inner) => {
                let (expr, attrs) = &**inner;
                validate_expression_idx_method_attribute_errors(*expr, arena)?;
                for attr in attrs.iter() {
                    validate_payload_method_attribute_errors(&attr.1, arena)?;
                }
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (_rec_flag, bindings) = &**inner;
                for binding in bindings {
                    validate_pattern_idx_method_attribute_errors(binding.pvb_pat, arena)?;
                    validate_expression_idx_method_attribute_errors(binding.pvb_expr, arena)?;
                    for attr in binding.pvb_attributes.iter() {
                        validate_payload_method_attribute_errors(&attr.1, arena)?;
                    }
                }
            }
            StructureItemDesc::Pstr_primitive(vd) => {
                let typ = arena.get_core_type(vd.pval_type).clone();
                validate_core_type_method_attribute_errors(&typ, arena)?;
                for attr in vd.pval_attributes.iter() {
                    validate_payload_method_attribute_errors(&attr.1, arena)?;
                }
            }
            StructureItemDesc::Pstr_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                for tdcl in tdcls {
                    validate_type_declaration_method_attribute_errors(tdcl, arena)?;
                }
            }
            StructureItemDesc::Pstr_typext(ext) => {
                validate_type_extension_method_attribute_errors(ext, arena)?;
            }
            StructureItemDesc::Pstr_exception(ext) => {
                validate_extension_constructor_method_attribute_errors(ext, arena)?;
            }
            StructureItemDesc::Pstr_module(mb) => {
                let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                validate_module_expr_method_attribute_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                for mb in mbs.iter() {
                    let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                    validate_module_expr_method_attribute_errors(&mod_expr, arena)?;
                }
            }
            StructureItemDesc::Pstr_modtype(mtd) => {
                if let Some(mod_type_idx) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type_idx).clone();
                    validate_module_type_method_attribute_errors(&mod_type, arena)?;
                }
            }
            StructureItemDesc::Pstr_include(incl) => {
                let mod_expr = arena.get_mod_expr(incl.pincl_mod).clone();
                validate_module_expr_method_attribute_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_attribute(attr) => {
                validate_payload_method_attribute_errors(&attr.1, arena)?;
            }
            StructureItemDesc::Pstr_extension(inner) => {
                let (extension, attrs) = &**inner;
                validate_structure_extension_payload_error(extension, arena)?;
                validate_payload_method_attribute_errors(&extension.1, arena)?;
                for attr in attrs.iter() {
                    validate_payload_method_attribute_errors(&attr.1, arena)?;
                }
            }
            StructureItemDesc::Pstr_open(_) => {}
        }
    }
    Ok(())
}

fn validate_signature_method_attribute_errors(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in signature {
        match &*item.psig_desc {
            SignatureItemDesc::Psig_value(vd) => {
                let typ = arena.get_core_type(vd.pval_type).clone();
                validate_core_type_method_attribute_errors(&typ, arena)?;
            }
            SignatureItemDesc::Psig_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                for tdcl in tdcls {
                    validate_type_declaration_method_attribute_errors(tdcl, arena)?;
                }
            }
            SignatureItemDesc::Psig_typext(ext) => {
                validate_type_extension_method_attribute_errors(ext, arena)?;
            }
            SignatureItemDesc::Psig_exception(ext) => {
                validate_extension_constructor_method_attribute_errors(ext, arena)?;
            }
            SignatureItemDesc::Psig_module(md) => {
                let mod_type = arena.get_mod_type(md.pmd_type).clone();
                validate_module_type_method_attribute_errors(&mod_type, arena)?;
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                for md in mds.iter() {
                    let mod_type = arena.get_mod_type(md.pmd_type).clone();
                    validate_module_type_method_attribute_errors(&mod_type, arena)?;
                }
            }
            SignatureItemDesc::Psig_modtype(mtd) => {
                if let Some(mod_type_idx) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type_idx).clone();
                    validate_module_type_method_attribute_errors(&mod_type, arena)?;
                }
            }
            SignatureItemDesc::Psig_include(incl) => {
                let mod_type = arena.get_mod_type(incl.pincl_mod).clone();
                validate_module_type_method_attribute_errors(&mod_type, arena)?;
            }
            SignatureItemDesc::Psig_attribute(attr) => {
                validate_payload_method_attribute_errors(&attr.1, arena)?;
            }
            SignatureItemDesc::Psig_extension(inner) => {
                let (extension, attrs) = &**inner;
                validate_payload_method_attribute_errors(&extension.1, arena)?;
                for attr in attrs.iter() {
                    validate_payload_method_attribute_errors(&attr.1, arena)?;
                }
            }
            SignatureItemDesc::Psig_open(_) => {}
        }
    }
    Ok(())
}

fn validate_module_expr_method_attribute_errors(
    mod_expr: &ModuleExpr,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => {
            validate_structure_method_attribute_errors(items, arena)
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_name, param_type, body) = &**inner;
            if let Some(param_type_idx) = *param_type {
                let mod_type = arena.get_mod_type(param_type_idx).clone();
                validate_module_type_method_attribute_errors(&mod_type, arena)?;
            }
            let body = arena.get_mod_expr(*body).clone();
            validate_module_expr_method_attribute_errors(&body, arena)
        }
        ModuleExprDesc::Pmod_apply(left, right) => {
            let left = arena.get_mod_expr(*left).clone();
            validate_module_expr_method_attribute_errors(&left, arena)?;
            let right = arena.get_mod_expr(*right).clone();
            validate_module_expr_method_attribute_errors(&right, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, mod_type_idx) => {
            let inner = arena.get_mod_expr(*inner).clone();
            validate_module_expr_method_attribute_errors(&inner, arena)?;
            let mod_type = arena.get_mod_type(*mod_type_idx).clone();
            validate_module_type_method_attribute_errors(&mod_type, arena)
        }
        ModuleExprDesc::Pmod_unpack(expr_idx) => {
            validate_expression_idx_method_attribute_errors(*expr_idx, arena)
        }
        ModuleExprDesc::Pmod_extension(extension) => {
            validate_payload_method_attribute_errors(&extension.1, arena)
        }
        ModuleExprDesc::Pmod_ident(_) => Ok(()),
    }
}

fn validate_module_type_method_attribute_errors(
    mod_type: &ModuleType,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*mod_type.pmty_desc {
        ModuleTypeDesc::Pmty_signature(items) => {
            validate_signature_method_attribute_errors(items, arena)
        }
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_name, param_type, result_type) = &**inner;
            if let Some(param_type_idx) = *param_type {
                let param_type = arena.get_mod_type(param_type_idx).clone();
                validate_module_type_method_attribute_errors(&param_type, arena)?;
            }
            let result_type = arena.get_mod_type(*result_type).clone();
            validate_module_type_method_attribute_errors(&result_type, arena)
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (mod_type_idx, constraints) = &**inner;
            let inner_type = arena.get_mod_type(*mod_type_idx).clone();
            validate_module_type_method_attribute_errors(&inner_type, arena)?;
            for constraint in constraints {
                match constraint {
                    WithConstraint::Pwith_type(_, tdcl)
                    | WithConstraint::Pwith_typesubst(_, tdcl) => {
                        validate_type_declaration_method_attribute_errors(tdcl, arena)?;
                    }
                    WithConstraint::Pwith_module(_, _) | WithConstraint::Pwith_modsubst(_, _) => {}
                }
            }
            Ok(())
        }
        ModuleTypeDesc::Pmty_typeof(mod_expr_idx) => {
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_method_attribute_errors(&mod_expr, arena)
        }
        ModuleTypeDesc::Pmty_extension(extension) => {
            validate_payload_method_attribute_errors(&extension.1, arena)
        }
        ModuleTypeDesc::Pmty_ident(_) | ModuleTypeDesc::Pmty_alias(_) => Ok(()),
    }
}

fn validate_pattern_idx_method_attribute_errors(
    pat_idx: PatIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let pat = arena.get_pat(pat_idx).clone();
    validate_pattern_method_attribute_errors(&pat, arena)
}

fn validate_pattern_method_attribute_errors(
    pat: &Pattern,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*pat.ppat_desc {
        PatternDesc::Ppat_alias(inner, _)
        | PatternDesc::Ppat_exception(inner)
        | PatternDesc::Ppat_open(_, inner) => {
            validate_pattern_idx_method_attribute_errors(*inner, arena)
        }
        PatternDesc::Ppat_tuple(items) | PatternDesc::Ppat_array(items) => {
            for item in items.iter() {
                validate_pattern_idx_method_attribute_errors(*item, arena)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_construct(_, arg) => {
            if let Some(arg) = arg {
                validate_pattern_idx_method_attribute_errors(*arg, arena)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_variant(inner) => {
            let (_label, arg) = &**inner;
            if let Some(arg) = arg {
                validate_pattern_idx_method_attribute_errors(*arg, arena)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_record(inner) => {
            let (fields, _closed) = &**inner;
            for field in fields {
                validate_pattern_idx_method_attribute_errors(field.pat, arena)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_or(left, right) => {
            validate_pattern_idx_method_attribute_errors(*left, arena)?;
            validate_pattern_idx_method_attribute_errors(*right, arena)
        }
        PatternDesc::Ppat_constraint(inner) => {
            let (inner_pat, typ_idx) = &**inner;
            validate_pattern_idx_method_attribute_errors(*inner_pat, arena)?;
            let typ = arena.get_core_type(*typ_idx).clone();
            validate_core_type_method_attribute_errors(&typ, arena)
        }
        PatternDesc::Ppat_extension(extension) => {
            validate_payload_method_attribute_errors(&extension.1, arena)
        }
        PatternDesc::Ppat_any
        | PatternDesc::Ppat_var(_)
        | PatternDesc::Ppat_constant(_)
        | PatternDesc::Ppat_interval(_)
        | PatternDesc::Ppat_type(_)
        | PatternDesc::Ppat_unpack(_) => Ok(()),
    }
}

fn validate_expression_idx_method_attribute_errors(
    expr_idx: ExprIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let expr = arena.get_expr(expr_idx).clone();
    validate_expression_method_attribute_errors(&expr, arena)
}

fn validate_cases_method_attribute_errors(cases: &[Case], arena: &mut ParseArena) -> PpxResult<()> {
    for case in cases {
        validate_pattern_idx_method_attribute_errors(case.pc_lhs, arena)?;
        if let Some(guard) = case.pc_guard {
            validate_expression_idx_method_attribute_errors(guard, arena)?;
        }
        validate_expression_idx_method_attribute_errors(case.pc_rhs, arena)?;
    }
    Ok(())
}

fn validate_jsx_element_method_attribute_errors(
    jsx: &JsxElement,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match jsx {
        JsxElement::Fragment(fragment) => {
            for child in &fragment.children {
                validate_expression_idx_method_attribute_errors(*child, arena)?;
            }
        }
        JsxElement::Unary(elem) => {
            validate_jsx_props_method_attribute_errors(&elem.props, arena)?;
        }
        JsxElement::Container(elem) => {
            validate_jsx_props_method_attribute_errors(&elem.props, arena)?;
            for child in &elem.children {
                validate_expression_idx_method_attribute_errors(*child, arena)?;
            }
        }
    }
    Ok(())
}

fn validate_jsx_props_method_attribute_errors(
    props: &[JsxProp],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for prop in props {
        match prop {
            JsxProp::Value { value, .. } => {
                validate_expression_idx_method_attribute_errors(*value, arena)?;
            }
            JsxProp::Spreading { expr, .. } => {
                validate_expression_idx_method_attribute_errors(*expr, arena)?;
            }
            JsxProp::Punning { .. } => {}
        }
    }
    Ok(())
}

fn validate_expression_method_attribute_errors(
    expr: &Expression,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_let(inner) => {
            let (_rec_flag, bindings, body) = &**inner;
            for binding in bindings {
                validate_pattern_idx_method_attribute_errors(binding.pvb_pat, arena)?;
                validate_expression_idx_method_attribute_errors(binding.pvb_expr, arena)?;
            }
            validate_expression_idx_method_attribute_errors(*body, arena)
        }
        ExpressionDesc::Pexp_fun(inner) => {
            validate_pattern_idx_method_attribute_errors(inner.lhs, arena)?;
            if let Some(default) = inner.default {
                validate_expression_idx_method_attribute_errors(default, arena)?;
            }
            validate_expression_idx_method_attribute_errors(inner.rhs, arena)
        }
        ExpressionDesc::Pexp_apply(inner) => {
            validate_expression_idx_method_attribute_errors(inner.funct, arena)?;
            for (_label, arg) in &inner.args {
                validate_expression_idx_method_attribute_errors(*arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            validate_expression_idx_method_attribute_errors(*scrutinee, arena)?;
            validate_cases_method_attribute_errors(cases, arena)
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            for item in items.iter() {
                validate_expression_idx_method_attribute_errors(*item, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_construct(_, Some(arg))
        | ExpressionDesc::Pexp_field(arg, _)
        | ExpressionDesc::Pexp_assert(arg)
        | ExpressionDesc::Pexp_await(arg)
        | ExpressionDesc::Pexp_comptime_compile_error(arg)
        | ExpressionDesc::Pexp_comptime_build_variant(arg)
        | ExpressionDesc::Pexp_comptime_variant_case(arg)
        | ExpressionDesc::Pexp_comptime_build_record(arg)
        | ExpressionDesc::Pexp_comptime_record_field(arg) => {
            validate_expression_idx_method_attribute_errors(*arg, arena)
        }
        ExpressionDesc::Pexp_send(inner) => {
            let (arg, _method) = &**inner;
            validate_expression_idx_method_attribute_errors(*arg, arena)
        }
        ExpressionDesc::Pexp_variant(inner) => {
            if let Some(arg) = inner.1 {
                validate_expression_idx_method_attribute_errors(arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, spread) = &**inner;
            if let Some(spread) = spread {
                validate_expression_idx_method_attribute_errors(*spread, arena)?;
            }
            for field in fields {
                validate_expression_idx_method_attribute_errors(field.expr, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (target, _field, value) = &**inner;
            validate_expression_idx_method_attribute_errors(*target, arena)?;
            validate_expression_idx_method_attribute_errors(*value, arena)
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (cond, then_expr, else_expr) = &**inner;
            validate_expression_idx_method_attribute_errors(*cond, arena)?;
            validate_expression_idx_method_attribute_errors(*then_expr, arena)?;
            if let Some(else_expr) = else_expr {
                validate_expression_idx_method_attribute_errors(*else_expr, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_sequence(left, right) | ExpressionDesc::Pexp_while(left, right) => {
            validate_expression_idx_method_attribute_errors(*left, arena)?;
            validate_expression_idx_method_attribute_errors(*right, arena)
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (pat, start, finish, _dir, body) = &**inner;
            validate_pattern_idx_method_attribute_errors(*pat, arena)?;
            validate_expression_idx_method_attribute_errors(*start, arena)?;
            validate_expression_idx_method_attribute_errors(*finish, arena)?;
            validate_expression_idx_method_attribute_errors(*body, arena)
        }
        ExpressionDesc::Pexp_for_of(inner)
        | ExpressionDesc::Pexp_for_await_of(inner)
        | ExpressionDesc::Pexp_inline_for(inner) => {
            let (pat, collection, body) = &**inner;
            validate_pattern_idx_method_attribute_errors(*pat, arena)?;
            validate_expression_idx_method_attribute_errors(*collection, arena)?;
            validate_expression_idx_method_attribute_errors(*body, arena)
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (inner_expr, typ_idx) = &**inner;
            validate_expression_idx_method_attribute_errors(*inner_expr, arena)?;
            let typ = arena.get_core_type(*typ_idx).clone();
            validate_core_type_method_attribute_errors(&typ, arena)
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (inner_expr, from_type, to_type) = &**inner;
            validate_expression_idx_method_attribute_errors(*inner_expr, arena)?;
            if let Some(from_type) = from_type {
                let typ = arena.get_core_type(*from_type).clone();
                validate_core_type_method_attribute_errors(&typ, arena)?;
            }
            let typ = arena.get_core_type(*to_type).clone();
            validate_core_type_method_attribute_errors(&typ, arena)
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_name, mod_expr, body) = &**inner;
            let mod_expr = arena.get_mod_expr(*mod_expr).clone();
            validate_module_expr_method_attribute_errors(&mod_expr, arena)?;
            validate_expression_idx_method_attribute_errors(*body, arena)
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (ext, body) = &**inner;
            validate_extension_constructor_method_attribute_errors(ext, arena)?;
            validate_expression_idx_method_attribute_errors(*body, arena)
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (_name, body) = &**inner;
            validate_expression_idx_method_attribute_errors(*body, arena)
        }
        ExpressionDesc::Pexp_pack(mod_expr_idx) => {
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_method_attribute_errors(&mod_expr, arena)
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (_override, _lid, body) = &**inner;
            validate_expression_idx_method_attribute_errors(*body, arena)
        }
        ExpressionDesc::Pexp_extension(extension) => {
            validate_expression_extension_payload_error(extension, arena)?;
            validate_payload_method_attribute_errors(&extension.1, arena)
        }
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            validate_jsx_element_method_attribute_errors(jsx, arena)
        }
        ExpressionDesc::Pexp_comptime_field(inner) => {
            let (value, field) = &**inner;
            validate_expression_idx_method_attribute_errors(*value, arena)?;
            validate_expression_idx_method_attribute_errors(*field, arena)
        }
        ExpressionDesc::Pexp_comptime_record(inner) => {
            let (typ_idx, fields) = &**inner;
            let typ = arena.get_core_type(*typ_idx).clone();
            validate_core_type_method_attribute_errors(&typ, arena)?;
            validate_expression_idx_method_attribute_errors(*fields, arena)
        }
        ExpressionDesc::Pexp_comptime_variant(inner) => {
            let (typ_idx, name, payload) = &**inner;
            let typ = arena.get_core_type(*typ_idx).clone();
            validate_core_type_method_attribute_errors(&typ, arena)?;
            validate_expression_idx_method_attribute_errors(*name, arena)?;
            if let Some(payload) = payload {
                validate_expression_idx_method_attribute_errors(*payload, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_comptime_typeinfo(typ_idx)
        | ExpressionDesc::Pexp_comptime_typename(typ_idx) => {
            let typ = arena.get_core_type(*typ_idx).clone();
            validate_core_type_method_attribute_errors(&typ, arena)
        }
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_construct(_, None)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue => Ok(()),
    }
}

fn validate_payload_await_errors(
    payload: &Payload,
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    match payload {
        Payload::PStr(items) => validate_structure_await_errors(items, arena, async_context),
        Payload::PSig(items) => validate_signature_await_errors(items, arena, async_context),
        Payload::PTyp(_) => Ok(()),
        Payload::PPat(inner) => {
            let (_pat, guard) = &**inner;
            if let Some(guard_idx) = guard {
                validate_expression_idx_await_context(*guard_idx, arena, async_context, false)?;
            }
            Ok(())
        }
    }
}

fn validate_js_string_literal(s: &str, loc: LocIdx) -> PpxResult<()> {
    let bytes = js_string_source_bytes(s);
    let bytes = bytes.as_ref();
    let mut byte_offset = 0;
    let mut char_offset = 0;

    while byte_offset < bytes.len() {
        match bytes[byte_offset] {
            b'\\' => {
                (byte_offset, char_offset) =
                    validate_js_string_escape(bytes, loc, byte_offset + 1, char_offset + 1)?;
            }
            byte if byte < 0x80 => {
                byte_offset += 1;
                char_offset += 1;
            }
            _ => {
                let width = if bytes[byte_offset] & 0b1111_1000 == 0b1111_0000 {
                    4
                } else if bytes[byte_offset] & 0b1111_0000 == 0b1110_0000 {
                    3
                } else if bytes[byte_offset] & 0b1110_0000 == 0b1100_0000 {
                    2
                } else {
                    return Err(PpxError::at_loc(
                        loc,
                        format!("Offset: {char_offset}, Invalid code point"),
                    ));
                };
                if byte_offset + width > bytes.len()
                    || std::str::from_utf8(&bytes[byte_offset..byte_offset + width]).is_err()
                {
                    return Err(PpxError::at_loc(
                        loc,
                        format!("Offset: {char_offset}, Invalid code point"),
                    ));
                }
                byte_offset += width;
                char_offset += 1;
            }
        }
    }

    Ok(())
}

fn js_string_source_bytes(s: &str) -> Cow<'_, [u8]> {
    // Source strings use the compiler's Latin-1 view: one Rust char stores one
    // original source byte, matching the byte string OCaml validates.
    if s.is_ascii() {
        Cow::Borrowed(s.as_bytes())
    } else {
        Cow::Owned(s.chars().map(|c| c as u8).collect())
    }
}

fn validate_js_string_escape(
    bytes: &[u8],
    loc: LocIdx,
    byte_offset: usize,
    char_offset: usize,
) -> PpxResult<(usize, usize)> {
    if byte_offset >= bytes.len() {
        return Err(PpxError::at_loc(
            loc,
            format!("Offset: {char_offset}, \\ ended unexpectedly"),
        ));
    }

    match bytes[byte_offset] {
        b'\\' | b'b' | b't' | b'n' | b'v' | b'f' | b'r' | b'0' | b'$' => {
            Ok((byte_offset + 1, char_offset + 1))
        }
        b'u' => {
            if byte_offset + 1 >= bytes.len() {
                return Err(PpxError::at_loc(
                    loc,
                    format!("Offset: {char_offset}, Invalid \\u escape"),
                ));
            }
            if bytes[byte_offset + 1] == b'{' {
                validate_js_string_codepoint_escape(bytes, loc, byte_offset + 2, char_offset + 2)
            } else {
                validate_js_string_fixed_escape_digits(
                    bytes,
                    loc,
                    byte_offset + 1,
                    char_offset + 1,
                    4,
                    "Invalid \\u escape",
                )?;
                Ok((byte_offset + 5, char_offset + 5))
            }
        }
        b'x' => {
            validate_js_string_fixed_escape_digits(
                bytes,
                loc,
                byte_offset + 1,
                char_offset + 1,
                2,
                "Invalid \\x escape",
            )?;
            Ok((byte_offset + 3, char_offset + 3))
        }
        _ => Ok((byte_offset + 1, char_offset + 1)),
    }
}

fn validate_js_string_fixed_escape_digits(
    bytes: &[u8],
    loc: LocIdx,
    byte_offset: usize,
    char_offset: usize,
    digits: usize,
    message: &str,
) -> PpxResult<()> {
    for i in 0..digits {
        if byte_offset + i >= bytes.len() || !bytes[byte_offset + i].is_ascii_hexdigit() {
            return Err(PpxError::at_loc(
                loc,
                format!("Offset: {char_offset}, {message}"),
            ));
        }
    }
    Ok(())
}

fn validate_js_string_codepoint_escape(
    bytes: &[u8],
    loc: LocIdx,
    mut byte_offset: usize,
    char_offset: usize,
) -> PpxResult<(usize, usize)> {
    let mut value: u32 = 0;

    while byte_offset < bytes.len() && bytes[byte_offset].is_ascii_hexdigit() {
        let digit = (bytes[byte_offset] as char).to_digit(16).unwrap_or(16);
        if value > 0x10FFFF {
            return Err(PpxError::at_loc(
                loc,
                format!("Offset: {char_offset}, Invalid \\u{{…}} codepoint escape sequence"),
            ));
        }
        value = value.saturating_mul(16).saturating_add(digit);
        byte_offset += 1;
    }

    if byte_offset < bytes.len()
        && bytes[byte_offset] == b'}'
        && value <= 0x10FFFF
        && !(0xD800..0xE000).contains(&value)
    {
        let next_offset = byte_offset + 1;
        Ok((next_offset, next_offset))
    } else {
        Err(PpxError::at_loc(
            loc,
            format!("Offset: {char_offset}, Invalid \\u{{…}} codepoint escape sequence"),
        ))
    }
}

fn attributes_have_template_marker(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _)| {
        let name = arena.get_string(attr_name.txt);
        name == "res.template" || name == "res.taggedTemplate"
    })
}

fn validate_attributes_js_string_errors(
    attrs: &[Attribute],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for attr in attrs {
        validate_payload_js_string_errors(&attr.1, arena)?;
    }
    Ok(())
}

fn validate_payload_js_string_errors(payload: &Payload, arena: &mut ParseArena) -> PpxResult<()> {
    match payload {
        Payload::PStr(items) => validate_structure_js_string_errors(items, arena),
        Payload::PSig(items) => validate_signature_js_string_errors(items, arena),
        Payload::PTyp(typ) => validate_core_type_js_string_errors(*typ, arena),
        Payload::PPat(inner) => {
            let (pat, guard) = &**inner;
            validate_pattern_js_string_errors(*pat, arena)?;
            if let Some(guard) = guard {
                validate_expression_idx_js_string_errors(*guard, arena)?;
            }
            Ok(())
        }
    }
}

fn validate_core_type_js_string_errors(
    typ_idx: CoreTypeIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let typ = arena.get_core_type(typ_idx).clone();
    validate_attributes_js_string_errors(&typ.ptyp_attributes, arena)?;
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, _) = &**inner;
            validate_attributes_js_string_errors(&arg.attrs, arena)?;
            validate_core_type_js_string_errors(arg.typ, arena)?;
            validate_core_type_js_string_errors(*ret, arena)
        }
        CoreTypeDesc::Ptyp_tuple(items) => {
            for item in items.iter() {
                validate_core_type_js_string_errors(*item, arena)?;
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (_, args) = &**inner;
            for arg in args {
                validate_core_type_js_string_errors(*arg, arena)?;
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            let (fields, _) = &**inner;
            for field in fields {
                match field {
                    ObjectField::Otag(_, attrs, typ) => {
                        validate_attributes_js_string_errors(attrs, arena)?;
                        validate_core_type_js_string_errors(*typ, arena)?;
                    }
                    ObjectField::Oinherit(typ) => {
                        validate_core_type_js_string_errors(*typ, arena)?;
                    }
                }
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (typ, _) = &**inner;
            validate_core_type_js_string_errors(*typ, arena)
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (fields, _, _) = &**inner;
            for field in fields {
                match field {
                    RowField::Rtag(_, attrs, _, args) => {
                        validate_attributes_js_string_errors(attrs, arena)?;
                        for arg in args {
                            validate_core_type_js_string_errors(*arg, arena)?;
                        }
                    }
                    RowField::Rinherit(typ) => {
                        validate_core_type_js_string_errors(*typ, arena)?;
                    }
                }
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (_, typ) = &**inner;
            validate_core_type_js_string_errors(*typ, arena)
        }
        CoreTypeDesc::Ptyp_package(inner) => {
            let (_, constraints) = &**inner;
            for (_, typ) in constraints {
                validate_core_type_js_string_errors(*typ, arena)?;
            }
            Ok(())
        }
        CoreTypeDesc::Ptyp_extension(extension) => {
            validate_payload_js_string_errors(&extension.1, arena)
        }
        CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => Ok(()),
    }
}

fn validate_pattern_js_string_errors(pat_idx: PatIdx, arena: &mut ParseArena) -> PpxResult<()> {
    let pat = arena.get_pat(pat_idx).clone();
    validate_attributes_js_string_errors(&pat.ppat_attributes, arena)?;
    match &*pat.ppat_desc {
        PatternDesc::Ppat_constant(constant) => {
            if let Constant::String(s, Some(delim)) = &**constant
                && delim == "js"
            {
                validate_js_string_literal(s, pat.ppat_loc)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_interval(inner) => {
            let (left, right) = &**inner;
            for constant in [left, right] {
                if let Constant::String(s, Some(delim)) = constant
                    && delim == "js"
                {
                    validate_js_string_literal(s, pat.ppat_loc)?;
                }
            }
            Ok(())
        }
        PatternDesc::Ppat_alias(inner, _)
        | PatternDesc::Ppat_exception(inner)
        | PatternDesc::Ppat_open(_, inner) => validate_pattern_js_string_errors(*inner, arena),
        PatternDesc::Ppat_tuple(items) | PatternDesc::Ppat_array(items) => {
            for item in items.iter() {
                validate_pattern_js_string_errors(*item, arena)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_construct(_, arg) => {
            if let Some(arg) = arg {
                validate_pattern_js_string_errors(*arg, arena)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_variant(inner) => {
            let (_, arg) = &**inner;
            if let Some(arg) = arg {
                validate_pattern_js_string_errors(*arg, arena)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_record(inner) => {
            let (fields, _) = &**inner;
            for field in fields {
                validate_pattern_js_string_errors(field.pat, arena)?;
            }
            Ok(())
        }
        PatternDesc::Ppat_or(left, right) => {
            validate_pattern_js_string_errors(*left, arena)?;
            validate_pattern_js_string_errors(*right, arena)
        }
        PatternDesc::Ppat_constraint(inner) => {
            let (pat, typ) = &**inner;
            validate_pattern_js_string_errors(*pat, arena)?;
            validate_core_type_js_string_errors(*typ, arena)
        }
        PatternDesc::Ppat_extension(extension) => {
            validate_payload_js_string_errors(&extension.1, arena)
        }
        PatternDesc::Ppat_any
        | PatternDesc::Ppat_var(_)
        | PatternDesc::Ppat_type(_)
        | PatternDesc::Ppat_unpack(_) => Ok(()),
    }
}

fn validate_value_bindings_js_string_errors(
    bindings: &[ValueBinding],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for vb in bindings {
        validate_pattern_js_string_errors(vb.pvb_pat, arena)?;
        validate_expression_idx_js_string_errors(vb.pvb_expr, arena)?;
        validate_attributes_js_string_errors(&vb.pvb_attributes, arena)?;
    }
    Ok(())
}

fn validate_cases_js_string_errors(cases: &[Case], arena: &mut ParseArena) -> PpxResult<()> {
    for case in cases {
        validate_pattern_js_string_errors(case.pc_lhs, arena)?;
        if let Some(guard) = case.pc_guard {
            validate_expression_idx_js_string_errors(guard, arena)?;
        }
        validate_expression_idx_js_string_errors(case.pc_rhs, arena)?;
    }
    Ok(())
}

fn validate_expression_idx_js_string_errors(
    expr_idx: ExprIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let expr = arena.get_expr(expr_idx).clone();
    validate_expression_js_string_errors(&expr, arena)
}

fn validate_jsx_element_js_string_errors(
    jsx: &JsxElement,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match jsx {
        JsxElement::Fragment(fragment) => {
            for child in &fragment.children {
                validate_expression_idx_js_string_errors(*child, arena)?;
            }
        }
        JsxElement::Unary(elem) => validate_jsx_props_js_string_errors(&elem.props, arena)?,
        JsxElement::Container(elem) => {
            validate_jsx_props_js_string_errors(&elem.props, arena)?;
            for child in &elem.children {
                validate_expression_idx_js_string_errors(*child, arena)?;
            }
        }
    }
    Ok(())
}

fn validate_jsx_props_js_string_errors(props: &[JsxProp], arena: &mut ParseArena) -> PpxResult<()> {
    for prop in props {
        match prop {
            JsxProp::Value { value, .. } => {
                validate_expression_idx_js_string_errors(*value, arena)?;
            }
            JsxProp::Spreading { expr, .. } => {
                validate_expression_idx_js_string_errors(*expr, arena)?;
            }
            JsxProp::Punning { .. } => {}
        }
    }
    Ok(())
}

fn validate_expression_js_string_errors(
    expr: &Expression,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    validate_attributes_js_string_errors(&expr.pexp_attributes, arena)?;
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => {
            if let Constant::String(s, Some(delim)) = &**constant
                && delim == "js"
                && !attributes_have_template_marker(&expr.pexp_attributes, arena)
            {
                validate_js_string_literal(s, expr.pexp_loc)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (_, bindings, body) = &**inner;
            validate_value_bindings_js_string_errors(bindings, arena)?;
            validate_expression_idx_js_string_errors(*body, arena)
        }
        ExpressionDesc::Pexp_fun(inner) => {
            if let Some(default) = inner.default {
                validate_expression_idx_js_string_errors(default, arena)?;
            }
            validate_pattern_js_string_errors(inner.lhs, arena)?;
            validate_expression_idx_js_string_errors(inner.rhs, arena)
        }
        ExpressionDesc::Pexp_apply(inner) => {
            validate_expression_idx_js_string_errors(inner.funct, arena)?;
            for (_, arg) in &inner.args {
                validate_expression_idx_js_string_errors(*arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            validate_expression_idx_js_string_errors(*scrutinee, arena)?;
            validate_cases_js_string_errors(cases, arena)
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            for item in items.iter() {
                validate_expression_idx_js_string_errors(*item, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_construct(_, arg) => {
            if let Some(arg) = arg {
                validate_expression_idx_js_string_errors(*arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_variant(inner) => {
            let (_, arg) = &**inner;
            if let Some(arg) = arg {
                validate_expression_idx_js_string_errors(*arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, spread) = &**inner;
            if let Some(spread) = spread {
                validate_expression_idx_js_string_errors(*spread, arena)?;
            }
            for field in fields {
                validate_expression_idx_js_string_errors(field.expr, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_field(target, _)
        | ExpressionDesc::Pexp_assert(target)
        | ExpressionDesc::Pexp_await(target)
        | ExpressionDesc::Pexp_comptime_compile_error(target)
        | ExpressionDesc::Pexp_comptime_build_variant(target)
        | ExpressionDesc::Pexp_comptime_variant_case(target)
        | ExpressionDesc::Pexp_comptime_build_record(target)
        | ExpressionDesc::Pexp_comptime_record_field(target) => {
            validate_expression_idx_js_string_errors(*target, arena)
        }
        ExpressionDesc::Pexp_send(inner) => {
            let (target, _) = &**inner;
            validate_expression_idx_js_string_errors(*target, arena)
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (target, _, value) = &**inner;
            validate_expression_idx_js_string_errors(*target, arena)?;
            validate_expression_idx_js_string_errors(*value, arena)
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (cond, then_expr, else_expr) = &**inner;
            validate_expression_idx_js_string_errors(*cond, arena)?;
            validate_expression_idx_js_string_errors(*then_expr, arena)?;
            if let Some(else_expr) = else_expr {
                validate_expression_idx_js_string_errors(*else_expr, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_sequence(left, right) | ExpressionDesc::Pexp_while(left, right) => {
            validate_expression_idx_js_string_errors(*left, arena)?;
            validate_expression_idx_js_string_errors(*right, arena)
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (pat, start, finish, _, body) = &**inner;
            validate_pattern_js_string_errors(*pat, arena)?;
            validate_expression_idx_js_string_errors(*start, arena)?;
            validate_expression_idx_js_string_errors(*finish, arena)?;
            validate_expression_idx_js_string_errors(*body, arena)
        }
        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            let (pat, iterable, body) = &**inner;
            validate_pattern_js_string_errors(*pat, arena)?;
            validate_expression_idx_js_string_errors(*iterable, arena)?;
            validate_expression_idx_js_string_errors(*body, arena)
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (inner_expr, typ) = &**inner;
            validate_expression_idx_js_string_errors(*inner_expr, arena)?;
            validate_core_type_js_string_errors(*typ, arena)
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (inner_expr, typ1, typ2) = &**inner;
            validate_expression_idx_js_string_errors(*inner_expr, arena)?;
            if let Some(typ1) = typ1 {
                validate_core_type_js_string_errors(*typ1, arena)?;
            }
            validate_core_type_js_string_errors(*typ2, arena)
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_, mod_expr, body) = &**inner;
            let mod_expr = arena.get_mod_expr(*mod_expr).clone();
            validate_module_expr_js_string_errors(&mod_expr, arena)?;
            validate_expression_idx_js_string_errors(*body, arena)
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (ext, body) = &**inner;
            validate_attributes_js_string_errors(&ext.pext_attributes, arena)?;
            validate_expression_idx_js_string_errors(*body, arena)
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (_, body) = &**inner;
            validate_expression_idx_js_string_errors(*body, arena)
        }
        ExpressionDesc::Pexp_pack(mod_expr) => {
            let mod_expr = arena.get_mod_expr(*mod_expr).clone();
            validate_module_expr_js_string_errors(&mod_expr, arena)
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (_, _, body) = &**inner;
            validate_expression_idx_js_string_errors(*body, arena)
        }
        ExpressionDesc::Pexp_extension(extension) => {
            validate_payload_js_string_errors(&extension.1, arena)
        }
        ExpressionDesc::Pexp_jsx_element(jsx) => validate_jsx_element_js_string_errors(jsx, arena),
        ExpressionDesc::Pexp_inline_for(inner) => {
            let (pat, collection, body) = &**inner;
            validate_pattern_js_string_errors(*pat, arena)?;
            validate_expression_idx_js_string_errors(*collection, arena)?;
            validate_expression_idx_js_string_errors(*body, arena)
        }
        ExpressionDesc::Pexp_comptime_typeinfo(typ)
        | ExpressionDesc::Pexp_comptime_typename(typ) => {
            validate_core_type_js_string_errors(*typ, arena)
        }
        ExpressionDesc::Pexp_comptime_field(inner) => {
            let (value, field) = &**inner;
            validate_expression_idx_js_string_errors(*value, arena)?;
            validate_expression_idx_js_string_errors(*field, arena)
        }
        ExpressionDesc::Pexp_comptime_record(inner) => {
            let (typ, fields) = &**inner;
            validate_core_type_js_string_errors(*typ, arena)?;
            validate_expression_idx_js_string_errors(*fields, arena)
        }
        ExpressionDesc::Pexp_comptime_variant(inner) => {
            let (typ, name, payload) = &**inner;
            validate_core_type_js_string_errors(*typ, arena)?;
            validate_expression_idx_js_string_errors(*name, arena)?;
            if let Some(payload) = payload {
                validate_expression_idx_js_string_errors(*payload, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue => Ok(()),
    }
}

fn validate_module_expr_js_string_errors(
    mod_expr: &ModuleExpr,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    validate_attributes_js_string_errors(&mod_expr.pmod_attributes, arena)?;
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => validate_structure_js_string_errors(items, arena),
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, param_type, body) = &**inner;
            if let Some(param_type) = param_type {
                let param_type = arena.get_mod_type(*param_type).clone();
                validate_module_type_js_string_errors(&param_type, arena)?;
            }
            let body = arena.get_mod_expr(*body).clone();
            validate_module_expr_js_string_errors(&body, arena)
        }
        ModuleExprDesc::Pmod_apply(left, right) => {
            let left = arena.get_mod_expr(*left).clone();
            validate_module_expr_js_string_errors(&left, arena)?;
            let right = arena.get_mod_expr(*right).clone();
            validate_module_expr_js_string_errors(&right, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, mod_type) => {
            let inner = arena.get_mod_expr(*inner).clone();
            validate_module_expr_js_string_errors(&inner, arena)?;
            let mod_type = arena.get_mod_type(*mod_type).clone();
            validate_module_type_js_string_errors(&mod_type, arena)
        }
        ModuleExprDesc::Pmod_unpack(expr) => validate_expression_idx_js_string_errors(*expr, arena),
        ModuleExprDesc::Pmod_extension(extension) => {
            validate_payload_js_string_errors(&extension.1, arena)
        }
        ModuleExprDesc::Pmod_ident(_) => Ok(()),
    }
}

fn validate_module_type_js_string_errors(
    mod_type: &ModuleType,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    validate_attributes_js_string_errors(&mod_type.pmty_attributes, arena)?;
    match &*mod_type.pmty_desc {
        ModuleTypeDesc::Pmty_signature(items) => validate_signature_js_string_errors(items, arena),
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_, param_type, result_type) = &**inner;
            if let Some(param_type) = param_type {
                let param_type = arena.get_mod_type(*param_type).clone();
                validate_module_type_js_string_errors(&param_type, arena)?;
            }
            let result_type = arena.get_mod_type(*result_type).clone();
            validate_module_type_js_string_errors(&result_type, arena)
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (mod_type, constraints) = &**inner;
            let mod_type = arena.get_mod_type(*mod_type).clone();
            validate_module_type_js_string_errors(&mod_type, arena)?;
            for constraint in constraints {
                match constraint {
                    WithConstraint::Pwith_type(_, tdcl) => {
                        validate_type_declaration_js_string_errors(tdcl, arena)?;
                    }
                    WithConstraint::Pwith_typesubst(_, tdcl) => {
                        validate_type_declaration_js_string_errors(tdcl, arena)?;
                    }
                    WithConstraint::Pwith_module(_, _) | WithConstraint::Pwith_modsubst(_, _) => {}
                }
            }
            Ok(())
        }
        ModuleTypeDesc::Pmty_typeof(mod_expr) => {
            let mod_expr = arena.get_mod_expr(*mod_expr).clone();
            validate_module_expr_js_string_errors(&mod_expr, arena)
        }
        ModuleTypeDesc::Pmty_extension(extension) => {
            validate_payload_js_string_errors(&extension.1, arena)
        }
        ModuleTypeDesc::Pmty_ident(_) | ModuleTypeDesc::Pmty_alias(_) => Ok(()),
    }
}

fn validate_type_declaration_js_string_errors(
    tdcl: &TypeDeclaration,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    validate_attributes_js_string_errors(&tdcl.ptype_attributes, arena)?;
    for (param, _) in &tdcl.ptype_params {
        validate_core_type_js_string_errors(*param, arena)?;
    }
    match &tdcl.ptype_kind {
        TypeKind::Ptype_record(fields) => {
            for field in fields {
                validate_attributes_js_string_errors(&field.pld_attributes, arena)?;
                validate_core_type_js_string_errors(field.pld_type, arena)?;
            }
        }
        TypeKind::Ptype_variant(ctors) => {
            for ctor in ctors {
                validate_attributes_js_string_errors(&ctor.pcd_attributes, arena)?;
                match &ctor.pcd_args {
                    ConstructorArguments::Pcstr_tuple(args) => {
                        for arg in args {
                            validate_core_type_js_string_errors(*arg, arena)?;
                        }
                    }
                    ConstructorArguments::Pcstr_record(fields) => {
                        for field in fields {
                            validate_attributes_js_string_errors(&field.pld_attributes, arena)?;
                            validate_core_type_js_string_errors(field.pld_type, arena)?;
                        }
                    }
                }
                if let Some(result) = ctor.pcd_res {
                    validate_core_type_js_string_errors(result, arena)?;
                }
            }
        }
        TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
    }
    if let Some(manifest) = tdcl.ptype_manifest {
        validate_core_type_js_string_errors(manifest, arena)?;
    }
    Ok(())
}

fn validate_structure_js_string_errors(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(inner) => {
                let (expr, attrs) = &**inner;
                validate_expression_idx_js_string_errors(*expr, arena)?;
                validate_attributes_js_string_errors(attrs, arena)?;
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (_, bindings) = &**inner;
                validate_value_bindings_js_string_errors(bindings, arena)?;
            }
            StructureItemDesc::Pstr_primitive(vd) => {
                validate_attributes_js_string_errors(&vd.pval_attributes, arena)?;
                validate_core_type_js_string_errors(vd.pval_type, arena)?;
            }
            StructureItemDesc::Pstr_type(inner) => {
                let (_, tdcls) = &**inner;
                for tdcl in tdcls {
                    validate_type_declaration_js_string_errors(tdcl, arena)?;
                }
            }
            StructureItemDesc::Pstr_typext(te) => {
                validate_attributes_js_string_errors(&te.ptyext_attributes, arena)?;
                for ctor in &te.ptyext_constructors {
                    validate_attributes_js_string_errors(&ctor.pext_attributes, arena)?;
                }
            }
            StructureItemDesc::Pstr_exception(ext) => {
                validate_attributes_js_string_errors(&ext.pext_attributes, arena)?;
            }
            StructureItemDesc::Pstr_module(mb) => {
                validate_attributes_js_string_errors(&mb.pmb_attributes, arena)?;
                let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                validate_module_expr_js_string_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                for mb in mbs.iter() {
                    validate_attributes_js_string_errors(&mb.pmb_attributes, arena)?;
                    let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                    validate_module_expr_js_string_errors(&mod_expr, arena)?;
                }
            }
            StructureItemDesc::Pstr_modtype(mtd) => {
                validate_attributes_js_string_errors(&mtd.pmtd_attributes, arena)?;
                if let Some(mod_type) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type).clone();
                    validate_module_type_js_string_errors(&mod_type, arena)?;
                }
            }
            StructureItemDesc::Pstr_include(incl) => {
                validate_attributes_js_string_errors(&incl.pincl_attributes, arena)?;
                let mod_expr = arena.get_mod_expr(incl.pincl_mod).clone();
                validate_module_expr_js_string_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_open(od) => {
                validate_attributes_js_string_errors(&od.popen_attributes, arena)?;
            }
            StructureItemDesc::Pstr_attribute(attr) => {
                validate_payload_js_string_errors(&attr.1, arena)?;
            }
            StructureItemDesc::Pstr_extension(inner) => {
                let (extension, attrs) = &**inner;
                validate_payload_js_string_errors(&extension.1, arena)?;
                validate_attributes_js_string_errors(attrs, arena)?;
            }
        }
    }
    Ok(())
}

fn validate_signature_js_string_errors(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in signature {
        match &*item.psig_desc {
            SignatureItemDesc::Psig_value(vd) => {
                validate_attributes_js_string_errors(&vd.pval_attributes, arena)?;
                validate_core_type_js_string_errors(vd.pval_type, arena)?;
            }
            SignatureItemDesc::Psig_type(inner) => {
                let (_, tdcls) = &**inner;
                for tdcl in tdcls {
                    validate_type_declaration_js_string_errors(tdcl, arena)?;
                }
            }
            SignatureItemDesc::Psig_typext(te) => {
                validate_attributes_js_string_errors(&te.ptyext_attributes, arena)?;
                for ctor in &te.ptyext_constructors {
                    validate_attributes_js_string_errors(&ctor.pext_attributes, arena)?;
                }
            }
            SignatureItemDesc::Psig_exception(ext) => {
                validate_attributes_js_string_errors(&ext.pext_attributes, arena)?;
            }
            SignatureItemDesc::Psig_module(md) => {
                validate_attributes_js_string_errors(&md.pmd_attributes, arena)?;
                let mod_type = arena.get_mod_type(md.pmd_type).clone();
                validate_module_type_js_string_errors(&mod_type, arena)?;
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                for md in mds.iter() {
                    validate_attributes_js_string_errors(&md.pmd_attributes, arena)?;
                    let mod_type = arena.get_mod_type(md.pmd_type).clone();
                    validate_module_type_js_string_errors(&mod_type, arena)?;
                }
            }
            SignatureItemDesc::Psig_modtype(mtd) => {
                validate_attributes_js_string_errors(&mtd.pmtd_attributes, arena)?;
                if let Some(mod_type) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type).clone();
                    validate_module_type_js_string_errors(&mod_type, arena)?;
                }
            }
            SignatureItemDesc::Psig_include(incl) => {
                validate_attributes_js_string_errors(&incl.pincl_attributes, arena)?;
                let mod_type = arena.get_mod_type(incl.pincl_mod).clone();
                validate_module_type_js_string_errors(&mod_type, arena)?;
            }
            SignatureItemDesc::Psig_open(od) => {
                validate_attributes_js_string_errors(&od.popen_attributes, arena)?;
            }
            SignatureItemDesc::Psig_attribute(attr) => {
                validate_payload_js_string_errors(&attr.1, arena)?;
            }
            SignatureItemDesc::Psig_extension(inner) => {
                let (extension, attrs) = &**inner;
                validate_payload_js_string_errors(&extension.1, arena)?;
                validate_attributes_js_string_errors(attrs, arena)?;
            }
        }
    }
    Ok(())
}

fn validate_structure_await_errors(
    structure: &[StructureItem],
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(inner) => {
                let (expr, attrs) = &**inner;
                validate_expression_idx_await_context(*expr, arena, async_context, false)?;
                for attr in attrs.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (_rec_flag, bindings) = &**inner;
                validate_value_bindings_await_context(bindings, arena, async_context)?;
            }
            StructureItemDesc::Pstr_primitive(vd) => {
                for attr in vd.pval_attributes.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            StructureItemDesc::Pstr_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                for tdcl in tdcls {
                    for attr in tdcl.ptype_attributes.iter() {
                        validate_payload_await_errors(&attr.1, arena, async_context)?;
                    }
                }
            }
            StructureItemDesc::Pstr_typext(te) => {
                for attr in te.ptyext_attributes.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            StructureItemDesc::Pstr_exception(ext) => {
                for attr in ext.pext_attributes.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            StructureItemDesc::Pstr_module(mb) => {
                let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                validate_module_expr_await_context(&mod_expr, arena, async_context)?;
                for attr in mb.pmb_attributes.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                for mb in mbs.iter() {
                    let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                    validate_module_expr_await_context(&mod_expr, arena, async_context)?;
                    for attr in mb.pmb_attributes.iter() {
                        validate_payload_await_errors(&attr.1, arena, async_context)?;
                    }
                }
            }
            StructureItemDesc::Pstr_modtype(mtd) => {
                if let Some(mod_type_idx) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type_idx).clone();
                    validate_module_type_await_context(&mod_type, arena, async_context)?;
                }
                for attr in mtd.pmtd_attributes.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            StructureItemDesc::Pstr_include(incl) => {
                let mod_expr = arena.get_mod_expr(incl.pincl_mod).clone();
                validate_module_expr_await_context(&mod_expr, arena, async_context)?;
                for attr in incl.pincl_attributes.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            StructureItemDesc::Pstr_open(od) => {
                for attr in od.popen_attributes.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            StructureItemDesc::Pstr_attribute(attr) => {
                validate_payload_await_errors(&attr.1, arena, async_context)?;
            }
            StructureItemDesc::Pstr_extension(inner) => {
                let (extension, attrs) = &**inner;
                validate_payload_await_errors(&extension.1, arena, async_context)?;
                for attr in attrs.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
        }
    }

    Ok(())
}

fn validate_signature_await_errors(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    for item in signature {
        match &*item.psig_desc {
            SignatureItemDesc::Psig_module(md) => {
                let mod_type = arena.get_mod_type(md.pmd_type).clone();
                validate_module_type_await_context(&mod_type, arena, async_context)?;
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                for md in mds.iter() {
                    let mod_type = arena.get_mod_type(md.pmd_type).clone();
                    validate_module_type_await_context(&mod_type, arena, async_context)?;
                }
            }
            SignatureItemDesc::Psig_modtype(mtd) => {
                if let Some(mod_type_idx) = mtd.pmtd_type {
                    let mod_type = arena.get_mod_type(mod_type_idx).clone();
                    validate_module_type_await_context(&mod_type, arena, async_context)?;
                }
            }
            SignatureItemDesc::Psig_include(incl) => {
                let mod_type = arena.get_mod_type(incl.pincl_mod).clone();
                validate_module_type_await_context(&mod_type, arena, async_context)?;
            }
            SignatureItemDesc::Psig_attribute(attr) => {
                validate_payload_await_errors(&attr.1, arena, async_context)?;
            }
            SignatureItemDesc::Psig_extension(inner) => {
                let (extension, attrs) = &**inner;
                validate_payload_await_errors(&extension.1, arena, async_context)?;
                for attr in attrs.iter() {
                    validate_payload_await_errors(&attr.1, arena, async_context)?;
                }
            }
            SignatureItemDesc::Psig_value(_)
            | SignatureItemDesc::Psig_type(_)
            | SignatureItemDesc::Psig_typext(_)
            | SignatureItemDesc::Psig_exception(_)
            | SignatureItemDesc::Psig_open(_) => {}
        }
    }

    Ok(())
}

fn validate_module_expr_await_context(
    mod_expr: &current::ModuleExpr,
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => {
            validate_structure_await_errors(items, arena, async_context)
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_name, param_type, body) = &**inner;
            if let Some(param_type_idx) = *param_type {
                let mod_type = arena.get_mod_type(param_type_idx).clone();
                validate_module_type_await_context(&mod_type, arena, async_context)?;
            }
            let body_expr = arena.get_mod_expr(*body).clone();
            validate_module_expr_await_context(&body_expr, arena, async_context)
        }
        ModuleExprDesc::Pmod_apply(left, right) => {
            let left_expr = arena.get_mod_expr(*left).clone();
            validate_module_expr_await_context(&left_expr, arena, async_context)?;
            let right_expr = arena.get_mod_expr(*right).clone();
            validate_module_expr_await_context(&right_expr, arena, async_context)
        }
        ModuleExprDesc::Pmod_constraint(inner, mod_type_idx) => {
            let inner_expr = arena.get_mod_expr(*inner).clone();
            validate_module_expr_await_context(&inner_expr, arena, async_context)?;
            let mod_type = arena.get_mod_type(*mod_type_idx).clone();
            validate_module_type_await_context(&mod_type, arena, async_context)
        }
        ModuleExprDesc::Pmod_unpack(expr_idx) => {
            validate_expression_idx_await_context(*expr_idx, arena, async_context, false)
        }
        ModuleExprDesc::Pmod_extension(extension) => {
            validate_payload_await_errors(&extension.1, arena, async_context)
        }
        ModuleExprDesc::Pmod_ident(_) => Ok(()),
    }
}

fn validate_module_type_await_context(
    mod_type: &ModuleType,
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    match &*mod_type.pmty_desc {
        ModuleTypeDesc::Pmty_signature(items) => {
            validate_signature_await_errors(items, arena, async_context)
        }
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_name, param_type, result_type) = &**inner;
            if let Some(param_type_idx) = *param_type {
                let param_type = arena.get_mod_type(param_type_idx).clone();
                validate_module_type_await_context(&param_type, arena, async_context)?;
            }
            let result_type = arena.get_mod_type(*result_type).clone();
            validate_module_type_await_context(&result_type, arena, async_context)
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (mod_type_idx, _constraints) = &**inner;
            let inner_type = arena.get_mod_type(*mod_type_idx).clone();
            validate_module_type_await_context(&inner_type, arena, async_context)
        }
        ModuleTypeDesc::Pmty_typeof(mod_expr_idx) => {
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_await_context(&mod_expr, arena, async_context)
        }
        ModuleTypeDesc::Pmty_extension(extension) => {
            validate_payload_await_errors(&extension.1, arena, async_context)
        }
        ModuleTypeDesc::Pmty_ident(_) | ModuleTypeDesc::Pmty_alias(_) => Ok(()),
    }
}

fn validate_value_bindings_await_context(
    bindings: &[ValueBinding],
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    for vb in bindings {
        validate_module_record_pattern_binding_error(vb, arena)?;
        validate_expression_idx_await_context(vb.pvb_expr, arena, async_context, false)?;
        for attr in vb.pvb_attributes.iter() {
            validate_payload_await_errors(&attr.1, arena, async_context)?;
        }
    }
    Ok(())
}

fn validate_module_record_pattern_binding_error(
    vb: &ValueBinding,
    arena: &ParseArena,
) -> PpxResult<()> {
    let pat = arena.get_pat(vb.pvb_pat);
    let expr = arena.get_expr(vb.pvb_expr);

    let (PatternDesc::Ppat_record(record_inner), ExpressionDesc::Pexp_pack(mod_expr_idx)) =
        (&*pat.ppat_desc, &*expr.pexp_desc)
    else {
        return Ok(());
    };

    let mod_expr = arena.get_mod_expr(*mod_expr_idx);
    if !matches!(&*mod_expr.pmod_desc, ModuleExprDesc::Pmod_ident(_)) {
        return Ok(());
    }

    let (lid_pats, _) = &**record_inner;
    for field in lid_pats {
        if !matches!(arena.get_longident(field.lid.txt), Longident::Lident(_)) {
            return Err(PpxError::at_loc(
                field.lid.loc,
                "Not supported pattern match on modules",
            ));
        }
    }

    Ok(())
}

fn validate_expression_idx_await_context(
    expr_idx: ExprIdx,
    arena: &mut ParseArena,
    async_context: bool,
    in_function_def: bool,
) -> PpxResult<()> {
    let expr = arena.get_expr(expr_idx).clone();
    validate_expression_await_context(&expr, arena, async_context, in_function_def)
}

fn validate_cases_await_context(
    cases: &[Case],
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    for case in cases {
        if let Some(guard) = case.pc_guard {
            validate_expression_idx_await_context(guard, arena, async_context, false)?;
        }
        validate_expression_idx_await_context(case.pc_rhs, arena, async_context, false)?;
    }
    Ok(())
}

fn letmodule_expr_has_await_payload(mod_expr: &current::ModuleExpr, arena: &ParseArena) -> bool {
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_ident(_) => has_await_attribute(&mod_expr.pmod_attributes, arena),
        ModuleExprDesc::Pmod_constraint(inner_mod_idx, _mty_idx) => {
            let inner_mod = arena.get_mod_expr(*inner_mod_idx);
            matches!(&*inner_mod.pmod_desc, ModuleExprDesc::Pmod_ident(_))
                && (has_await_attribute(&inner_mod.pmod_attributes, arena)
                    || has_await_attribute(&mod_expr.pmod_attributes, arena))
        }
        _ => false,
    }
}

fn validate_jsx_element_await_context(
    jsx: &JsxElement,
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    match jsx {
        JsxElement::Fragment(fragment) => {
            for child in &fragment.children {
                validate_expression_idx_await_context(*child, arena, async_context, false)?;
            }
        }
        JsxElement::Unary(elem) => {
            validate_jsx_props_await_context(&elem.props, arena, async_context)?;
        }
        JsxElement::Container(elem) => {
            validate_jsx_props_await_context(&elem.props, arena, async_context)?;
            for child in &elem.children {
                validate_expression_idx_await_context(*child, arena, async_context, false)?;
            }
        }
    }
    Ok(())
}

fn validate_jsx_props_await_context(
    props: &[JsxProp],
    arena: &mut ParseArena,
    async_context: bool,
) -> PpxResult<()> {
    for prop in props {
        match prop {
            JsxProp::Value { value, .. } => {
                validate_expression_idx_await_context(*value, arena, async_context, false)?;
            }
            JsxProp::Spreading { expr, .. } => {
                validate_expression_idx_await_context(*expr, arena, async_context, false)?;
            }
            JsxProp::Punning { .. } => {}
        }
    }
    Ok(())
}

fn expression_is_lident(expr_idx: ExprIdx, expected: &str, arena: &ParseArena) -> bool {
    let expr = arena.get_expr(expr_idx);
    let ExpressionDesc::Pexp_ident(lid) = &*expr.pexp_desc else {
        return false;
    };
    let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
        return false;
    };
    arena.get_string(*name_idx) == expected
}

fn hash_hash_property_name(expr: &Expression, arena: &ParseArena) -> Option<(LocIdx, String)> {
    let ExpressionDesc::Pexp_apply(inner) = &*expr.pexp_desc else {
        return None;
    };
    let PexpApply { funct, args, .. } = &**inner;
    if args.len() != 2
        || !matches!(args[0].0, ArgLabel::Nolabel)
        || !matches!(args[1].0, ArgLabel::Nolabel)
        || !expression_is_lident(*funct, "##", arena)
    {
        return None;
    }

    let property = arena.get_expr(args[1].1);
    match &*property.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => {
            let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
                return None;
            };
            Some((lid.loc, arena.get_string(*name_idx).to_string()))
        }
        ExpressionDesc::Pexp_constant(c) => match &**c {
            Constant::String(name, None) => Some((property.pexp_loc, name.to_string())),
            _ => None,
        },
        _ => None,
    }
}

fn hash_hash_property_access(expr: &Expression, arena: &ParseArena) -> bool {
    hash_hash_property_name(expr, arena).is_some()
}

fn hash_set_apply_args<'a>(
    expr: &'a Expression,
    arena: &ParseArena,
) -> Option<&'a [(ArgLabel, ExprIdx)]> {
    let ExpressionDesc::Pexp_apply(inner) = &*expr.pexp_desc else {
        return None;
    };
    let PexpApply { funct, args, .. } = &**inner;
    if args.len() != 2
        || !matches!(args[0].0, ArgLabel::Nolabel)
        || !matches!(args[1].0, ArgLabel::Nolabel)
        || !expression_is_lident(*funct, "#=", arena)
    {
        return None;
    }
    Some(args)
}

fn invalid_property_name_error(name: &str, loc: LocIdx) -> Option<PpxError> {
    if name.contains('#') {
        Some(PpxError::at_loc(
            loc,
            format!("property name ({name}) can not contain speical character #"),
        ))
    } else {
        None
    }
}

fn hash_set_property_name_error(expr: &Expression, arena: &ParseArena) -> Option<PpxError> {
    let args = hash_set_apply_args(expr, arena)?;
    let lhs = arena.get_expr(args[0].1);
    match &*lhs.pexp_desc {
        ExpressionDesc::Pexp_send(inner) => {
            let (_obj, method) = &**inner;
            invalid_property_name_error(&method.txt, method.loc)
        }
        _ => {
            let (loc, name) = hash_hash_property_name(lhs, arena)?;
            invalid_property_name_error(&name, loc)
        }
    }
}

fn invalid_hash_set_assignment(expr: &Expression, arena: &ParseArena) -> bool {
    let Some(args) = hash_set_apply_args(expr, arena) else {
        return false;
    };
    let lhs = arena.get_expr(args[0].1);
    !matches!(&*lhs.pexp_desc, ExpressionDesc::Pexp_send(_))
        && !hash_hash_property_access(lhs, arena)
}

fn validate_expression_await_context(
    expr: &Expression,
    arena: &mut ParseArena,
    async_context: bool,
    in_function_def: bool,
) -> PpxResult<()> {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_let(inner) => {
            let (_rec_flag, bindings, body) = &**inner;
            validate_value_bindings_await_context(bindings, arena, async_context)?;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let child_async_context = if has_this_attr(&expr.pexp_attributes, arena) {
                false
            } else {
                (in_function_def && async_context) || inner.is_async
            };
            if let Some(default) = inner.default {
                validate_expression_idx_await_context(default, arena, child_async_context, false)?;
            }
            validate_expression_idx_await_context(inner.rhs, arena, child_async_context, true)?;
        }
        ExpressionDesc::Pexp_apply(inner) => {
            // Match ast_exp_apply.ml: #= only assigns to send expressions or ## property reads.
            if let Some(error) = hash_set_property_name_error(expr, arena) {
                return Err(error);
            }
            if invalid_hash_set_assignment(expr, arena) {
                return Err(PpxError::at_loc(expr.pexp_loc, "invalid #= assignment"));
            }
            validate_expression_idx_await_context(inner.funct, arena, async_context, false)?;
            for (_label, arg) in &inner.args {
                validate_expression_idx_await_context(*arg, arena, async_context, false)?;
            }
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            validate_expression_idx_await_context(*scrutinee, arena, async_context, false)?;
            validate_cases_await_context(cases, arena, async_context)?;
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            for item in items.iter() {
                validate_expression_idx_await_context(*item, arena, async_context, false)?;
            }
        }
        ExpressionDesc::Pexp_construct(_, Some(arg))
        | ExpressionDesc::Pexp_assert(arg)
        | ExpressionDesc::Pexp_comptime_compile_error(arg)
        | ExpressionDesc::Pexp_comptime_build_variant(arg)
        | ExpressionDesc::Pexp_comptime_variant_case(arg)
        | ExpressionDesc::Pexp_comptime_build_record(arg)
        | ExpressionDesc::Pexp_comptime_record_field(arg) => {
            validate_expression_idx_await_context(*arg, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, spread) = &**inner;
            if let Some(spread) = spread {
                validate_expression_idx_await_context(*spread, arena, async_context, false)?;
            }
            for field in fields {
                validate_expression_idx_await_context(field.expr, arena, async_context, false)?;
            }
        }
        ExpressionDesc::Pexp_variant(inner) => {
            let (_label, arg) = &**inner;
            if let Some(arg) = arg {
                validate_expression_idx_await_context(*arg, arena, async_context, false)?;
            }
        }
        ExpressionDesc::Pexp_field(target, _) => {
            validate_expression_idx_await_context(*target, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_send(inner) => {
            let (target, _method) = &**inner;
            validate_expression_idx_await_context(*target, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (target, _field, value) = &**inner;
            validate_expression_idx_await_context(*target, arena, async_context, false)?;
            validate_expression_idx_await_context(*value, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (cond, then_expr, else_expr) = &**inner;
            validate_expression_idx_await_context(*cond, arena, async_context, false)?;
            validate_expression_idx_await_context(*then_expr, arena, async_context, false)?;
            if let Some(else_expr) = else_expr {
                validate_expression_idx_await_context(*else_expr, arena, async_context, false)?;
            }
        }
        ExpressionDesc::Pexp_sequence(left, right) | ExpressionDesc::Pexp_while(left, right) => {
            validate_expression_idx_await_context(*left, arena, async_context, false)?;
            validate_expression_idx_await_context(*right, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (_pat, start, finish, _dir, body) = &**inner;
            validate_expression_idx_await_context(*start, arena, async_context, false)?;
            validate_expression_idx_await_context(*finish, arena, async_context, false)?;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_for_of(inner) => {
            let (_pat, iterable, body) = &**inner;
            validate_expression_idx_await_context(*iterable, arena, async_context, false)?;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_for_await_of(inner) => {
            let (_pat, iterable, body) = &**inner;
            validate_expression_idx_await_context(*iterable, arena, async_context, false)?;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
            if !async_context {
                return Err(PpxError::at_loc(
                    expr.pexp_loc,
                    AWAIT_NOT_ASYNC_CONTEXT_ERROR,
                ));
            }
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (inner_expr, _typ) = &**inner;
            validate_expression_idx_await_context(*inner_expr, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (inner_expr, _typ1, _typ2) = &**inner;
            validate_expression_idx_await_context(*inner_expr, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_name, mod_expr_idx, body) = &**inner;
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_await_context(&mod_expr, arena, async_context)?;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
            if letmodule_expr_has_await_payload(&mod_expr, arena) && !async_context {
                return Err(PpxError::at_loc(
                    expr.pexp_loc,
                    AWAIT_NOT_ASYNC_CONTEXT_ERROR,
                ));
            }
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (_ext, body) = &**inner;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (_name, body) = &**inner;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_pack(mod_expr_idx) => {
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            validate_module_expr_await_context(&mod_expr, arena, async_context)?;
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (_override, _mod_name, body) = &**inner;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_extension(extension) => {
            validate_payload_await_errors(&extension.1, arena, async_context)?;
        }
        ExpressionDesc::Pexp_await(inner) => {
            validate_expression_idx_await_context(*inner, arena, async_context, false)?;
            if !async_context {
                return Err(PpxError::at_loc(
                    expr.pexp_loc,
                    AWAIT_NOT_ASYNC_CONTEXT_ERROR,
                ));
            }
        }
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            validate_jsx_element_await_context(jsx, arena, async_context)?;
        }
        ExpressionDesc::Pexp_inline_for(inner) => {
            let (_pat, collection, body) = &**inner;
            validate_expression_idx_await_context(*collection, arena, async_context, false)?;
            validate_expression_idx_await_context(*body, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_comptime_field(inner) => {
            let (value, field) = &**inner;
            validate_expression_idx_await_context(*value, arena, async_context, false)?;
            validate_expression_idx_await_context(*field, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_comptime_record(inner) => {
            let (_typ, fields) = &**inner;
            validate_expression_idx_await_context(*fields, arena, async_context, false)?;
        }
        ExpressionDesc::Pexp_comptime_variant(inner) => {
            let (_typ, name, payload) = &**inner;
            validate_expression_idx_await_context(*name, arena, async_context, false)?;
            if let Some(payload) = payload {
                validate_expression_idx_await_context(*payload, arena, async_context, false)?;
            }
        }
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_construct(_, None)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue
        | ExpressionDesc::Pexp_comptime_typeinfo(_)
        | ExpressionDesc::Pexp_comptime_typename(_) => {}
    }

    Ok(())
}

fn validate_structure_this_errors(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> PpxResult<()> {
    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_value(inner) => {
                let (_rec_flag, bindings) = &**inner;
                for binding in bindings {
                    validate_expression_idx_this_errors(binding.pvb_expr, arena)?;
                }
            }
            StructureItemDesc::Pstr_eval(inner) => {
                let (expr, _) = &**inner;
                validate_expression_idx_this_errors(*expr, arena)?;
            }
            StructureItemDesc::Pstr_module(mb) => {
                let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                validate_module_expr_this_errors(&mod_expr, arena)?;
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                for mb in mbs.iter() {
                    let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                    validate_module_expr_this_errors(&mod_expr, arena)?;
                }
            }
            StructureItemDesc::Pstr_include(include_decl) => {
                let mod_expr = arena.get_mod_expr(include_decl.pincl_mod).clone();
                validate_module_expr_this_errors(&mod_expr, arena)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_module_expr_this_errors(
    mod_expr: &ModuleExpr,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => validate_structure_this_errors(items, arena),
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_name, _param, body) = &**inner;
            let body = arena.get_mod_expr(*body).clone();
            validate_module_expr_this_errors(&body, arena)
        }
        ModuleExprDesc::Pmod_apply(left, right) => {
            let left = arena.get_mod_expr(*left).clone();
            validate_module_expr_this_errors(&left, arena)?;
            let right = arena.get_mod_expr(*right).clone();
            validate_module_expr_this_errors(&right, arena)
        }
        ModuleExprDesc::Pmod_constraint(inner, _mty) => {
            let inner = arena.get_mod_expr(*inner).clone();
            validate_module_expr_this_errors(&inner, arena)
        }
        ModuleExprDesc::Pmod_extension(extension) => match &extension.1 {
            Payload::PStr(items) => validate_structure_this_errors(items, arena),
            _ => Ok(()),
        },
        _ => Ok(()),
    }
}

fn validate_expression_idx_this_errors(expr_idx: ExprIdx, arena: &mut ParseArena) -> PpxResult<()> {
    let expr = arena.get_expr(expr_idx).clone();
    validate_expression_this_errors(&expr, arena)
}

fn validate_method_callback_this_errors(
    expr: &Expression,
    arg_label: &ArgLabel,
    lhs: PatIdx,
    rhs: ExprIdx,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let self_pat = arena.get_pat(lhs).clone();
    if single_var_pattern_name_conservative(&self_pat, arena).is_none() {
        return Err(PpxError::at_loc(
            self_pat.ppat_loc,
            "%@this expect its pattern variable to be simple form",
        ));
    }

    if matches!(arg_label, ArgLabel::Optional(_)) {
        return Err(PpxError::at_loc(
            expr.pexp_loc,
            "Uncurried function doesn't support optional arguments yet",
        ));
    }

    let mut current_body = arena.get_expr(rhs).clone();
    loop {
        if has_this_attr(&current_body.pexp_attributes, arena) {
            return validate_expression_this_errors(&current_body, arena);
        }
        match &*current_body.pexp_desc {
            ExpressionDesc::Pexp_fun(inner) => {
                if matches!(inner.arg_label, ArgLabel::Optional(_)) {
                    return Err(PpxError::at_loc(
                        expr.pexp_loc,
                        "Uncurried function doesn't support optional arguments yet",
                    ));
                }
                current_body = arena.get_expr(inner.rhs).clone();
            }
            _ => return validate_expression_this_errors(&current_body, arena),
        }
    }
}

fn validate_expression_this_errors(expr: &Expression, arena: &mut ParseArena) -> PpxResult<()> {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) if has_this_attr(&expr.pexp_attributes, arena) => {
            validate_method_callback_this_errors(
                expr,
                &inner.arg_label,
                inner.lhs,
                inner.rhs,
                arena,
            )
        }
        ExpressionDesc::Pexp_fun(inner) => {
            if let Some(default) = inner.default {
                validate_expression_idx_this_errors(default, arena)?;
            }
            validate_expression_idx_this_errors(inner.rhs, arena)
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (_rec_flag, bindings, body) = &**inner;
            for binding in bindings {
                validate_expression_idx_this_errors(binding.pvb_expr, arena)?;
            }
            validate_expression_idx_this_errors(*body, arena)
        }
        ExpressionDesc::Pexp_apply(inner) => {
            validate_expression_idx_this_errors(inner.funct, arena)?;
            for (_label, arg) in &inner.args {
                validate_expression_idx_this_errors(*arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            validate_expression_idx_this_errors(*scrutinee, arena)?;
            for case in cases {
                if let Some(guard) = case.pc_guard {
                    validate_expression_idx_this_errors(guard, arena)?;
                }
                validate_expression_idx_this_errors(case.pc_rhs, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            for item in items.iter() {
                validate_expression_idx_this_errors(*item, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_construct(_, Some(arg))
        | ExpressionDesc::Pexp_field(arg, _)
        | ExpressionDesc::Pexp_assert(arg)
        | ExpressionDesc::Pexp_await(arg) => validate_expression_idx_this_errors(*arg, arena),
        ExpressionDesc::Pexp_variant(inner) => {
            if let Some(arg) = inner.1 {
                validate_expression_idx_this_errors(arg, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, spread) = &**inner;
            if let Some(spread) = spread {
                validate_expression_idx_this_errors(*spread, arena)?;
            }
            for field in fields {
                validate_expression_idx_this_errors(field.expr, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (target, _field, value) = &**inner;
            validate_expression_idx_this_errors(*target, arena)?;
            validate_expression_idx_this_errors(*value, arena)
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (cond, then_expr, else_expr) = &**inner;
            validate_expression_idx_this_errors(*cond, arena)?;
            validate_expression_idx_this_errors(*then_expr, arena)?;
            if let Some(else_expr) = else_expr {
                validate_expression_idx_this_errors(*else_expr, arena)?;
            }
            Ok(())
        }
        ExpressionDesc::Pexp_sequence(left, right) | ExpressionDesc::Pexp_while(left, right) => {
            validate_expression_idx_this_errors(*left, arena)?;
            validate_expression_idx_this_errors(*right, arena)
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (_pat, start, finish, _dir, body) = &**inner;
            validate_expression_idx_this_errors(*start, arena)?;
            validate_expression_idx_this_errors(*finish, arena)?;
            validate_expression_idx_this_errors(*body, arena)
        }
        ExpressionDesc::Pexp_for_of(inner)
        | ExpressionDesc::Pexp_for_await_of(inner)
        | ExpressionDesc::Pexp_inline_for(inner) => {
            let (_pat, collection, body) = &**inner;
            validate_expression_idx_this_errors(*collection, arena)?;
            validate_expression_idx_this_errors(*body, arena)
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (inner_expr, _typ) = &**inner;
            validate_expression_idx_this_errors(*inner_expr, arena)
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (inner_expr, _from, _to) = &**inner;
            validate_expression_idx_this_errors(*inner_expr, arena)
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_name, mod_expr, body) = &**inner;
            let mod_expr = arena.get_mod_expr(*mod_expr).clone();
            validate_module_expr_this_errors(&mod_expr, arena)?;
            validate_expression_idx_this_errors(*body, arena)
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (_ext, body) = &**inner;
            validate_expression_idx_this_errors(*body, arena)
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (_override, _lid, body) = &**inner;
            validate_expression_idx_this_errors(*body, arena)
        }
        ExpressionDesc::Pexp_extension(extension) => match &extension.1 {
            Payload::PStr(items) => validate_structure_this_errors(items, arena),
            _ => Ok(()),
        },
        _ => Ok(()),
    }
}

/// Handle @deriving(abstract) which transforms record types into abstract types with accessors
///
/// For a type like:
/// ```rescript
/// @deriving(abstract)
/// type t = { @optional cite: React.component<...>, info: props }
/// ```
///
/// Generates:
/// ```rescript
/// include (struct
///   include (struct type t = { ... } end : sig end)  // Original type hidden
///   type t                                           // Abstract type
///   external t: (~cite: ..., ~info: ...) => t        // Maker function
///   external citeGet: t => option<...>               // Getter for optional
///   external infoGet: t => props                     // Getter
/// end)
/// ```
fn handle_deriving_abstract(
    tdcls: &[TypeDeclaration],
    rec_flag: RecFlag,
    new_tdcls: &[TypeDeclaration],
    light: bool,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    let none_loc = arena.none_loc();

    // Generate the code for each type declaration
    let mut abstract_tdcls: Vec<TypeDeclaration> = vec![];
    let mut primitives: Vec<StructureItem> = vec![];

    for tdcl in tdcls {
        let (abstract_tdcl, value_descriptions) = handle_abstract_tdcl(tdcl, light, arena);
        abstract_tdcls.push(abstract_tdcl);
        for vd in value_descriptions {
            primitives.push(StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(vd))),
                pstr_loc: none_loc,
            });
        }
    }

    // Create the inner include: include (struct <original type with record> end : sig end)
    let type_str_item = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_type(Box::new((
            rec_flag,
            new_tdcls.to_vec(),
        )))),
        pstr_loc: loc,
    };

    let inner_mod = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(vec![
            type_str_item,
        ]))),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    let empty_sig = current::ModuleType {
        pmty_desc: Box::new(current::ModuleTypeDesc::Pmty_signature(Box::new(vec![]))),
        pmty_loc: loc,
        pmty_attributes: Attributes::new(),
    };

    let constrained_mod = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_constraint(
            arena.push_mod_expr(inner_mod),
            arena.push_mod_type(empty_sig),
        )),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    let inner_include = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_include(Box::new(
            current::IncludeDeclaration {
                pincl_mod: arena.push_mod_expr(constrained_mod),
                pincl_loc: loc,
                pincl_attributes: Attributes::new(),
            },
        ))),
        pstr_loc: loc,
    };

    // Create the abstract type declaration
    let abstract_type_str = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_type(Box::new((
            rec_flag,
            abstract_tdcls,
        )))),
        pstr_loc: none_loc,
    };

    // Build the outer structure: inner_include, abstract_type, primitives
    let mut outer_structure = vec![inner_include, abstract_type_str];
    outer_structure.extend(primitives);

    let outer_mod = ModuleExpr {
        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(outer_structure))),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    let outer_include = current::IncludeDeclaration {
        pincl_mod: arena.push_mod_expr(outer_mod),
        pincl_loc: loc,
        pincl_attributes: Attributes::new(),
    };

    vec![StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_include(Box::new(outer_include))),
        pstr_loc: loc,
    }]
}

/// Handle a single type declaration for @deriving(abstract)
/// Returns the abstract type declaration and the list of value descriptions (primitives)
fn handle_abstract_tdcl(
    tdcl: &TypeDeclaration,
    light: bool,
    arena: &mut ParseArena,
) -> (TypeDeclaration, Vec<ValueDescription>) {
    let loc = tdcl.ptype_loc;
    let type_name = arena.get_string(tdcl.ptype_name.txt).to_string();
    let core_type = core_type_of_type_declaration_with_attrs(tdcl, arena);

    let is_private = matches!(tdcl.ptype_private, PrivateFlag::Private);

    match &tdcl.ptype_kind {
        TypeKind::Ptype_record(labels) => {
            let abstract_tdcl = TypeDeclaration {
                ptype_name: tdcl.ptype_name.clone(),
                ptype_params: tdcl.ptype_params.clone(),
                ptype_cstrs: tdcl.ptype_cstrs.clone(),
                ptype_kind: TypeKind::Ptype_abstract,
                ptype_private: tdcl.ptype_private.clone(),
                ptype_manifest: tdcl.ptype_manifest.clone(),
                ptype_attributes: Attributes::new(),
                ptype_loc: tdcl.ptype_loc,
            };
            // OCaml uses Ext_list.fold_right which processes right-to-left and prepends (::)
            // This results in accessors in the same order as the original labels.
            // We collect into vectors and then reverse to get the same effect.
            let mut setter_accessor: Vec<ValueDescription> = vec![];

            // Check if any field has @optional
            let has_optional_field = labels.iter().any(|label| {
                label.pld_attributes.iter().any(|(attr_name, _)| {
                    let name = arena.get_string(attr_name.txt);
                    name == "optional"
                })
            });

            // Build maker args and labels_info
            // OCaml: fold_right starts with [unit] or [] accumulator, and prepends each arg
            let mut maker_args: Vec<TypeArg> = vec![];
            let mut labels_info: Vec<(bool, Located<StrIdx>)> = vec![];

            // Process in reverse order (like fold_right) and prepend (like ::)
            for label in labels.iter().rev() {
                let label_name = arena.get_string(label.pld_name.txt).to_string();
                let label_loc = label.pld_name.loc;
                let pld_type = &label.pld_type;

                // Check for @as attribute
                let prim_as_attr = get_bs_as_string(&label.pld_attributes, arena);
                let prim_as_name = prim_as_attr.clone().unwrap_or_else(|| label_name.clone());
                let prim_as_idx = match &prim_as_attr {
                    Some(name) if name != &label_name => arena.intern_string(name),
                    _ => label.pld_name.txt,
                };
                let new_label = if prim_as_name != label_name {
                    Located {
                        txt: arena.intern_string(&prim_as_name),
                        loc: label.pld_name.loc,
                    }
                } else {
                    label.pld_name.clone()
                };

                let is_optional = label.pld_attributes.iter().any(|(attr_name, _)| {
                    let name = arena.get_string(attr_name.txt);
                    name == "optional"
                });

                // Build the argument for maker function
                let arg_label = if is_optional {
                    ArgLabel::Optional(label.pld_name.clone())
                } else {
                    ArgLabel::Labelled(label.pld_name.clone())
                };

                // Insert at front (like OCaml :: prepending)
                maker_args.insert(
                    0,
                    TypeArg {
                        attrs: Attributes::new(),
                        lbl: arg_label,
                        typ: pld_type.clone(),
                    },
                );

                labels_info.insert(0, (is_optional, new_label.clone()));

                // Build accessor type
                // OCaml behavior varies based on whether encode_attributes_as_string processes it:
                // - Non-optional: pval_prim already has FFI encoding, rs_externals returns false,
                //   arrow is NOT re-processed. Arrow uses tdcl.ptype_loc (from Typ.arrows ~loc).
                // - Optional: pval_prim = [name] with @get attr, rs_externals returns true,
                //   encode_attributes_as_string rebuilds arrow with pval_loc = pld_loc.
                let accessor_type = if is_optional {
                    // Returns option<pld_type>
                    // After encode_attributes_as_string, arrow uses pld_loc
                    let pld_core_type = arena.get_core_type(*pld_type).clone();
                    let option_type = lift_option_type(&pld_core_type, arena);
                    make_arrow_type_with_loc(&core_type, &option_type, Some(label.pld_loc), arena)
                } else {
                    // Not re-processed, arrow uses tdcl.ptype_loc
                    let pld_core_type = arena.get_core_type(*pld_type).clone();
                    make_arrow_type_with_loc(&core_type, &pld_core_type, Some(loc), arena)
                };

                // Accessor primitive:
                // Both optional and non-optional go through encode_attributes_as_string,
                // which produces [prim_name, ffi_data].
                //
                // For optional: originally has [prim_as_name] with @get attr
                //   -> encode_attributes_as_string processes @get -> [prim_as_name, ffi_bs Js_get]
                // For non-optional: has ffi_bs_as_prims [dummy] -> ["", ffi_bs Js_get]
                //
                // The difference is:
                // - Optional: prim_name = prim_as_name, first string is the name
                // - Non-optional: prim_name = "", first string is empty
                //
                // Note: OCaml's ffi_bs uses Param_number(1) for [dummy] because
                // ffi_bs_aux counts consecutive dummy params.
                let accessor_prim = if is_optional {
                    // OCaml: encode_attributes_as_string processes @get attr
                    // The default external_desc.return_wrapper is Return_unset
                    // check_return_wrapper keeps Return_unset for non-unit result types
                    // ffi_bs([dummy]) returns Param_number(1)
                    let ffi = FfiType::FfiBs {
                        params: Params::ParamNumber(1),
                        return_wrapper: ReturnWrapper::ReturnUnset, // Default for encode_attributes_as_string
                        external_spec: ExternalSpec::JsGet {
                            js_get_name: prim_as_name.clone(),
                            js_get_scopes: vec![],
                        },
                    };
                    vec![prim_as_idx, prim_str(arena, encode_ffi_type(&ffi))]
                } else {
                    // OCaml: ffi_bs_as_prims [dummy] Return_identity (Js_get {...})
                    // This explicitly passes Return_identity
                    let ffi = FfiType::FfiBs {
                        params: Params::ParamNumber(1),
                        return_wrapper: ReturnWrapper::ReturnIdentity,
                        external_spec: ExternalSpec::JsGet {
                            js_get_name: prim_as_name.clone(),
                            js_get_scopes: vec![],
                        },
                    };
                    vec![
                        arena.prim_empty_external_ffi(),
                        prim_str(arena, encode_ffi_type(&ffi)),
                    ]
                };

                // Accessor attributes: empty for both (FFI attrs like @get are consumed during encoding)
                let accessor_attrs: Vec<Attribute> = vec![];

                let accessor_name = if light {
                    label.pld_name.clone()
                } else {
                    Located {
                        txt: arena.push_string(format!("{}Get", label_name)),
                        loc: label.pld_name.loc,
                    }
                };

                let accessor_vd = ValueDescription {
                    pval_name: accessor_name,
                    pval_type: arena.push_core_type(accessor_type),
                    pval_prim: accessor_prim,
                    pval_attributes: accessor_attrs.into(),
                    pval_loc: label.pld_loc,
                };
                // Insert at front (like OCaml :: prepending)
                setter_accessor.insert(0, accessor_vd);

                // Setter for mutable fields - also insert at front
                if matches!(label.pld_mutable, current::MutableFlag::Mutable) {
                    let pld_core_type = arena.get_core_type(*pld_type).clone();
                    let setter_type = make_setter_type_with_loc(
                        &core_type,
                        &pld_core_type,
                        Some(label.pld_loc),
                        arena,
                    );
                    // OCaml: setter pval_prim = [prim_as_name], pval_attributes = [@set]
                    // The @set attribute gets processed by encode_external which adds
                    // JsSet FFI encoding as a second prim string.
                    // We do this directly here since our pipeline doesn't re-process.
                    let setter_ffi = FfiType::FfiBs {
                        params: Params::ParamNumber(2),
                        return_wrapper: ReturnWrapper::ReturnReplacedWithUnit,
                        external_spec: ExternalSpec::JsSet {
                            js_set_name: prim_as_name.clone(),
                            js_set_scopes: vec![],
                        },
                    };
                    let setter_prim =
                        vec![prim_as_idx, prim_str(arena, encode_ffi_type(&setter_ffi))];
                    let setter_vd = ValueDescription {
                        pval_name: Located {
                            txt: arena.push_string(format!("{}Set", label_name)),
                            loc: label_loc,
                        },
                        pval_type: arena.push_core_type(setter_type),
                        pval_prim: setter_prim,
                        pval_attributes: Attributes::new(),
                        pval_loc: label.pld_loc,
                    };
                    // Setter comes before accessor in OCaml's prepend order
                    setter_accessor.insert(0, setter_vd);
                }
            }

            // Add unit arg at the end if has_optional_field (OCaml starts fold_right with [unit])
            if has_optional_field {
                let unit_type = make_unit_type(arena);
                maker_args.push(TypeArg {
                    attrs: Attributes::new(),
                    lbl: ArgLabel::Nolabel,
                    typ: arena.push_core_type(unit_type),
                });
            }

            // Build the final value descriptions
            let value_descs = if is_private {
                setter_accessor
            } else {
                // Build maker type - use type decl location for outer arrow
                let make_type = if maker_args.is_empty() {
                    core_type.clone()
                } else {
                    make_arrows_type_with_loc(&maker_args, &core_type, Some(loc), arena)
                };

                // Compute prim for maker: ffi_obj_as_prims
                let my_prims = compute_maker_prims(&labels_info, has_optional_field, arena);

                let maker_vd = ValueDescription {
                    // Reuse the type declaration's name identity so marshal sharing
                    // matches OCaml in @deriving(abstract) maker generation.
                    pval_name: Located {
                        txt: tdcl.ptype_name.txt,
                        loc,
                    },
                    pval_type: arena.push_core_type(make_type),
                    pval_prim: my_prims,
                    pval_attributes: Attributes::new(),
                    pval_loc: loc,
                };

                // OCaml: my_maker :: setter_accessor
                let mut result = vec![maker_vd];
                result.extend(setter_accessor);
                result
            };

            (abstract_tdcl, value_descs)
        }
        _ => {
            // OCaml keeps non-record declarations unchanged for deriving(abstract).
            (tdcl.clone(), vec![])
        }
    }
}

/// Lift a type to option<type>
fn lift_option_type(typ: &CoreType, arena: &mut ParseArena) -> CoreType {
    // OCaml's lift_option_type:
    //   { ptyp_desc = Ptyp_constr ({txt = Ast_literal.predef_option; loc = ptyp_loc}, [ty]);
    //     ptyp_loc;
    //     ptyp_attributes = [] }
    // predef_option = Ldot(Lident "*predef*", "option")
    let ptyp_loc = typ.ptyp_loc;
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: arena.predef_option_lident(),
                loc: ptyp_loc,
            },
            vec![arena.push_core_type(typ.clone())],
        )))),
        ptyp_loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Create an arrow type: arg -> ret (uses ghost location)
fn make_arrow_type(arg: &CoreType, ret: &CoreType, arena: &mut ParseArena) -> CoreType {
    make_arrow_type_with_loc(arg, ret, None, arena)
}

/// Create an arrow type: arg -> ret with explicit location
/// If loc is Some, uses that location; otherwise uses ghost
fn make_arrow_type_with_loc(
    arg: &CoreType,
    ret: &CoreType,
    loc: Option<LocIdx>,
    arena: &mut ParseArena,
) -> CoreType {
    let ptyp_loc = loc.unwrap_or_else(|| arena.none_loc());
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(arg.clone()),
            }),
            arena.push_core_type(ret.clone()),
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Create setter type: t -> field_type -> unit (uses ghost location)
fn make_setter_type(
    record_type: &CoreType,
    field_type: &CoreType,
    arena: &mut ParseArena,
) -> CoreType {
    make_setter_type_with_loc(record_type, field_type, None, arena)
}

/// Create setter type: t -> field_type -> unit with explicit location
/// If loc is Some, uses that for the outermost arrow; inner arrow uses ghost
fn make_setter_type_with_loc(
    record_type: &CoreType,
    field_type: &CoreType,
    loc: Option<LocIdx>,
    arena: &mut ParseArena,
) -> CoreType {
    let none_loc = arena.none_loc();
    let outer_loc = loc.unwrap_or(none_loc);
    let unit_type = make_unit_type(arena);

    let args = vec![
        TypeArg {
            attrs: Attributes::new(),
            lbl: ArgLabel::Nolabel,
            typ: arena.push_core_type(record_type.clone()),
        },
        TypeArg {
            attrs: Attributes::new(),
            lbl: ArgLabel::Nolabel,
            typ: arena.push_core_type(field_type.clone()),
        },
    ];
    make_arrows_type_with_loc(&args, &unit_type, Some(outer_loc), arena)

}

/// Create unit type
fn make_unit_type(arena: &mut ParseArena) -> CoreType {
    let none_loc = arena.none_loc();
    let unit_ident = arena.push_lident_static("unit");
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: unit_ident,
                loc: none_loc,
            },
            vec![],
        )))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Create arrow type with multiple arguments (uses ghost location)
fn make_arrows_type(args: &[TypeArg], ret: &CoreType, arena: &mut ParseArena) -> CoreType {
    make_arrows_type_with_loc(args, ret, None, arena)
}

/// Create arrow type with multiple arguments
/// OCaml's Typ.arrows:
/// - Uses the provided loc for ALL arrows (loc is a closure variable)
/// - Outermost arrow has `arity = Some(len(args))`
/// - Inner arrows have `arity = None`
fn make_arrows_type_with_loc(
    args: &[TypeArg],
    ret: &CoreType,
    loc: Option<LocIdx>,
    arena: &mut ParseArena,
) -> CoreType {
    let none_loc = arena.none_loc();
    let ptyp_loc = loc.unwrap_or(none_loc);
    if args.is_empty() {
        return ret.clone();
    }

    let args = args.to_vec();
    let arity = arena.push_arity(Some(args.len() as i32));
    let first = args[0].clone();
    arena.set_nary_arrow_args(arity, args);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(first),
            arena.push_core_type(ret.clone()),
            arity,
        )))),
        ptyp_loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Make @get attribute
fn make_get_attr(loc: LocIdx, arena: &mut ParseArena) -> Attribute {
    (
        Located {
            txt: arena.intern_string("get"),
            loc,
        },
        Payload::PStr(Box::new(vec![])),
    )
}

/// Make @set attribute
fn make_set_attr(loc: LocIdx, arena: &mut ParseArena) -> Attribute {
    (
        Located {
            txt: arena.intern_string("set"),
            loc,
        },
        Payload::PStr(Box::new(vec![])),
    )
}

/// Get the @as("...") attribute value
fn get_bs_as_string(attrs: &[Attribute], arena: &ParseArena) -> Option<String> {
    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        if name == "as" {
            if let Some(items) = payload_str_items(payload) {
                if let Some(item) = items.first() {
                    if let StructureItemDesc::Pstr_eval(eval_inner) = &*item.pstr_desc {
                        let (ref expr, _) = **eval_inner;
                        if let ExpressionDesc::Pexp_constant(c) = &*arena.get_expr(*expr).pexp_desc
                        {
                            if let Constant::String(txt, _) = &**c {
                                return Some(txt.to_string());
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

/// Compute prims for maker function based on optional labels
///
/// OCaml's pval_prim_of_option_labels produces:
///   [""; encode(Ffi_obj_create(arg_kinds))]
///
/// where arg_kinds is built from labels_info:
/// - For optional labels: ObjOptional { name, for_sure_no_nested_option: false }
/// - For non-optional labels: ObjLabel { name }
/// - If ends_with_unit: [empty_kind Extern_unit] at the end
fn compute_maker_prims(
    labels_info: &[(bool, Located<StrIdx>)],
    has_optional: bool,
    arena: &mut ParseArena,
) -> Vec<StrIdx> {
    // Build arg_kinds list matching OCaml's pval_prim_of_option_labels
    let mut arg_kinds: Vec<ObjParam> = Vec::new();

    for (is_optional, label) in labels_info {
        let label_name = arena.get_string(label.txt).to_string();
        let obj_arg_label = if *is_optional {
            // OCaml: External_arg_spec.optional false label_name
            // for_sure_no_nested_option = false
            Label::ObjOptional {
                name: label_name,
                for_sure_no_nested_option: false,
            }
        } else {
            // OCaml: External_arg_spec.obj_label label_name
            Label::ObjLabel { name: label_name }
        };

        arg_kinds.push(ObjParam {
            obj_arg_type: Attr::Nothing,
            obj_arg_label,
        });
    }

    // If ends_with_unit (has_optional), add empty_kind Extern_unit at the end
    if has_optional {
        arg_kinds.push(ObjParam {
            obj_arg_type: Attr::ExternUnit,
            obj_arg_label: Label::ObjEmpty,
        });
    }

    // OCaml: ffi_obj_as_prims arg_kinds = [""; to_string (Ffi_obj_create arg_kinds)]
    let ffi = FfiType::FfiObjCreate(arg_kinds);
    vec![
        arena.prim_empty_external_ffi(),
        prim_str(arena, encode_ffi_type(&ffi)),
    ]
}

/// Generate accessor structure/signature items for one type declaration.
fn generate_accessor_items_for_tdcl(
    tdcl: &TypeDeclaration,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> Option<(Vec<StructureItem>, Vec<SignatureItem>)> {
    // OCaml computes core_type separately in structure_gen and signature_gen.
    // Keep them physically distinct to match marshal sharing.
    let structure_core_type_with_attrs = core_type_of_type_declaration_with_attrs(tdcl, arena);
    let signature_core_type_with_attrs = core_type_of_type_declaration_with_attrs(tdcl, arena);

    let (structure_items, signature_items) = match &tdcl.ptype_kind {
        TypeKind::Ptype_record(labels) => generate_record_accessors_and_sigs(
            labels,
            &structure_core_type_with_attrs,
            &signature_core_type_with_attrs,
            loc,
            arena,
        ),
        TypeKind::Ptype_variant(constructors) => generate_variant_accessors_and_sigs(
            constructors,
            tdcl,
            &structure_core_type_with_attrs,
            &signature_core_type_with_attrs,
            loc,
            arena,
        ),
        _ => return None, // Abstract or open types not supported
    };

    Some((structure_items, signature_items))
}

/// Generate `include (struct <accessor_bindings> end : sig <accessor_sigs> end)`
/// for the full `tdcls` group (one include per deriving action, matching OCaml).
fn generate_accessor_include(
    tdcls: &[TypeDeclaration],
    loc: LocIdx,
    arena: &mut ParseArena,
) -> StructureItem {
    let mut structure_items: Vec<StructureItem> = vec![];
    let mut signature_items: Vec<SignatureItem> = vec![];

    for tdcl in tdcls {
        if let Some((mut tdcl_structure_items, mut tdcl_signature_items)) =
            generate_accessor_items_for_tdcl(tdcl, loc, arena)
        {
            structure_items.append(&mut tdcl_structure_items);
            signature_items.append(&mut tdcl_signature_items);
        }
    }

    build_structure_signature_include(structure_items, signature_items, loc, arena)
}

fn gentype_attrs_for_derived_accessors(core_type: &CoreType, arena: &mut ParseArena) -> Attributes {
    // OCaml compiler/frontend/ast_derive_projector.ml:30-38 and
    // compiler/frontend/ast_derive_projector.ml:124-132 check whether the
    // synthesized core type carries a GenType attribute; when it does, generated
    // accessors receive exactly `Ast_attributes.gentype`
    // from compiler/frontend/ast_attributes.ml:285-290.
    let has_gentype = core_type
        .ptyp_attributes
        .iter()
        .any(|(attr_name, _)| matches!(arena.get_string(attr_name.txt), "genType" | "gentype"));

    if has_gentype {
        Attributes::from_vec(vec![(
            Located {
                txt: arena.intern_string("genType"),
                loc: arena.none_loc(),
            },
            Payload::PStr(Box::new(vec![])),
        )])
    } else {
        Attributes::new()
    }
}

/// Generate accessor structure items and signature items for record fields
fn generate_record_accessors_and_sigs(
    labels: &[current::LabelDeclaration],
    structure_core_type: &CoreType,
    signature_core_type: &CoreType,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> (Vec<StructureItem>, Vec<SignatureItem>) {
    let mut structure_items = Vec::new();
    let mut signature_items = Vec::new();
    let gentype_attrs = gentype_attrs_for_derived_accessors(structure_core_type, arena);

    // OCaml uses Location.none (ghost) for generated expression/pattern locations
    // because Exp.field, Exp.ident, Pat.var, Pat.constraint_, Ast_compatible.fun_
    // don't receive ~loc argument. But longident locations use the actual label location.
    let none_loc = arena.none_loc();

    for label in labels {
        // Get the label's location for longident locations
        let label_loc = label.pld_name.loc;

        // Structure item: let fieldName = (param: t) => param.fieldName
        let param_str = arena.intern_string("param");
        // OCaml: Pat.constraint_ (Pat.var {txt; loc}) core_type
        // Pat.var and Pat.constraint_ have no ~loc, use default_loc (ghost)
        let inner_pat = Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                txt: param_str,
                loc: label_loc,
            })),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        };
        let inner_pat_idx = arena.push_pat(inner_pat);
        let param_pat = Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
                inner_pat_idx,
                arena.push_core_type(structure_core_type.clone()),
            )))),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        };

        // OCaml: Exp.field (Exp.ident {txt = Lident txt; loc}) {txt = Longident.Lident pld_label; loc}
        // Exp.field and Exp.ident have no ~loc, use default_loc (ghost)
        let fa_lid = arena.push_lident_from_idx(param_str);
        let fa_ident = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: fa_lid,
                loc: label_loc,
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        let fa_idx = arena.push_expr(fa_ident);
        let fa_field_lid = arena.push_longident(Longident::Lident(label.pld_name.txt));
        let field_access = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_field(
                fa_idx,
                Located {
                    txt: fa_field_lid,
                    loc: label_loc,
                },
            )),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };

        // OCaml: Ast_compatible.fun_ ~arity:(Some 1) pat exp - no ~loc
        let fun_expr = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label: ArgLabel::Nolabel,
                default: None,
                lhs: arena.push_pat(param_pat),
                rhs: arena.push_expr(field_access),
                is_async: false,
                arity: arena.static_ppx_arity_1(),
            }))),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };

        // OCaml: Ast_comb.single_non_rec_value pld_name ...
        // single_non_rec_value = Str.value Nonrecursive [Vb.mk (Pat.var name) exp]
        // - Vb.mk has no ~loc, so pvb_loc = ghost
        // - Str.value has no ~loc, so pstr_loc = ghost
        let binding = ValueBinding {
            pvb_pat: arena.push_pat(Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                    txt: label.pld_name.txt,
                    loc: label_loc,
                })),
                ppat_loc: none_loc,
                ppat_attributes: Attributes::new(),
            }),
            pvb_expr: arena.push_expr(fun_expr),
            pvb_attributes: gentype_attrs.clone(),
            pvb_loc: none_loc,
        };

        structure_items.push(StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
                RecFlag::Nonrecursive,
                vec![binding],
            )))),
            pstr_loc: none_loc,
        });

        // Signature item: val fieldName: t -> fieldType
        // OCaml: Ast_helper.Typ.arrows [{attrs; lbl; typ}] pld_type - no ~loc
        let arrow_type = CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
                Box::new(TypeArg {
                    attrs: Attributes::new(),
                    lbl: ArgLabel::Nolabel,
                    typ: arena.push_core_type(signature_core_type.clone()),
                }),
                label.pld_type,
                arena.push_arity(Some(1)),
            )))),
            ptyp_loc: none_loc,
            ptyp_attributes: Attributes::new(),
        };

        // OCaml: Ast_comb.single_non_rec_val pld_name arrow_type
        // single_non_rec_val = Sig.value (Val.mk name ty)
        // - Val.mk has no ~loc, so pval_loc = ghost
        // - Sig.value has no ~loc, so psig_loc = ghost
        let val_desc = ValueDescription {
            pval_name: Located {
                txt: label.pld_name.txt,
                loc: label_loc,
            },
            pval_type: arena.push_core_type(arrow_type),
            pval_prim: vec![],
            pval_attributes: gentype_attrs.clone(),
            pval_loc: none_loc,
        };

        signature_items.push(SignatureItem {
            psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(val_desc))),
            psig_loc: none_loc,
        });
    }

    (structure_items, signature_items)
}

/// Generate accessor structure items and signature items for variant constructors
fn generate_variant_accessors_and_sigs(
    constructors: &[current::ConstructorDeclaration],
    _tdcl: &TypeDeclaration,
    structure_core_type: &CoreType,
    signature_core_type: &CoreType,
    _loc: LocIdx,
    arena: &mut ParseArena,
) -> (Vec<StructureItem>, Vec<SignatureItem>) {
    let mut structure_items = Vec::new();
    let mut signature_items = Vec::new();
    let gentype_attrs = gentype_attrs_for_derived_accessors(structure_core_type, arena);
    let none_loc = arena.none_loc();

    for ctor in constructors {
        let ctor_loc = ctor.pcd_name.loc;
        let ctor_name = arena.get_string(ctor.pcd_name.txt);
        let fn_name = uncapitalize_first(ctor_name);
        let fn_name_idx = arena.intern_string(&fn_name);

        let arity = match &ctor.pcd_args {
            ConstructorArguments::Pcstr_tuple(args) => args.len(),
            ConstructorArguments::Pcstr_record(_) => {
                // Record constructors not supported, skip
                continue;
            }
        };

        let structure_annotate_type = match &ctor.pcd_res {
            Some(t) => *t,
            None => arena.push_core_type(structure_core_type.clone()),
        };
        let signature_annotate_type = match &ctor.pcd_res {
            Some(t) => arena.get_core_type(*t).clone(),
            None => signature_core_type.clone(),
        };

        if arity == 0 {
            // No args: let ctorName = CtorName : t
            let ctor_lid = arena.push_longident(Longident::Lident(ctor.pcd_name.txt));
            let construct_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                    Located {
                        txt: ctor_lid,
                        loc: ctor_loc,
                    },
                    None,
                )),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };
            let construct_idx = arena.push_expr(construct_expr);
            let ctor_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    construct_idx,
                    structure_annotate_type,
                )))),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };

            let binding = ValueBinding {
                pvb_pat: arena.push_pat(Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                        txt: fn_name_idx,
                        loc: ctor_loc,
                    })),
                    ppat_loc: none_loc,
                    ppat_attributes: Attributes::new(),
                }),
                pvb_expr: arena.push_expr(ctor_expr),
                pvb_attributes: gentype_attrs.clone(),
                pvb_loc: none_loc,
            };

            structure_items.push(StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
                    RecFlag::Nonrecursive,
                    vec![binding],
                )))),
                pstr_loc: none_loc,
            });

            // val ctorName: t
            let val_desc = ValueDescription {
                pval_name: Located {
                    txt: fn_name_idx,
                    loc: ctor_loc,
                },
                pval_type: arena.push_core_type(signature_annotate_type),
                pval_prim: vec![],
                pval_attributes: gentype_attrs.clone(),
                pval_loc: none_loc,
            };

            signature_items.push(SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(val_desc))),
                psig_loc: none_loc,
            });
        } else {
            // Has args: let ctorName = (p0, p1, ...) => CtorName(p0, p1, ...)
            let params: Vec<StrIdx> = (0..arity)
                .map(|i| arena.intern_string(&format!("param_{}", i)))
                .collect();

            // Build constructor argument (single or tuple)
            let ctor_arg = if arity == 1 {
                Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                        txt: arena.push_lident_from_idx(params[0]),
                        loc: ctor_loc,
                    })),
                    pexp_loc: none_loc,
                    pexp_attributes: Attributes::new(),
                }
            } else {
                let tuple_items: Vec<ExprIdx> = params
                    .iter()
                    .map(|&p| {
                        let expr = Expression {
                            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                                txt: arena.push_lident_from_idx(p),
                                loc: ctor_loc,
                            })),
                            pexp_loc: none_loc,
                            pexp_attributes: Attributes::new(),
                        };
                        arena.push_expr(expr)
                    })
                    .collect();
                Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_tuple(Box::new(tuple_items))),
                    pexp_loc: none_loc,
                    pexp_attributes: Attributes::new(),
                }
            };

            let ctor_lid = arena.push_longident(Longident::Lident(ctor.pcd_name.txt));
            let ctor_arg_idx = arena.push_expr(ctor_arg);
            let construct_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                    Located {
                        txt: ctor_lid,
                        loc: ctor_loc,
                    },
                    Some(ctor_arg_idx),
                )),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };
            let construct_idx = arena.push_expr(construct_expr);
            let ctor_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    construct_idx,
                    structure_annotate_type,
                )))),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };

            let body = arena.push_expr(ctor_expr);
            let arity_id = arena.push_arity(Some(arity as i32));
            let unknown_arity = arena.push_arity(None);
            let fun_params = params
                .iter()
                .map(|&param| FunParam {
                    p_attrs: Attributes::new(),
                    p_lbl: ArgLabel::Nolabel,
                    p_default: None,
                    p_pat: arena.push_pat(Pattern {
                        ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                            txt: param,
                            loc: ctor_loc,
                        })),
                        ppat_loc: none_loc,
                        ppat_attributes: Attributes::new(),
                    }),
                })
                .collect::<Vec<_>>();
            let first = fun_params[0].clone();
            arena.set_nary_fun_params(arity_id, fun_params, unknown_arity);
            let final_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: first.p_lbl,
                    default: None,
                    lhs: first.p_pat,
                    rhs: body,
                    is_async: false,
                    arity: arity_id,
                }))),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };

            let binding = ValueBinding {
                pvb_pat: arena.push_pat(Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_var(Located {
                        txt: fn_name_idx,
                        loc: ctor_loc,
                    })),
                    ppat_loc: none_loc,
                    ppat_attributes: Attributes::new(),
                }),
                pvb_expr: arena.push_expr(final_expr),
                pvb_attributes: gentype_attrs.clone(),
                pvb_loc: none_loc,
            };

            structure_items.push(StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
                    RecFlag::Nonrecursive,
                    vec![binding],
                )))),
                pstr_loc: none_loc,
            });

            // Signature: val ctorName: arg0 -> arg1 -> ... -> t
            let pcd_args = match &ctor.pcd_args {
                ConstructorArguments::Pcstr_tuple(args) => args.clone(),
                _ => vec![],
            };
            let args: Vec<TypeArg> = pcd_args
                .iter()
                .map(|arg_type| TypeArg {
                    attrs: Attributes::new(),
                    lbl: ArgLabel::Nolabel,
                    typ: arg_type.clone(),
                })
                .collect();
            let arrow_type = make_arrows(args, signature_annotate_type, ctor_loc, arena);

            let val_desc = ValueDescription {
                pval_name: Located {
                    txt: fn_name_idx,
                    loc: ctor_loc,
                },
                pval_type: arena.push_core_type(arrow_type),
                pval_prim: vec![],
                pval_attributes: gentype_attrs.clone(),
                pval_loc: none_loc,
            };

            signature_items.push(SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(val_desc))),
                psig_loc: none_loc,
            });
        }
    }

    (structure_items, signature_items)
}

/// Create an arrow type from a list of arguments and return type.
/// Matches OCaml's Typ.arrows: only the outermost arrow gets arity = Some(n),
/// inner arrows get arity = None.
fn make_arrows(args: Vec<TypeArg>, ret: CoreType, loc: LocIdx, arena: &mut ParseArena) -> CoreType {
    if args.is_empty() {
        return ret;
    }

    let arity = arena.push_arity(Some(args.len() as i32));
    let first = args[0].clone();
    arena.set_nary_arrow_args(arity, args);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(first),
            arena.push_core_type(ret),
            arity,
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Generate a core type with attributes (including @deriving)
/// This matches OCaml's Ast_derive_util.core_type_of_type_declaration
fn core_type_of_type_declaration_with_attrs(
    tdcl: &TypeDeclaration,
    arena: &mut ParseArena,
) -> CoreType {
    // OCaml: Typ.constr ~attrs {txt = Lident txt; loc} (Ext_list.map ptype_params fst)
    // - loc in longident is ptype_name.loc (the name's location)
    // - Typ.constr has no ~loc argument, so ptyp_loc = !default_loc = ghost
    let name_loc = tdcl.ptype_name.loc;
    let none_loc = arena.none_loc();
    let name_lid = arena.push_longident(Longident::Lident(tdcl.ptype_name.txt));

    let type_args: Vec<CoreTypeIdx> = tdcl
        .ptype_params
        .iter()
        .map(|(core_type, _)| core_type.clone())
        .collect();

    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located {
                txt: name_lid,
                loc: name_loc,
            },
            type_args,
        )))),
        ptyp_loc: none_loc,
        // Include the type declaration's attributes (which has @deriving)
        ptyp_attributes: tdcl.ptype_attributes.clone(),
    }
}

// ========== PPX Application ==========

/// Apply built-in PPX transformations to a structure.
///
/// This implements OCaml's `structure_mapper` which:
/// 1. Processes each structure item with rewrite_structure_item
/// 2. For Pstr_value items, "spelunks" through expressions to find Pexp_letmodule
///    with @res.await and hoists module type declarations before the Pstr_value
///
/// OCaml: bs_builtin_ppx.ml lines 656-755 (structure_mapper)
pub fn rewrite_structure(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> PpxResult<Vec<StructureItem>> {
    validate_structure_deriving_errors(structure, arena)?;
    validate_structure_method_attribute_errors(structure, arena)?;
    validate_structure_js_string_errors(structure, arena)?;
    validate_structure_await_errors(structure, arena, true)?;
    validate_structure_this_errors(structure, arena)?;

    // Context for tracking already-created module type names (per-structure scope)
    let mut await_context = std::collections::HashSet::new();
    let mut result = Vec::new();
    let spice_mapper_active = spice_ppx::structure_uses_spice_mapper(structure, arena);

    for item in structure {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_module(mb) => {
                // OCaml structure_mapper handles module-level await here (not in structure_item mapper)
                // and deduplicates generated module type declarations per structure.
                if let Some((module_type_decl, transformed_mb)) =
                    transform_module_await(mb, item.pstr_loc, arena)
                {
                    let mb_expr = arena.get_mod_expr(mb.pmb_expr);
                    if let ModuleExprDesc::Pmod_ident(located_lid) = &*mb_expr.pmod_desc {
                        let module_type_name = local_module_type_name(located_lid.txt, arena);
                        if await_context.insert(module_type_name) {
                            result.push(module_type_decl);
                        }
                    }
                    result.push(transformed_mb);
                } else {
                    result.extend(try_rewrite_structure_item(
                        item,
                        arena,
                        spice_mapper_active,
                    )?);
                }
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (ref _rec_flag, ref bindings) = **inner;
                // Spelunk through the ORIGINAL bindings to find await module types
                // (before expression rewriting transforms them)
                let module_type_decls = spelunk_value_bindings_for_await_module_types(
                    bindings,
                    &mut await_context,
                    arena,
                );

                // Add hoisted module type declarations first
                result.extend(module_type_decls);

                // Then process the structure item normally
                result.extend(try_rewrite_structure_item(
                    item,
                    arena,
                    spice_mapper_active,
                )?);
            }
            _ => {
                // Non-Pstr_value items: just process normally
                result.extend(try_rewrite_structure_item(
                    item,
                    arena,
                    spice_mapper_active,
                )?);
            }
        }
    }

    validate_structure_builtin_type_redefinition_errors(&result, arena)?;

    Ok(result)
}

/// Lightweight extension expansion: only expands %%raw, %raw, %re, %%private.
/// Does NOT touch externals, @deriving, or other transformations.
/// This is safe to call before type checking without breaking existing code.
pub fn expand_extensions(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> PpxResult<Vec<StructureItem>> {
    // Match OCaml bs_builtin_ppx structure_mapper/aux order:
    // for consecutive %%private, process `rest` first and then prepend the
    // local module wrapper for the accumulated private items.
    fn expand_extensions_rec(
        structure: &[StructureItem],
        arena: &mut ParseArena,
    ) -> PpxResult<Vec<StructureItem>> {
        if structure.is_empty() {
            return Ok(Vec::new());
        }

        if is_private_extension(&structure[0], arena) {
            let mut i = 0;
            let first_loc = structure[0].pstr_loc;
            let mut accumulated_items: Vec<StructureItem> = Vec::new();
            while i < structure.len() && is_private_extension(&structure[i], arena) {
                if let StructureItemDesc::Pstr_extension(inner) = &*structure[i].pstr_desc {
                    let (ext, _attrs) = &**inner;
                    let (ext_name, payload) = ext;
                    let items = private_extension_structure_items(payload, ext_name.loc)?;
                    for item in items.iter() {
                        accumulated_items.extend(expand_extensions_item(item, arena)?);
                    }
                }
                i += 1;
            }

            let mut rest = expand_extensions_rec(&structure[i..], arena)?;
            if accumulated_items.is_empty() {
                Ok(rest)
            } else {
                check_private_extension_items(&accumulated_items, arena)?;
                let mut wrapped = wrap_in_local_module(accumulated_items, first_loc, arena);
                wrapped.append(&mut rest);
                Ok(wrapped)
            }
        } else {
            // Preserve OCaml mapper side-effect order: in `item :: mapper rest`,
            // `rest` is evaluated first, so local-module counters observed by
            // `expand_extensions_item(item, ...)` reflect the already-processed
            // tail even though output order remains head-then-tail.
            let mut rest = expand_extensions_rec(&structure[1..], arena)?;
            let mut first = expand_extensions_item(&structure[0], arena)?;
            first.append(&mut rest);
            Ok(first)
        }
    }

    expand_extensions_rec(structure, arena)
}

/// Check if a structure item is a %%private extension
fn is_private_extension(item: &StructureItem, arena: &ParseArena) -> bool {
    if let StructureItemDesc::Pstr_extension(inner) = &*item.pstr_desc {
        let (ext, _attrs) = &**inner;
        let (ext_name, _payload) = ext;
        arena.get_string(ext_name.txt) == "private"
    } else {
        false
    }
}

fn expand_extensions_item(
    item: &StructureItem,
    arena: &mut ParseArena,
) -> PpxResult<Vec<StructureItem>> {
    match &*item.pstr_desc {
        StructureItemDesc::Pstr_extension(inner) => {
            let (ref ext, ref _attrs) = **inner;
            let (ext_name, payload) = ext;
            let name = arena.get_string(ext_name.txt).to_string();
            if name == "raw" {
                Ok(vec![handle_raw_structure(
                    item,
                    payload,
                    arena,
                    ext_name.loc,
                )])
            } else if name == "private" {
                handle_private_extension(payload, ext_name.loc, arena)
            } else {
                Ok(vec![item.clone()])
            }
        }
        // Recurse into expressions to expand %raw, %re
        StructureItemDesc::Pstr_eval(inner) => {
            let (ref expr_idx, ref attrs) = **inner;
            let expr = arena.get_expr(*expr_idx).clone();
            let new_expr = expand_extensions_expr(&expr, arena);
            let new_expr_idx = arena.push_expr(new_expr);
            Ok(vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((
                    new_expr_idx,
                    attrs.clone(),
                )))),
                pstr_loc: item.pstr_loc,
            }])
        }
        StructureItemDesc::Pstr_value(inner) => {
            let (ref rec, ref bindings) = **inner;
            let new_bindings: Vec<_> = bindings
                .iter()
                .map(|vb| {
                    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
                    let new_expr = expand_extensions_expr(&vb_expr, arena);
                    let new_expr_idx = arena.push_expr(new_expr);
                    crate::parser::ast::ValueBinding {
                        pvb_pat: vb.pvb_pat.clone(),
                        pvb_expr: new_expr_idx,
                        pvb_attributes: vb.pvb_attributes.clone(),
                        pvb_loc: vb.pvb_loc,
                    }
                })
                .collect();
            Ok(vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
                    *rec,
                    new_bindings,
                )))),
                pstr_loc: item.pstr_loc,
            }])
        }
        StructureItemDesc::Pstr_module(mb) => {
            let new_expr_idx = expand_extensions_mod_expr(mb.pmb_expr, arena)?;
            Ok(vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_module(Box::new(
                    crate::parser::ast::ModuleBinding {
                        pmb_name: mb.pmb_name.clone(),
                        pmb_expr: new_expr_idx,
                        pmb_attributes: mb.pmb_attributes.clone(),
                        pmb_loc: mb.pmb_loc,
                    },
                ))),
                pstr_loc: item.pstr_loc,
            }])
        }
        // Keep externals untouched in the lightweight extension pass.
        // FFI encoding and external type reconstruction happen in rewrite_structure_item_no_spice,
        // and must operate on the original type to preserve @as(...) constants in pval_prim.
        StructureItemDesc::Pstr_primitive(_) => Ok(vec![item.clone()]),
        _ => Ok(vec![item.clone()]),
    }
}

fn expand_extensions_expr(expr: &Expression, arena: &mut ParseArena) -> Expression {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_extension(ext) => {
            let (ref ext_name, ref payload) = **ext;
            let name = arena.get_string(ext_name.txt).to_string();
            match name.as_str() {
                "raw" => {
                    let raw_prim = prim_str(arena, "#raw_expr");
                    handle_raw(expr, payload, arena, raw_prim, ext_name.loc)
                }
                "re" => match payload_single_string_literal_with_loc(payload, arena) {
                    Some((code, _loc))
                        if is_js_regex_literal(code) || is_js_regex_like_literal(code) =>
                    {
                        handle_re(expr, payload, arena, ext_name.loc)
                    }
                    Some(_) => expr.clone(),
                    None => handle_re(expr, payload, arena, ext_name.loc),
                },
                _ => expr.clone(),
            }
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (ref rec_flag, ref bindings, ref body) = **inner;
            let new_bindings: Vec<_> = bindings
                .iter()
                .map(|vb| {
                    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
                    let new_expr = expand_extensions_expr(&vb_expr, arena);
                    let new_expr_idx = arena.push_expr(new_expr);
                    crate::parser::ast::ValueBinding {
                        pvb_pat: vb.pvb_pat.clone(),
                        pvb_expr: new_expr_idx,
                        pvb_attributes: vb.pvb_attributes.clone(),
                        pvb_loc: vb.pvb_loc,
                    }
                })
                .collect();
            let body_expr = arena.get_expr(*body).clone();
            let new_body = expand_extensions_expr(&body_expr, arena);
            let new_body_idx = arena.push_expr(new_body);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                    *rec_flag,
                    new_bindings,
                    new_body_idx,
                )))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        ExpressionDesc::Pexp_sequence(e1, e2) => {
            let e1_expr = arena.get_expr(*e1).clone();
            let e2_expr = arena.get_expr(*e2).clone();
            let new_e1 = expand_extensions_expr(&e1_expr, arena);
            let new_e2 = expand_extensions_expr(&e2_expr, arena);
            let new_e1_idx = arena.push_expr(new_e1);
            let new_e2_idx = arena.push_expr(new_e2);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_sequence(new_e1_idx, new_e2_idx)),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        _ => expr.clone(),
    }
}

/// Recursively expand extensions in module expressions (handles functors, structures, etc.)
fn expand_extensions_mod_expr(me_idx: ModExprIdx, arena: &mut ParseArena) -> PpxResult<ModExprIdx> {
    let me = arena.get_mod_expr(me_idx).clone();
    match &*me.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => {
            let new_items = expand_extensions(items, arena)?;
            let new_me = ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(new_items))),
                pmod_loc: me.pmod_loc,
                pmod_attributes: me.pmod_attributes.clone(),
            };
            Ok(arena.push_mod_expr(new_me))
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (ref name, ref mty, ref body) = **inner;
            let new_body_idx = expand_extensions_mod_expr(*body, arena)?;
            let new_me = ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_functor(Box::new((
                    name.clone(),
                    mty.clone(),
                    new_body_idx,
                )))),
                pmod_loc: me.pmod_loc,
                pmod_attributes: me.pmod_attributes.clone(),
            };
            Ok(arena.push_mod_expr(new_me))
        }
        ModuleExprDesc::Pmod_apply(me1, me2) => {
            let new_me1_idx = expand_extensions_mod_expr(*me1, arena)?;
            let new_me2_idx = expand_extensions_mod_expr(*me2, arena)?;
            let new_me = ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_apply(new_me1_idx, new_me2_idx)),
                pmod_loc: me.pmod_loc,
                pmod_attributes: me.pmod_attributes.clone(),
            };
            Ok(arena.push_mod_expr(new_me))
        }
        ModuleExprDesc::Pmod_constraint(inner_idx, mty) => {
            let new_inner_idx = expand_extensions_mod_expr(*inner_idx, arena)?;
            let new_me = ModuleExpr {
                pmod_desc: Box::new(ModuleExprDesc::Pmod_constraint(new_inner_idx, *mty)),
                pmod_loc: me.pmod_loc,
                pmod_attributes: me.pmod_attributes.clone(),
            };
            Ok(arena.push_mod_expr(new_me))
        }
        _ => Ok(me_idx),
    }
}

/// Apply built-in PPX transformations to a signature
pub fn rewrite_signature(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
) -> PpxResult<Vec<SignatureItem>> {
    validate_signature_deriving_errors(signature, arena)?;
    validate_signature_method_attribute_errors(signature, arena)?;
    validate_signature_js_string_errors(signature, arena)?;
    validate_signature_await_errors(signature, arena, true)?;
    let rewritten = try_rewrite_signature_items(signature, arena)?;
    validate_signature_builtin_type_redefinition_errors(&rewritten, arena)?;
    Ok(rewritten)
}

fn try_rewrite_signature_items(
    items: &[SignatureItem],
    arena: &mut ParseArena,
) -> PpxResult<Vec<SignatureItem>> {
    let mut rewritten = Vec::new();
    let spice_mapper_active = spice_ppx::signature_uses_spice_mapper(items, arena);
    for item in items {
        let expanded_items =
            spice_ppx::expand_signature_item_with_mapper(item, arena, spice_mapper_active)
                .map_err(PpxError::message)?;
        for expanded in expanded_items {
            if let SignatureItemDesc::Psig_value(vd) = &*expanded.psig_desc {
                validate_external_attribute_errors(vd, arena)?;
            }
            let rewritten_item = rewrite_signature_item_no_spice(&expanded, arena);
            rewritten.extend(expand_signature_deriving_items(
                &expanded,
                rewritten_item,
                arena,
            ));
        }
    }
    Ok(rewritten)
}

fn rewrite_signature_items(items: &[SignatureItem], arena: &mut ParseArena) -> Vec<SignatureItem> {
    try_rewrite_signature_items(items, arena).unwrap_or_else(|_| {
        items
            .iter()
            .flat_map(|item| {
                let rewritten_item = rewrite_signature_item_no_spice(item, arena);
                expand_signature_deriving_items(item, rewritten_item, arena)
            })
            .collect()
    })
}

fn expand_signature_deriving_items(
    original: &SignatureItem,
    rewritten: SignatureItem,
    arena: &mut ParseArena,
) -> Vec<SignatureItem> {
    let SignatureItemDesc::Psig_type(inner) = &*original.psig_desc else {
        return vec![rewritten];
    };
    let (_rec_flag, tdcls) = &**inner;
    let Some(last_tdcl) = tdcls.last() else {
        return vec![rewritten];
    };
    let (actions, _remaining_attrs) = parse_deriving_actions(&last_tdcl.ptype_attributes, arena);
    if !actions
        .iter()
        .any(|action| matches!(action, DeriveAction::Accessors))
    {
        return vec![rewritten];
    }

    let mut items = vec![rewritten];
    for tdcl in tdcls.iter() {
        if let Some((_structure_items, signature_items)) =
            generate_accessor_items_for_tdcl(tdcl, tdcl.ptype_loc, arena)
        {
            items.extend(signature_items);
        }
    }
    items
}

fn try_rewrite_structure_item(
    item: &StructureItem,
    arena: &mut ParseArena,
    spice_mapper_active: bool,
) -> PpxResult<Vec<StructureItem>> {
    let mut result = Vec::new();
    for expanded in spice_ppx::expand_structure_item_with_mapper(item, arena, spice_mapper_active)
        .map_err(PpxError::message)?
    {
        if let StructureItemDesc::Pstr_primitive(vd) = &*expanded.pstr_desc {
            validate_external_attribute_errors(vd, arena)?;
        }
        result.extend(rewrite_structure_item_no_spice(&expanded, arena));
    }
    Ok(result)
}

/// Rewrite a structure item, potentially returning multiple items for @deriving.
fn rewrite_structure_item(item: &StructureItem, arena: &mut ParseArena) -> Vec<StructureItem> {
    let spice_mapper_active =
        spice_ppx::structure_uses_spice_mapper(std::slice::from_ref(item), arena);
    try_rewrite_structure_item(item, arena, spice_mapper_active)
        .unwrap_or_else(|_| rewrite_structure_item_no_spice(item, arena))
}

fn rewrite_structure_item_no_spice(
    item: &StructureItem,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    match &*item.pstr_desc {
        StructureItemDesc::Pstr_primitive(vd) => {
            if is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
                // OCaml rewrites attributes (e.g. "js" -> "*j" in strings) before
                // encoding the external (ast_external.ml line 59).
                let rewritten_attrs = rewrite_attributes(&vd.pval_attributes, arena);
                // Rewrite the type to transform string delimiters in @as attributes
                let vd_type = arena.get_core_type(vd.pval_type).clone();
                let rewritten_type = rewrite_core_type(&vd_type, arena);
                let rewritten_vd = ValueDescription {
                    pval_name: vd.pval_name.clone(),
                    pval_type: arena.push_core_type(rewritten_type.clone()),
                    pval_prim: vd.pval_prim.clone(),
                    pval_attributes: rewritten_attrs.into(),
                    pval_loc: vd.pval_loc,
                };

                // Check if FFI has relative paths before encoding
                // (need to build FFI type to check, same as encode_external does)
                let no_inline = check_external_relative(&rewritten_vd, arena);

                let encoded = encode_external(&rewritten_vd, arena);
                // OCaml's FFI processing (ast_external_process.ml handle_attributes)
                // reconstructs the arrow type with ptyp_loc = pval_loc.
                // For @obj externals, also reconstructs Ptyp_any -> Ptyp_object.
                let pval_type =
                    process_obj_type(&rewritten_type, vd.pval_loc, &vd.pval_attributes, arena);
                let external_result = StructureItem {
                    pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(
                        ValueDescription {
                            pval_prim: encoded.pval_prim,
                            pval_attributes: encoded.pval_attributes.clone().into(),
                            pval_name: vd.pval_name.clone(),
                            pval_type: arena.push_core_type(pval_type.clone()),
                            pval_loc: vd.pval_loc,
                        },
                    ))),
                    pstr_loc: item.pstr_loc,
                };

                if no_inline {
                    // Wrap in Pstr_include to prevent cross-module inlining
                    // of relative path externals (ast_external.ml lines 78-98)
                    let loc = vd.pval_loc;
                    let sig_value = ValueDescription {
                        pval_name: vd.pval_name.clone(),
                        pval_type: arena.push_core_type(pval_type.clone()),
                        pval_prim: vec![],
                        pval_attributes: encoded.pval_attributes.clone().into(),
                        pval_loc: vd.pval_loc,
                    };
                    let inner_mod_idx = arena.push_mod_expr(ModuleExpr {
                        pmod_desc: Box::new(ModuleExprDesc::Pmod_structure(Box::new(vec![
                            external_result,
                        ]))),
                        pmod_loc: loc,
                        pmod_attributes: Attributes::new(),
                    });
                    let sig_mod_type_idx = arena.push_mod_type(ModuleType {
                        pmty_desc: Box::new(ModuleTypeDesc::Pmty_signature(Box::new(vec![
                            SignatureItem {
                                psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(
                                    sig_value,
                                ))),
                                psig_loc: loc,
                            },
                        ]))),
                        pmty_loc: loc,
                        pmty_attributes: Attributes::new(),
                    });
                    let constrained_idx = arena.push_mod_expr(ModuleExpr {
                        pmod_desc: Box::new(ModuleExprDesc::Pmod_constraint(
                            inner_mod_idx,
                            sig_mod_type_idx,
                        )),
                        pmod_loc: loc,
                        pmod_attributes: Attributes::new(),
                    });
                    vec![StructureItem {
                        pstr_desc: Box::new(StructureItemDesc::Pstr_include(Box::new(
                            IncludeDeclaration {
                                pincl_mod: constrained_idx,
                                pincl_loc: loc,
                                pincl_attributes: Attributes::new(),
                            },
                        ))),
                        pstr_loc: loc,
                    }]
                } else {
                    vec![external_result]
                }
            } else {
                // Non-ReScript externals still need attribute and type rewriting
                // (e.g. "js" -> "*j" in @ocaml.doc string delimiters and @as attributes in types)
                let vd_type = arena.get_core_type(vd.pval_type).clone();
                let rewritten_type = rewrite_core_type(&vd_type, arena);
                vec![StructureItem {
                    pstr_desc: Box::new(StructureItemDesc::Pstr_primitive(Box::new(
                        ValueDescription {
                            pval_name: vd.pval_name.clone(),
                            pval_type: arena.push_core_type(rewritten_type),
                            pval_prim: vd.pval_prim.clone(),
                            pval_attributes: rewrite_attributes(&vd.pval_attributes, arena).into(),
                            pval_loc: vd.pval_loc,
                        },
                    ))),
                    pstr_loc: item.pstr_loc,
                }]
            }
        }
        // Handle value bindings - need to rewrite expressions and patterns
        // Also handle @inline transformation
        StructureItemDesc::Pstr_value(inner) => {
            let (ref rec_flag, ref bindings) = **inner;
            // Check for @inline on a single non-recursive let binding
            if *rec_flag == RecFlag::Nonrecursive && bindings.len() == 1 {
                let vb = &bindings[0];
                let maybe_pval_name = match &*arena.get_pat(vb.pvb_pat).ppat_desc {
                    PatternDesc::Ppat_var(pval_name) => Some(pval_name.clone()),
                    _ => None,
                };
                // Check if pattern is a simple variable
                if let Some(pval_name) = maybe_pval_name {
                    // Rewrite expression first to get string transformation
                    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
                    let pvb_expr = rewrite_expression(&vb_expr, arena);

                    // Check for @inline attribute
                    if has_inline_attr(&vb.pvb_attributes, arena) {
                        // Transform based on the expression type
                        if let Some(prim_item) = transform_inline_binding(
                            &pval_name,
                            &pvb_expr,
                            vb.pvb_loc,
                            item.pstr_loc,
                            arena,
                        ) {
                            return vec![prim_item];
                        }
                    }

                    // No @inline or couldn't transform - return rewritten binding
                    let original_pat = arena.get_pat(vb.pvb_pat).clone();
                    let rewritten_pat = rewrite_pattern(&original_pat, arena);
                    return vec![StructureItem {
                        pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
                            *rec_flag,
                            vec![ValueBinding {
                                pvb_expr: arena.push_expr(pvb_expr),
                                pvb_pat: arena.push_pat(rewritten_pat),
                                pvb_attributes: rewrite_attributes(&vb.pvb_attributes, arena)
                                    .into(),
                                pvb_loc: vb.pvb_loc,
                            }],
                        )))),
                        pstr_loc: item.pstr_loc,
                    }];
                }
            }

            // Default case: rewrite all bindings. Recursive bindings must keep
            // their original patterns so Typecore can raise Illegal_letrec_pat,
            // matching OCaml.
            let new_bindings = if *rec_flag == RecFlag::Recursive {
                rewrite_value_bindings_without_flattening(bindings, arena)
            } else {
                flatten_value_bindings(bindings, arena)
            };
            vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((
                    *rec_flag,
                    new_bindings,
                )))),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Handle eval expressions
        StructureItemDesc::Pstr_eval(inner) => {
            let (ref expr, ref attrs) = **inner;
            let expr_owned = arena.get_expr(*expr).clone();
            let rewritten_expr = rewrite_expression(&expr_owned, arena);
            vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((
                    arena.push_expr(rewritten_expr),
                    rewrite_attributes(attrs, arena).into(),
                )))),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Module - recurse into module structure.
        // Module-level @res.await transformation is handled in rewrite_structure.
        StructureItemDesc::Pstr_module(mb) => {
            let mb_expr = arena.get_mod_expr(mb.pmb_expr).clone();
            let rewritten_mb_expr = rewrite_module_expr(&mb_expr, arena);
            vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_module(Box::new(
                    current::ModuleBinding {
                        pmb_name: mb.pmb_name.clone(),
                        pmb_expr: arena.push_mod_expr(rewritten_mb_expr),
                        pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena).into(),
                        pmb_loc: mb.pmb_loc,
                    },
                ))),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Recursive modules
        StructureItemDesc::Pstr_recmodule(mbs) => {
            let new_mbs = mbs
                .iter()
                .map(|mb| {
                    let mb_expr = arena.get_mod_expr(mb.pmb_expr).clone();
                    let rewritten_mb_expr = rewrite_module_expr(&mb_expr, arena);
                    current::ModuleBinding {
                        pmb_name: mb.pmb_name.clone(),
                        pmb_expr: arena.push_mod_expr(rewritten_mb_expr),
                        pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena).into(),
                        pmb_loc: mb.pmb_loc,
                    }
                })
                .collect();
            vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_recmodule(Box::new(new_mbs))),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Include - recurse into module expression
        StructureItemDesc::Pstr_include(incl) => {
            let incl_mod = arena.get_mod_expr(incl.pincl_mod).clone();
            let rewritten_incl_mod = rewrite_module_expr(&incl_mod, arena);
            vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_include(Box::new(
                    current::IncludeDeclaration {
                        pincl_mod: arena.push_mod_expr(rewritten_incl_mod),
                        pincl_loc: incl.pincl_loc,
                        pincl_attributes: rewrite_attributes(&incl.pincl_attributes, arena).into(),
                    },
                ))),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Handle structure-level extensions (%%raw, %%private)
        StructureItemDesc::Pstr_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            let (ext_name, payload) = ext;
            let name = arena.get_string(ext_name.txt);
            if name == "raw" {
                // %%raw("...") -> Pstr_eval with local_external_apply using #raw_stmt
                // OCaml: loc comes from {txt = "raw"; loc} - extension identifier location
                vec![handle_raw_structure(item, payload, arena, ext_name.loc)]
            } else if name == "private" {
                // %%private(let x = ...) -> module local_N = { let x = ... } ; open! local_N
                handle_private_extension(payload, ext_name.loc, arena).unwrap_or_default()
            } else {
                // Rewrite payload for string transformation
                vec![StructureItem {
                    pstr_desc: Box::new(StructureItemDesc::Pstr_extension(Box::new((
                        (ext_name.clone(), rewrite_payload(payload, arena)),
                        rewrite_attributes(attrs, arena).into(),
                    ))))
                    .into(),
                    pstr_loc: item.pstr_loc,
                }]
            }
        }
        // Handle floating attributes (@@attr) - need to transform strings in payload
        StructureItemDesc::Pstr_attribute(attr) => {
            vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_attribute(Box::new(
                    rewrite_attribute(attr, arena),
                ))),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Handle type declarations with @deriving
        StructureItemDesc::Pstr_type(inner) => {
            let (ref rec_flag, ref tdcls) = **inner;
            handle_deriving_type(item, *rec_flag, tdcls, arena)
        }
        // Handle open - rewrite attributes
        StructureItemDesc::Pstr_open(od) => vec![StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_open(Box::new(
                current::OpenDescription {
                    popen_lid: od.popen_lid.clone(),
                    popen_override: od.popen_override,
                    popen_loc: od.popen_loc,
                    popen_attributes: rewrite_attributes(&od.popen_attributes, arena).into(),
                },
            ))),
            pstr_loc: item.pstr_loc,
        }],
        // Handle modtype - rewrite attributes
        StructureItemDesc::Pstr_modtype(mtd) => {
            let pmtd_type = mtd.pmtd_type.as_ref().map(|mt| {
                let mt_owned = arena.get_mod_type(*mt).clone();
                let rewritten_mt = rewrite_module_type(&mt_owned, arena);
                arena.push_mod_type(rewritten_mt)
            });
            vec![StructureItem {
                pstr_desc: Box::new(StructureItemDesc::Pstr_modtype(Box::new(
                    current::ModuleTypeDeclaration {
                        pmtd_name: mtd.pmtd_name.clone(),
                        pmtd_type,
                        pmtd_attributes: rewrite_attributes(&mtd.pmtd_attributes, arena).into(),
                        pmtd_loc: mtd.pmtd_loc,
                    },
                ))),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Handle exception - rewrite attributes
        StructureItemDesc::Pstr_exception(ec) => vec![StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_exception(Box::new(
                current::ExtensionConstructor {
                    pext_name: ec.pext_name.clone(),
                    pext_kind: ec.pext_kind.clone(),
                    pext_loc: ec.pext_loc,
                    pext_attributes: rewrite_attributes(&ec.pext_attributes, arena).into(),
                },
            ))),
            pstr_loc: item.pstr_loc,
        }],
        // Handle type extension - rewrite attributes
        StructureItemDesc::Pstr_typext(te) => vec![StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_typext(Box::new(
                current::TypeExtension {
                    ptyext_path: te.ptyext_path.clone(),
                    ptyext_params: te.ptyext_params.clone(),
                    ptyext_constructors: te
                        .ptyext_constructors
                        .iter()
                        .map(|ec| current::ExtensionConstructor {
                            pext_name: ec.pext_name.clone(),
                            pext_kind: ec.pext_kind.clone(),
                            pext_loc: ec.pext_loc,
                            pext_attributes: rewrite_attributes(&ec.pext_attributes, arena).into(),
                        })
                        .collect(),
                    ptyext_private: te.ptyext_private,
                    ptyext_attributes: rewrite_attributes(&te.ptyext_attributes, arena).into(),
                },
            ))),
            pstr_loc: item.pstr_loc,
        }],
    }
}

/// Rewrite a module expression, recursing into structure
fn rewrite_module_expr(
    mod_expr: &current::ModuleExpr,
    arena: &mut ParseArena,
) -> current::ModuleExpr {
    let new_desc = match &*mod_expr.pmod_desc {
        current::ModuleExprDesc::Pmod_structure(items) => {
            let rewritten_items = rewrite_structure(items, arena).unwrap_or_else(|_| {
                items
                    .iter()
                    .flat_map(|item| rewrite_structure_item(item, arena))
                    .collect()
            });
            current::ModuleExprDesc::Pmod_structure(Box::new(rewritten_items))
        }
        current::ModuleExprDesc::Pmod_functor(inner) => {
            let (ref param, ref mod_type, ref body) = **inner;
            let rewritten_mod_type = mod_type.map(|mt_idx| {
                let mt = arena.get_mod_type(mt_idx).clone();
                let rw = rewrite_module_type(&mt, arena);
                arena.push_mod_type(rw)
            });
            let body_me = arena.get_mod_expr(*body).clone();
            let rw_body = rewrite_module_expr(&body_me, arena);
            current::ModuleExprDesc::Pmod_functor(Box::new((
                param.clone(),
                rewritten_mod_type,
                arena.push_mod_expr(rw_body),
            )))
        }
        current::ModuleExprDesc::Pmod_apply(m1, m2) => {
            let m1_me = arena.get_mod_expr(*m1).clone();
            let m2_me = arena.get_mod_expr(*m2).clone();
            let rw1 = rewrite_module_expr(&m1_me, arena);
            let rw2 = rewrite_module_expr(&m2_me, arena);
            current::ModuleExprDesc::Pmod_apply(arena.push_mod_expr(rw1), arena.push_mod_expr(rw2))
        }
        current::ModuleExprDesc::Pmod_constraint(m, mt) => {
            let m_me = arena.get_mod_expr(*m).clone();
            let mt_mt = arena.get_mod_type(*mt).clone();
            let rw_m = rewrite_module_expr(&m_me, arena);
            let rw_mt = rewrite_module_type(&mt_mt, arena);
            current::ModuleExprDesc::Pmod_constraint(
                arena.push_mod_expr(rw_m),
                arena.push_mod_type(rw_mt),
            )
        }
        // Handle module extension - rewrite payload
        current::ModuleExprDesc::Pmod_extension(ext) => {
            let (ref ext_name, ref payload) = **ext;
            current::ModuleExprDesc::Pmod_extension(Box::new((
                ext_name.clone(),
                rewrite_payload(payload, arena),
            )))
        }
        // Ident, unpack - just clone
        _ => return mod_expr.clone(),
    };

    current::ModuleExpr {
        pmod_desc: Box::new(new_desc),
        pmod_loc: mod_expr.pmod_loc,
        pmod_attributes: rewrite_attributes(&mod_expr.pmod_attributes, arena).into(),
    }
}

/// Rewrite a module type, recursing into signature and nested module types
fn rewrite_module_type(
    mod_type: &current::ModuleType,
    arena: &mut ParseArena,
) -> current::ModuleType {
    let new_desc = match &*mod_type.pmty_desc {
        current::ModuleTypeDesc::Pmty_signature(items) => {
            current::ModuleTypeDesc::Pmty_signature(Box::new(rewrite_signature_items(items, arena)))
        }
        current::ModuleTypeDesc::Pmty_functor(inner) => {
            let (ref name, ref param_type, ref result_type) = **inner;
            let rewritten_param = param_type.map(|pt_idx| {
                let pt = arena.get_mod_type(pt_idx).clone();
                let rw = rewrite_module_type(&pt, arena);
                arena.push_mod_type(rw)
            });
            let result_mt = arena.get_mod_type(*result_type).clone();
            let rw_result = rewrite_module_type(&result_mt, arena);
            current::ModuleTypeDesc::Pmty_functor(Box::new((
                name.clone(),
                rewritten_param,
                arena.push_mod_type(rw_result),
            )))
        }
        current::ModuleTypeDesc::Pmty_with(inner) => {
            let (ref mt_idx, ref constraints) = **inner;
            let mt = arena.get_mod_type(*mt_idx).clone();
            let rw = rewrite_module_type(&mt, arena);
            current::ModuleTypeDesc::Pmty_with(Box::new((
                arena.push_mod_type(rw),
                constraints.clone(),
            )))
        }
        current::ModuleTypeDesc::Pmty_typeof(me_idx) => {
            let me = arena.get_mod_expr(*me_idx).clone();
            let rw = rewrite_module_expr(&me, arena);
            current::ModuleTypeDesc::Pmty_typeof(arena.push_mod_expr(rw))
        }
        current::ModuleTypeDesc::Pmty_extension(ext) => {
            let (ref ext_name, ref payload) = **ext;
            current::ModuleTypeDesc::Pmty_extension(Box::new((
                ext_name.clone(),
                rewrite_payload(payload, arena),
            )))
        }
        // Ident, Alias - just return as-is (will be wrapped with rewritten attributes)
        _ => {
            return current::ModuleType {
                pmty_desc: mod_type.pmty_desc.clone(),
                pmty_loc: mod_type.pmty_loc,
                pmty_attributes: rewrite_attributes(&mod_type.pmty_attributes, arena).into(),
            };
        }
    };

    current::ModuleType {
        pmty_desc: Box::new(new_desc),
        pmty_loc: mod_type.pmty_loc,
        pmty_attributes: rewrite_attributes(&mod_type.pmty_attributes, arena).into(),
    }
}

fn rewrite_signature_item_no_spice(item: &SignatureItem, arena: &mut ParseArena) -> SignatureItem {
    match &*item.psig_desc {
        SignatureItemDesc::Psig_value(vd) => {
            // OCaml rewrites attributes (e.g. "js" -> "*j" in strings) before
            // encoding the external (ast_external.ml handle_external_in_sig,
            // bs_builtin_ppx.ml line 409).
            let rewritten_attrs = rewrite_attributes(&vd.pval_attributes, arena);
            if is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
                // OCaml runs type mapping before external encoding.
                let vd_type = arena.get_core_type(vd.pval_type).clone();
                let rewritten_type = rewrite_core_type(&vd_type, arena);
                let rewritten_vd = ValueDescription {
                    pval_name: vd.pval_name.clone(),
                    pval_type: arena.push_core_type(rewritten_type.clone()),
                    pval_prim: vd.pval_prim.clone(),
                    pval_attributes: rewritten_attrs.into(),
                    pval_loc: vd.pval_loc,
                };
                let encoded = encode_external(&rewritten_vd, arena);
                // OCaml's FFI processing reconstructs the arrow type with ptyp_loc = pval_loc
                // For @obj externals, also reconstructs Ptyp_any -> Ptyp_object.
                let pval_type =
                    process_obj_type(&rewritten_type, vd.pval_loc, &vd.pval_attributes, arena);
                SignatureItem {
                    psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(
                        ValueDescription {
                            pval_prim: encoded.pval_prim,
                            pval_attributes: encoded.pval_attributes.into(),
                            pval_name: vd.pval_name.clone(),
                            pval_type: arena.push_core_type(pval_type),
                            pval_loc: vd.pval_loc,
                        },
                    ))),
                    psig_loc: item.psig_loc,
                }
            } else if let Some(inline_vd) = transform_inline_sig_value(vd, arena) {
                // Handle @inline("value") let x: t in signature
                // (bs_builtin_ppx.ml line 413-478)
                SignatureItem {
                    psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(inline_vd))),
                    psig_loc: item.psig_loc,
                }
            } else {
                SignatureItem {
                    psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(
                        ValueDescription {
                            pval_name: vd.pval_name.clone(),
                            pval_type: vd.pval_type.clone(),
                            pval_prim: vd.pval_prim.clone(),
                            pval_attributes: rewritten_attrs.into(),
                            pval_loc: vd.pval_loc,
                        },
                    ))),
                    psig_loc: item.psig_loc,
                }
            }
        }
        // Handle floating attributes (@@attr) - need to transform strings in payload
        SignatureItemDesc::Psig_attribute(attr) => SignatureItem {
            psig_desc: Box::new(SignatureItemDesc::Psig_attribute(Box::new(
                rewrite_attribute(attr, arena),
            ))),
            psig_loc: item.psig_loc,
        },
        // Handle extensions - need to transform strings in payload
        SignatureItemDesc::Psig_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            let (ext_name, payload) = ext;
            SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_extension(Box::new((
                    (ext_name.clone(), rewrite_payload(payload, arena)),
                    rewrite_attributes(attrs, arena).into(),
                ))))
                .into(),
                psig_loc: item.psig_loc,
            }
        }
        // Handle open - rewrite attributes
        SignatureItemDesc::Psig_open(od) => SignatureItem {
            psig_desc: Box::new(SignatureItemDesc::Psig_open(Box::new(
                current::OpenDescription {
                    popen_lid: od.popen_lid.clone(),
                    popen_override: od.popen_override,
                    popen_loc: od.popen_loc,
                    popen_attributes: rewrite_attributes(&od.popen_attributes, arena).into(),
                },
            ))),
            psig_loc: item.psig_loc,
        },
        // Handle modtype - rewrite attributes and module type
        SignatureItemDesc::Psig_modtype(mtd) => {
            let pmtd_type = mtd.pmtd_type.as_ref().map(|mt| {
                let mt_owned = arena.get_mod_type(*mt).clone();
                let rewritten_mt = rewrite_module_type(&mt_owned, arena);
                arena.push_mod_type(rewritten_mt)
            });
            SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_modtype(Box::new(
                    current::ModuleTypeDeclaration {
                        pmtd_name: mtd.pmtd_name.clone(),
                        pmtd_type,
                        pmtd_attributes: rewrite_attributes(&mtd.pmtd_attributes, arena).into(),
                        pmtd_loc: mtd.pmtd_loc,
                    },
                ))),
                psig_loc: item.psig_loc,
            }
        }
        // Handle exception - rewrite attributes
        SignatureItemDesc::Psig_exception(ec) => SignatureItem {
            psig_desc: Box::new(SignatureItemDesc::Psig_exception(Box::new(
                current::ExtensionConstructor {
                    pext_name: ec.pext_name.clone(),
                    pext_kind: ec.pext_kind.clone(),
                    pext_loc: ec.pext_loc,
                    pext_attributes: rewrite_attributes(&ec.pext_attributes, arena).into(),
                },
            ))),
            psig_loc: item.psig_loc,
        },
        // Handle type extension - rewrite attributes
        SignatureItemDesc::Psig_typext(te) => SignatureItem {
            psig_desc: Box::new(SignatureItemDesc::Psig_typext(Box::new(
                current::TypeExtension {
                    ptyext_path: te.ptyext_path.clone(),
                    ptyext_params: te.ptyext_params.clone(),
                    ptyext_constructors: te
                        .ptyext_constructors
                        .iter()
                        .map(|ec| current::ExtensionConstructor {
                            pext_name: ec.pext_name.clone(),
                            pext_kind: ec.pext_kind.clone(),
                            pext_loc: ec.pext_loc,
                            pext_attributes: rewrite_attributes(&ec.pext_attributes, arena).into(),
                        })
                        .collect(),
                    ptyext_private: te.ptyext_private,
                    ptyext_attributes: rewrite_attributes(&te.ptyext_attributes, arena).into(),
                },
            ))),
            psig_loc: item.psig_loc,
        },
        // Handle type declarations - rewrite attributes (including constructor/label attributes)
        SignatureItemDesc::Psig_type(inner) => {
            let (ref rec_flag, ref tdcls) = **inner;
            let rewritten_tdcls: Vec<TypeDeclaration> = tdcls
                .iter()
                .map(|tdcl| rewrite_type_declaration(tdcl, arena))
                .collect();
            SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_type(Box::new((
                    *rec_flag,
                    rewritten_tdcls,
                )))),
                psig_loc: item.psig_loc,
            }
        }
        // Handle include - recurse into module type
        SignatureItemDesc::Psig_include(incl) => {
            let incl_mod = arena.get_mod_type(incl.pincl_mod).clone();
            let rewritten_incl_mod = rewrite_module_type(&incl_mod, arena);
            SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_include(Box::new(
                    current::IncludeDescription {
                        pincl_mod: arena.push_mod_type(rewritten_incl_mod),
                        pincl_loc: incl.pincl_loc,
                        pincl_attributes: rewrite_attributes(&incl.pincl_attributes, arena).into(),
                    },
                ))),
                psig_loc: item.psig_loc,
            }
        }
        // Handle module - recurse into module type
        SignatureItemDesc::Psig_module(md) => {
            let mod_type = arena.get_mod_type(md.pmd_type).clone();
            let rewritten_mod_type = rewrite_module_type(&mod_type, arena);
            SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_module(Box::new(
                    current::ModuleDeclaration {
                        pmd_name: md.pmd_name.clone(),
                        pmd_type: arena.push_mod_type(rewritten_mod_type),
                        pmd_attributes: rewrite_attributes(&md.pmd_attributes, arena).into(),
                        pmd_loc: md.pmd_loc,
                    },
                ))),
                psig_loc: item.psig_loc,
            }
        }
        // Handle recursive modules - recurse into module types
        SignatureItemDesc::Psig_recmodule(mds) => {
            let new_mds = mds
                .iter()
                .map(|md| {
                    let mod_type = arena.get_mod_type(md.pmd_type).clone();
                    let rewritten_mod_type = rewrite_module_type(&mod_type, arena);
                    current::ModuleDeclaration {
                        pmd_name: md.pmd_name.clone(),
                        pmd_type: arena.push_mod_type(rewritten_mod_type),
                        pmd_attributes: rewrite_attributes(&md.pmd_attributes, arena).into(),
                        pmd_loc: md.pmd_loc,
                    }
                })
                .collect();
            SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_recmodule(Box::new(new_mds))),
                psig_loc: item.psig_loc,
            }
        } // All SignatureItemDesc variants are covered above
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_first_char_special() {
        assert!(first_char_special("#foo"));
        assert!(first_char_special("?foo"));
        assert!(first_char_special("%foo"));
        assert!(!first_char_special("foo"));
        assert!(!first_char_special(""));
    }

    #[test]
    fn test_prims_to_be_encoded() {
        use crate::parse_arena::ParseArena;
        let mut arena = ParseArena::new();
        let console_log = arena.intern("console.log");
        let foo = arena.intern("#foo");
        assert!(prims_to_be_encoded(&[console_log], &arena));
        assert!(!prims_to_be_encoded(&[foo], &arena));
        assert!(!prims_to_be_encoded(&[], &arena));
    }

    #[test]
    fn test_classify_js_exp_preserves_single_leading_literal_comment_like_ocaml() {
        assert_eq!(
            classify_js_exp("/*hello*/ 0"),
            JsExpClassification::JsLiteral {
                comment: Some("/*hello*/".to_string()),
            }
        );
        assert_eq!(
            classify_js_exp("//eslint-disable\n0"),
            JsExpClassification::JsLiteral {
                comment: Some("//eslint-disable".to_string()),
            }
        );
    }

    #[test]
    fn test_classify_js_exp_discards_multiple_leading_literal_comments_like_ocaml() {
        assert_eq!(
            classify_js_exp("/*a*/ /*b*/ 0"),
            JsExpClassification::JsLiteral { comment: None }
        );
    }

    #[test]
    fn test_classify_parenthesized_raw_object_literal_like_ocaml() {
        assert_eq!(
            classify_js_exp("({kind: \"app.created\"})"),
            JsExpClassification::JsLiteral { comment: None }
        );
    }
}
