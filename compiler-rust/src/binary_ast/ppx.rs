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

use std::fmt;

use crate::diagnostics::{Warning, WarningConfig};
use crate::intern::StrIdx;

mod check;
use crate::parse_arena::{
    CoreTypeIdx, ExprIdx, LidentIdx, LocIdx, Located, ModExprIdx, ModTypeIdx, ParseArena, PatIdx,
};
use crate::parser::ast::{
    self as current, ArgLabel, Attribute, Attributes, Case, Constant, ConstructorArguments,
    ConstructorDeclaration, CoreType, CoreTypeDesc, DictEntry, DictPatternEntry, Expression,
    ExpressionDesc, ExpressionRecordField, ExtensionConstructor, ExtensionConstructorKind,
    FunParam, IncludeDeclaration, JsxContainerElement, JsxElement, JsxFragment, JsxProp,
    JsxUnaryElement, LabelDeclaration, ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeDesc,
    ObjectField, Pattern, PatternDesc, PatternRecordField, Payload, PexpApply, PexpFun, RecFlag,
    RowField, SignatureItem, SignatureItemDesc, StructureItem, StructureItemDesc, TypeArg,
    TypeDeclaration, TypeExtension, TypeKind, ValueBinding, ValueDescription, WithConstraint,
};
use crate::parser::longident::Longident;

use super::derive;
use crate::parser::ast::{
    Extension, PexpBraces, PexpRaw, PrimitiveRepr, PstrRaw, RawKind, RawSource, SpreadElement,
};
use crate::types::external_ffi_types::{
    Attr, Cst, DeclKind, ExternalDecl, ExternalFfi, ExternalModuleName, ImportAttributes,
    InlineConst, Label, LabelNoname, ModuleBindName, ModuleSource, ObjParam, Param, ReturnWrapper,
};

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

/// Error for `@deriving(accessors)` on a variant with an inline record argument.
pub const ACCESSORS_VARIANT_RECORD_ARG_ERROR: &str = "@deriving(accessors) from a variant record argument is unsupported. Either define the record type separately from the variant type or use a positional argument.";
/// Error for `await` outside an `async` function.
pub const AWAIT_NOT_ASYNC_CONTEXT_ERROR: &str = "Await on expression not in an async context";

/// A warning raised by the builtin PPX.
#[derive(Debug, Clone)]
pub struct PpxWarning {
    /// Where the warning is reported.
    pub loc: LocIdx,
    /// The warning.
    pub warning: Warning,
}

/// A `@@warning` or `@@warnerror` attribute's specification string.
#[derive(Debug, Clone)]
pub struct WarningAttributeSpec {
    /// The specification, such as `"-27+32"`.
    pub spec: String,
    /// Whether it came from `@@warnerror`, which turns the warnings into errors.
    pub as_error: bool,
}

/// A fatal builtin PPX error, with any warnings raised before it.
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

    pub(crate) fn at_loc(loc: LocIdx, message: impl Into<String>) -> Self {
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

    /// Where the error is reported, if it has a location.
    pub fn loc(&self) -> Option<LocIdx> {
        self.loc
    }

    /// The error message.
    pub fn message_text(&self) -> &str {
        &self.message
    }

    /// Warnings raised before the error, to report alongside it.
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

/// Result of a builtin PPX transformation.
pub type PpxResult<T> = Result<T, PpxError>;

/// Check if the first char of a string is special (OCaml FFI marker)
fn first_char_special(s: &str) -> bool {
    matches!(s.chars().next(), Some('#' | '?' | '%'))
}

fn prim_str(arena: &mut ParseArena, s: impl Into<String>) -> StrIdx {
    arena.push_string(s.into())
}

/// `Ast_attributes.prim_to_be_encoded`.
fn prim_to_be_encoded(name: &str) -> bool {
    !first_char_special(name)
}

/// Check if an external declaration has ReScript FFI attributes
fn has_external_attrs(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _payload)| {
        let name = arena.get_string(attr_name.txt);
        EXTERNAL_ATTRS.contains(&name)
    })
}

/// `Ast_attributes.rs_externals`: does a value description need digesting as
/// a ReScript external? A `val` (`None`) or an already-digested external
/// does not.
pub fn is_rs_external(
    attrs: &[Attribute],
    pval_prim: &Option<PrimitiveRepr>,
    arena: &ParseArena,
) -> bool {
    let Some(PrimitiveRepr::PrimName(name)) = pval_prim else {
        return false;
    };
    has_external_attrs(attrs, arena) || prim_to_be_encoded(arena.get_string(*name))
}

/// Check if attributes contain @obj
fn has_obj_attr(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _)| {
        let name = arena.get_string(attr_name.txt);
        name == "obj"
    })
}

/// `Bs_syntaxerr` `Experimental_feature_not_enabled LetUnwrap`
/// (bs_syntaxerr.ml:89-93).
const LET_UNWRAP_NOT_ENABLED_ERROR: &str = "Experimental feature not enabled: LetUnwrap. Enable it by setting \"LetUnwrap\" to true under \"experimental-features\" in rescript.json.";
/// `Bs_syntaxerr` `LetUnwrap_not_supported_in_position `Toplevel`
/// (bs_syntaxerr.ml:95-97).
const LET_UNWRAP_TOPLEVEL_ERROR: &str = "`let?` is not allowed for top-level bindings.";
/// `Bs_syntaxerr` `LetUnwrap_not_supported_in_position `Unsupported_type`
/// (bs_syntaxerr.ml:98-100).
const LET_UNWRAP_UNSUPPORTED_TYPE_ERROR: &str =
    "`let?` is only supported in let bindings targeting the `result` or `option` type.";

/// Check if attributes contain @let.unwrap.
fn has_unwrap_attr(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs
        .iter()
        .any(|(attr_name, _)| arena.get_string(attr_name.txt) == "let.unwrap")
}

/// Conservative variable extraction used by OCaml's Ast_pat helper.
/// Returns the pattern's own name StrIdx so desugaring can reuse the same
/// string object, matching OCaml marshal identity.
fn single_var_pattern_name_conservative(pat: &Pattern, arena: &ParseArena) -> Option<StrIdx> {
    match &pat.ppat_desc {
        PatternDesc::Ppat_any => Some(arena.static_empty_str()),
        PatternDesc::Ppat_var(name) => Some(name.txt),
        PatternDesc::Ppat_alias(inner, alias_name) => {
            if single_var_pattern_name_conservative(arena.get_pat(*inner), arena).is_some() {
                Some(alias_name.txt)
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
) -> Option<(LetUnwrapVariant, StrIdx)> {
    let PatternDesc::Ppat_construct(ctor_lid, payload) = &pat.ppat_desc else {
        return None;
    };
    let Longident::Lident(ctor_name_idx) = arena.get_longident(ctor_lid.txt) else {
        return None;
    };
    let ctor_name = arena.get_string(*ctor_name_idx);

    let variant = match (ctor_name, !payload.txt.is_empty()) {
        ("Ok", true) => LetUnwrapVariant::ResultOk,
        ("Error", true) => LetUnwrapVariant::ResultError,
        ("Some", true) => LetUnwrapVariant::OptionSome,
        ("None", false) => LetUnwrapVariant::OptionNone,
        _ => return None,
    };

    let var_name = match arena.pat_list(payload.txt) {
        [inner] => Some(*inner),
        _ => None,
    }
    .and_then(|inner| single_var_pattern_name_conservative(arena.get_pat(inner), arena))
    .filter(|name_idx| !arena.get_string(*name_idx).is_empty())
    .unwrap_or_else(|| arena.static_x_name());

    Some((variant, var_name))
}

/// Result of classifying a JavaScript expression.
/// This mirrors OCaml's `Js_raw_info.exp` type.
#[derive(Debug, Clone, PartialEq)]
pub enum JsExpClassification {
    /// A function expression (regular or arrow)
    JsFunction {
        /// The number of parameters.
        arity: usize,
        /// Whether it is an arrow function.
        arrow: bool,
    },
    /// A literal value (string, number, bool, null, undefined, object literal, array literal)
    JsLiteral {
        /// The single comment leading the literal, if any.
        comment: Option<String>,
    },
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
    use oxc_parser::Parser;
    use oxc_span::SourceType;

    let allocator = Allocator::default();
    let parser_return = Parser::new(&allocator, s, SourceType::default()).parse();
    if !parser_return.diagnostics.is_empty() {
        return None;
    }

    let mut leading_comments = parser_return
        .program
        .comments
        .iter()
        .filter(|comment| comment.is_leading());
    let comment = leading_comments.next()?;
    if leading_comments.next().is_some() {
        return None;
    }

    let comment_text = comment.content_span().source_text(s);
    Some(if comment.is_block() {
        format!("/*{comment_text}*/")
    } else {
        format!("//{comment_text}")
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

    let allocator = Allocator::default();
    let source_type = SourceType::default();

    // Try to parse the string as a JavaScript expression. Flow's AST, which
    // OCaml's `classify_exp` matches on, has no parenthesized-expression
    // nodes, so `(function () {...})` is a function there too.
    let parser_result = Parser::new(&allocator, s, source_type)
        .with_options(oxc_parser::ParseOptions {
            preserve_parens: false,
            ..oxc_parser::ParseOptions::default()
        })
        .parse_expression();

    match parser_result {
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
    }
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

    if parser_return.diagnostics.is_empty() && parser_return.program.body.is_empty() {
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
    // Flow recovers an arrow function whose body has parse errors and
    // Classify_function.classify_exp still sees the arrow root
    // (compiler/ml/ast_payload.ml:134-150); classify the parameter list with a
    // placeholder body.
    let completed = if after_arrow == "{" {
        format!("{trimmed}}}")
    } else {
        format!("{} undefined", &trimmed[..arrow_pos + 2])
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
    !after_keyword.chars().next().is_some_and(valid_js_char)
}

fn js_identifier_end(code: &str, start: usize) -> usize {
    let mut end = start;
    for (offset, ch) in code[start..].char_indices() {
        if valid_js_char(ch) {
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
    if after_function.chars().next().is_some_and(valid_js_char) {
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
        Some(ch) if valid_first_js_char(ch) => {
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
    if is_js_regex_like_literal(code)
        && (oxc_message == "Unterminated regular expression"
            || (code.trim() == "/" && oxc_message == "Unexpected token"))
    {
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

    if oxc_message == "Unexpected token"
        && start_offset < code.trim_end().len()
        && let Some(token) = code.get(start_offset..).and_then(|s| s.chars().next())
    {
        return (
            format!("Unexpected token `{token}`"),
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
    if after_keyword.chars().next().is_some_and(valid_js_char) {
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
    let first_label = first_error.labels.first();
    let start_offset = first_label.map_or(code.len(), |label| label.offset() as usize);
    let end_offset = first_label.map_or(start_offset, |label| (label.offset() + label.len()) as usize);
    // Flow's `do_parse ... Parse.expression false` does not require EOF
    // (compiler/ml/ast_payload.ml:177-180). Oxc 0.158 does. A complete
    // expression followed by another token is not a Flow parse warning.
    if first_error.to_string() == "Unexpected token"
        && start_offset > 0
        && code.get(..start_offset).is_some_and(|prefix| {
            Parser::new(&allocator, prefix, SourceType::default())
                .parse_expression()
                .is_ok()
        })
    {
        return None;
    }
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
    let first_error = parser_return.diagnostics.into_iter().next()?;
    let first_label = first_error.labels.first();
    let start_offset = first_label.map_or(code.len(), |label| label.offset() as usize);
    let end_offset = first_label.map_or(start_offset, |label| (label.offset() + label.len()) as usize);
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
    let payload_info = payload_raw_source_info(payload, arena);
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

/// ast_payload.ml `validate_raw_source ~kind:Raw_re ~loc ~offset:0` for a
/// regexp literal's `/pattern/flags` source: reject a non-regexp, then warn
/// about the JS parser's errors.
fn validate_regexp_source(
    code: &str,
    loc: LocIdx,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) -> PpxResult<()> {
    if !is_js_regex_literal(code) && !is_js_regex_like_literal(code) {
        return Err(PpxError::at_loc(
            loc,
            "Syntax error: a valid JS regex literal expected",
        ));
    }
    if let Some(warning) = raw_js_expression_parse_warning(code, loc, 0, arena) {
        warnings.push(PpxWarning {
            loc: warning.loc,
            warning: Warning::BsFfiWarning {
                message: warning.message,
            },
        });
    }
    Ok(())
}

fn push_raw_js_program_warning(
    payload: &Payload,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let payload_info = payload_raw_source_info(payload, arena);
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
) -> PpxResult<()> {
    let (name, payload) = attr;
    let attr_name = arena.get_string(name.txt);
    match attr_name {
        "warning" | "warnerror" => {
            let errflag = attr_name == "warnerror";
            if let Some(spec) = payload_semantic_string(payload, arena)? {
                if !warning_spec_parse_ok(&spec, errflag) {
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
        "ppwarning" => {
            if let Some(message) = payload_semantic_string(payload, arena)? {
                // builtin_attributes.ml:202-212 reports at the item's `pstr_loc`.
                let Payload::PStr(items) = payload else {
                    unreachable!("a single string literal payload is a structure");
                };
                warnings.push(PpxWarning {
                    loc: items[0].pstr_loc,
                    warning: Warning::Preprocessor { message },
                });
            }
        }
        _ => {}
    }
    Ok(())
}

fn builtin_warning_attribute_spec(
    attr: &Attribute,
    arena: &ParseArena,
) -> PpxResult<Option<WarningAttributeSpec>> {
    let (name, payload) = attr;
    let attr_name = arena.get_string(name.txt);
    Ok(match attr_name {
        "warning" | "warnerror" => {
            payload_semantic_string(payload, arena)?.map(|spec| WarningAttributeSpec {
                spec,
                as_error: attr_name == "warnerror",
            })
        }
        _ => None,
    })
}

/// The floating attributes (`@@attr`) at the start of a structure.
fn leading_structure_attributes(structure: &[StructureItem]) -> impl Iterator<Item = &Attribute> {
    structure.iter().map_while(|item| match &item.pstr_desc {
        StructureItemDesc::Pstr_attribute(attr) => Some(&**attr),
        _ => None,
    })
}

/// The floating attributes (`@@attr`) at the start of a signature.
fn leading_signature_attributes(signature: &[SignatureItem]) -> impl Iterator<Item = &Attribute> {
    signature.iter().map_while(|item| match &item.psig_desc {
        SignatureItemDesc::Psig_attribute(attr) => Some(&**attr),
        _ => None,
    })
}

/// `Builtin_attributes.warning_attribute` over `attrs`, which raises on a
/// payload `string_of_payload` cannot read (builtin_attributes.ml:19-22).
fn collect_builtin_warning_attributes<'a>(
    attrs: impl Iterator<Item = &'a Attribute>,
    arena: &ParseArena,
) -> PpxResult<Vec<PpxWarning>> {
    let mut warnings = Vec::new();
    for attr in attrs {
        collect_builtin_warning_attribute(attr, arena, &mut warnings)?;
    }
    Ok(warnings)
}

/// Mirrors `Bs_ast_invariant.iter_warnings_on_stru`: only leading floating
/// structure attributes are checked before frontend rewriting.
pub fn collect_leading_builtin_warning_attributes(
    structure: &[StructureItem],
    arena: &ParseArena,
) -> PpxResult<Vec<PpxWarning>> {
    collect_builtin_warning_attributes(leading_structure_attributes(structure), arena)
}

/// Mirrors `Bs_ast_invariant.iter_warnings_on_stru` at
/// compiler/frontend/bs_ast_invariant.ml:151-158: leading `@@warning` and
/// `@@warnerror` attributes update the warning state before frontend rewriting.
pub fn collect_leading_builtin_warning_attribute_specs(
    structure: &[StructureItem],
    arena: &ParseArena,
) -> PpxResult<Vec<WarningAttributeSpec>> {
    leading_structure_attributes(structure)
        .filter_map(|attr| builtin_warning_attribute_spec(attr, arena).transpose())
        .collect()
}

/// Mirrors `Bs_ast_invariant.iter_warnings_on_sigi` at
/// compiler/frontend/bs_ast_invariant.ml:160-167 for interface files.
pub fn collect_leading_builtin_warning_signature_attributes(
    signature: &[SignatureItem],
    arena: &ParseArena,
) -> PpxResult<Vec<PpxWarning>> {
    collect_builtin_warning_attributes(leading_signature_attributes(signature), arena)
}

/// Mirrors `Bs_ast_invariant.iter_warnings_on_sigi` for interface files.
pub fn collect_leading_builtin_warning_signature_attribute_specs(
    signature: &[SignatureItem],
    arena: &ParseArena,
) -> PpxResult<Vec<WarningAttributeSpec>> {
    leading_signature_attributes(signature)
        .filter_map(|attr| builtin_warning_attribute_spec(attr, arena).transpose())
        .collect()
}

fn attr_named(attrs: &[Attribute], name: &str, arena: &ParseArena) -> bool {
    attrs
        .iter()
        .any(|(attr_name, _)| arena.get_string(attr_name.txt) == name)
}

fn is_bs_unused_attribute_candidate(name: &str) -> bool {
    matches!(
        name,
        "as" | "config"
            | "ignore"
            | "int"
            | "optional"
            | "res.hoistedFunction"
            | "string"
            | "unwrap"
    )
}

/// OCaml `Bs_ast_invariant.removed_ocaml_attribute`: OCaml spellings of
/// builtin attributes the compiler used to accept, with the hint to show.
fn removed_ocaml_attribute(name: &str) -> Option<&'static str> {
    Some(match name {
        "ocaml.deprecated" => "use `@deprecated` instead.",
        "ocaml.unboxed" => "use `@unboxed` instead.",
        "ocaml.immediate" => "use `@immediate` instead.",
        "ocaml.warnerror" => "use `@warnerror` instead.",
        "ocaml.boxed" => "remove it: types are boxed unless marked `@unboxed`.",
        "ocaml.deprecated_mutable" => "remove it.",
        "ocaml.text" => "use a doc comment instead.",
        "ocaml.warning" => "use `@warning` instead.",
        "ocaml.ppwarning" => "use `@ppwarning` instead.",
        _ => return None,
    })
}

/// OCaml `Bs_ast_invariant.check_removed_ocaml_attribute`.
fn check_removed_ocaml_attribute(attr: &Attribute, arena: &ParseArena) -> Option<PpxError> {
    let name = arena.get_string(attr.0.txt);
    removed_ocaml_attribute(name).map(|hint| {
        PpxError::at_loc(
            attr.0.loc,
            format!("`@{name}` is no longer supported, {hint}"),
        )
    })
}

/// OCaml `Bs_ast_invariant.check_removed_ocaml_extension`.
fn check_removed_ocaml_extension(ext: &Extension, arena: &ParseArena) -> Option<PpxError> {
    (arena.get_string(ext.0.txt) == "ocaml.error").then(|| {
        PpxError::at_loc(
            ext.0.loc,
            "`%ocaml.error` is no longer supported, use `%error` instead.",
        )
    })
}

/// OCaml `Bs_ast_invariant.warn_unused_attribute` (bs_ast_invariant.ml:36-45),
/// without its leading `check_removed_ocaml_attribute`, which callers run.
pub(crate) fn warn_unused_attribute(
    attr: &Attribute,
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) {
    let (attr_name, _) = attr;
    let name = arena.get_string(attr_name.txt);
    if is_bs_unused_attribute_candidate(name)
        && !arena.loc_ghost(attr_name.loc)
        && !arena.is_used_attribute(attr_name.loc)
    {
        warnings.push(PpxWarning {
            loc: attr_name.loc,
            warning: Warning::BsUnusedAttribute {
                name: name.to_string(),
            },
        });
    }
}

/// OCaml `Bs_ast_invariant.check_constant` (bs_ast_invariant.ml:54-64): an
/// integer literal without suffix that `Int32.of_string` rejects warns.
fn check_constant(
    loc: LocIdx,
    constant: &Constant,
    warnings: &mut Vec<PpxWarning>,
    arena: &ParseArena,
) {
    if let Constant::Integer(s, None) = constant {
        if !crate::types::typecore::int32_literal_fits_ocaml(arena.get_string(*s)) {
            warnings.push(PpxWarning {
                loc,
                warning: Warning::BsIntegerLiteralOverflow,
            });
        }
    }
}

/// OCaml `Bs_ast_invariant.emit_external_warnings` (bs_ast_invariant.ml:68-148),
/// run over the rewritten tree. The sweep stops at the first error it raises;
/// warnings emitted before it are printed first.
struct UnusedAttributeSweep<'w> {
    warnings: &'w mut Vec<PpxWarning>,
    /// Set when OCaml's sweep would raise (invalid/duplicated constructor
    /// `@as` in `process_tag_type`); later warnings are never reached. The
    /// error itself is reported by the type checker.
    stopped: bool,
    /// An error raised by the sweep (`Location.raise_errorf`).
    error: Option<PpxError>,
}

impl UnusedAttributeSweep<'_> {
    fn raise(&mut self, loc: LocIdx, message: impl Into<String>) {
        if !self.stopped {
            self.stopped = true;
            self.error = Some(PpxError::at_loc(loc, message));
        }
    }
}

impl super::ast_iter::AstIter for UnusedAttributeSweep<'_> {
    fn type_declaration(&mut self, arena: &ParseArena, td: &TypeDeclaration) {
        if self.stopped {
            return;
        }
        let name = arena.get_string(td.ptype_name.txt);
        if is_builtin_rank0_type_name(name) {
            self.raise(
                td.ptype_loc,
                format!("built-in type `{name}` can not be redefined "),
            );
            return;
        }
        super::ast_iter::walk_type_declaration(self, arena, td);
    }

    fn value_description(&mut self, arena: &ParseArena, vd: &ValueDescription) {
        if self.stopped {
            return;
        }
        // bs_ast_invariant.ml:119-142.
        if let Some(PrimitiveRepr::PrimName(byte_name)) = &vd.pval_prim {
            let byte_name = arena.get_string(*byte_name);
            if matches!(byte_name, "%identity" | "%component_identity")
                && !core_type_is_arity_one(vd.pval_type, arena)
            {
                self.raise(
                    vd.pval_loc,
                    format!("{byte_name} expects a function type of the form 'a => 'b (arity 1)"),
                );
                return;
            }
            let safe = byte_name
                .as_bytes()
                .first()
                .is_some_and(|c| matches!(c, b'%' | b'#' | b'?'));
            if !safe {
                self.warnings.push(PpxWarning {
                    loc: vd.pval_loc,
                    warning: Warning::BsFfiWarning {
                        message: format!("{byte_name} such externals are unsafe"),
                    },
                });
                return;
            }
        }
        super::ast_iter::walk_value_description(self, arena, vd);
    }

    fn attribute(&mut self, arena: &ParseArena, attr: &Attribute) {
        // `attribute = fun _ attr -> warn_unused_attribute attr`: payloads are
        // not traversed.
        if self.stopped {
            return;
        }
        if let Some(error) = check_removed_ocaml_attribute(attr, arena) {
            self.stopped = true;
            self.error = Some(error);
            return;
        }
        warn_unused_attribute(attr, arena, self.warnings);
    }

    fn extension(&mut self, arena: &ParseArena, ext: &Extension) {
        if self.stopped {
            return;
        }
        if let Some(error) = check_removed_ocaml_extension(ext, arena) {
            self.stopped = true;
            self.error = Some(error);
            return;
        }
        super::ast_iter::walk_extension(self, arena, ext);
    }

    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        if arena.expr_needs_no_attribute_sweep(idx) {
            return;
        }
        // `Pexp_constant` runs the literal check and then sweeps only its
        // attributes, without `super.expr` (bs_ast_invariant.ml).
        let expr = arena.get_expr(idx);
        match &expr.pexp_desc {
            ExpressionDesc::Pexp_constant(constant) => {
                if !self.stopped {
                    check_constant(expr.pexp_loc, constant, self.warnings, arena);
                    self.attributes(arena, expr.pexp_attributes.as_slice());
                }
            }
            _ => super::ast_iter::walk_expr(self, arena, idx),
        }
    }

    fn pat(&mut self, arena: &ParseArena, idx: PatIdx) {
        // `Ppat_constant` runs `check_constant` and then sweeps only its
        // attributes (bs_ast_invariant.ml).
        let pat = arena.get_pat(idx);
        if let PatternDesc::Ppat_constant(constant) = &pat.ppat_desc {
            if !self.stopped {
                check_constant(pat.ppat_loc, constant, self.warnings, arena);
                self.attributes(arena, pat.ppat_attributes.as_slice());
            }
        } else {
            super::ast_iter::walk_pat(self, arena, idx);
        }
    }

    fn label_declaration(&mut self, arena: &ParseArena, ld: &LabelDeclaration) {
        // bs_ast_invariant.ml: a field's `@as` is taken out of its attributes
        // when it names the field, so one still here is either a second one,
        // which the type checker rejects, or a payload that is not a name and
        // warns as the unused attribute it is.
        for attr in ld.pld_attributes.iter() {
            if arena.get_string(attr.0.txt) != "as" {
                continue;
            }
            match crate::ast_payload::string_literal_of_payload(arena, &attr.1) {
                Ok(Some(_)) => arena.mark_used_attribute(attr),
                Ok(None) => {}
                Err(error) => {
                    self.raise(error.loc, error.message);
                    return;
                }
            }
        }
        super::ast_iter::walk_label_declaration(self, arena, ld);
    }

    fn constructor_declaration(&mut self, arena: &ParseArena, cd: &ConstructorDeclaration) {
        if self.stopped {
            return;
        }
        // `Ast_untagged_variants.process_constructor_tag`: an `@as` left in
        // the attributes is invalid or a duplicate, and the tag must decode.
        if let Err((loc, error)) = crate::types::typemod::process_constructor_tag(arena, cd) {
            self.raise(loc, error.message_text());
            return;
        }
        let name = arena.get_string(cd.pcd_name.txt);
        if matches!(name, "false" | "true" | "()") {
            self.raise(cd.pcd_name.loc, format!("{name} can not be redefined "));
            return;
        }
        super::ast_iter::walk_constructor_declaration(self, arena, cd);
    }
}

/// Mark the first leading `@@config` used (OCaml `Ast_config.iter_on_config_str`
/// via `Ast_config.process_str`), which runs before the builtin mapper.
pub fn mark_config_attributes_structure(items: &[StructureItem], arena: &ParseArena) {
    mark_first_config_attribute(leading_structure_attributes(items), arena);
}

/// Mark the first leading `@@config` of an interface used, like
/// [`mark_config_attributes_structure`] does for implementations.
pub fn mark_config_attributes_signature(items: &[SignatureItem], arena: &ParseArena) {
    mark_first_config_attribute(leading_signature_attributes(items), arena);
}

fn mark_first_config_attribute<'a>(
    mut attrs: impl Iterator<Item = &'a Attribute>,
    arena: &ParseArena,
) {
    if let Some(attr) = attrs.find(|attr| arena.get_string(attr.0.txt) == "config") {
        arena.mark_used_attribute(attr);
    }
}

/// OCaml `Bs_ast_invariant.emit_external_warnings_on_structure`: the warnings
/// in traversal order, and the error the sweep raised (if any).
pub fn collect_unused_attribute_warnings_structure(
    items: &[StructureItem],
    arena: &ParseArena,
) -> (Vec<PpxWarning>, Option<PpxError>) {
    let mut warnings = Vec::new();
    let mut sweep = UnusedAttributeSweep {
        warnings: &mut warnings,
        stopped: false,
        error: None,
    };
    super::ast_iter::walk_structure(&mut sweep, arena, items);
    let error = sweep.error.take();
    (warnings, error)
}

/// OCaml `Bs_ast_invariant.removed_ocaml_spellings`: the PPX bridge renames
/// the `ocaml.`-prefixed builtins a PPX emits to their bare names, so source
/// written with them is checked before it reaches the bridge.
struct RemovedOcamlSpellings {
    error: Option<PpxError>,
}

impl super::ast_iter::AstIter for RemovedOcamlSpellings {
    fn attribute(&mut self, arena: &ParseArena, attr: &Attribute) {
        if self.error.is_some() {
            return;
        }
        self.error = check_removed_ocaml_attribute(attr, arena);
        if self.error.is_none() {
            super::ast_iter::walk_attribute(self, arena, attr);
        }
    }

    fn extension(&mut self, arena: &ParseArena, ext: &Extension) {
        if self.error.is_some() {
            return;
        }
        self.error = check_removed_ocaml_extension(ext, arena);
        if self.error.is_none() {
            super::ast_iter::walk_extension(self, arena, ext);
        }
    }
}

/// OCaml `Bs_ast_invariant.check_removed_ocaml_spellings_on_structure`.
pub fn check_removed_ocaml_spellings_structure(
    items: &[StructureItem],
    arena: &ParseArena,
) -> Result<(), PpxError> {
    let mut check = RemovedOcamlSpellings { error: None };
    super::ast_iter::walk_structure(&mut check, arena, items);
    check.error.map_or(Ok(()), Err)
}

/// OCaml `Bs_ast_invariant.check_removed_ocaml_spellings_on_signature`.
pub fn check_removed_ocaml_spellings_signature(
    items: &[SignatureItem],
    arena: &ParseArena,
) -> Result<(), PpxError> {
    let mut check = RemovedOcamlSpellings { error: None };
    super::ast_iter::walk_signature(&mut check, arena, items);
    check.error.map_or(Ok(()), Err)
}

/// OCaml `Bs_ast_invariant.emit_external_warnings_on_signature`.
pub fn collect_unused_attribute_warnings_signature(
    items: &[SignatureItem],
    arena: &ParseArena,
) -> (Vec<PpxWarning>, Option<PpxError>) {
    let mut warnings = Vec::new();
    let mut sweep = UnusedAttributeSweep {
        warnings: &mut warnings,
        stopped: false,
        error: None,
    };
    super::ast_iter::walk_signature(&mut sweep, arena, items);
    let error = sweep.error.take();
    (warnings, error)
}

/// The `@string is redundant here` warning `spec_of_ptyp` emits through
/// `Ast_polyvar.map_row_fields_into_strings` (ast_polyvar.ml:70-78) for a
/// closed polyvariant of nullary tags without `@as`. Called wherever the
/// external checks run `spec_of_ptyp`.
fn spec_of_ptyp_warning(typ: &CoreType, arena: &ParseArena, warnings: &mut Vec<PpxWarning>) {
    if check_type_ffi_attrs(typ, arena) != Some("string") || type_ffi_attr_count(typ, arena) != 1 {
        return;
    }

    let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc else {
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
        .filter(|(attr_name, _)| ffi_type_attr_name(arena.get_string(attr_name.txt)).is_some())
        .count()
}

/// Parse `s` as one JavaScript regexp literal, returning its pattern and
/// raw flag spelling (ast_mapper_from0.ml `Pexp_extension "re"`: the flags
/// are cut from the literal's raw text so unknown flags survive).
pub fn parse_js_regexp_literal(s: &str) -> Option<(String, String)> {
    use oxc_allocator::Allocator;
    use oxc_ast::ast::Expression;
    use oxc_parser::Parser;
    use oxc_span::{GetSpan, SourceType};

    let allocator = Allocator::default();
    match Parser::new(&allocator, s, SourceType::default()).parse_expression() {
        Ok(expr @ Expression::RegExpLiteral(_)) => {
            let span = expr.span();
            let raw = &s[span.start as usize..span.end as usize];
            let pattern_end = raw.rfind('/')?;
            if pattern_end == 0 {
                return None;
            }
            Some((
                raw[1..pattern_end].to_string(),
                raw[pattern_end + 1..].to_string(),
            ))
        }
        _ => None,
    }
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
fn build_arg_type_specs(typ: &CoreType, arena: &ParseArena) -> (Vec<Param>, usize) {
    let args = list_of_arrow_args(typ, arena);

    let mut param_specs: Vec<Param> = Vec::new();
    let mut arity = 0;
    // OCaml tracks whether any runtime argument remains after filtering Arg_cst.
    // When all args are constants but arity > 0, it appends a trailing unit param.
    let mut has_runtime_args = false;

    for arg in args.iter() {
        let (label_noname, arg_type, keeps_runtime_arg) = match &arg.lbl {
            ArgLabel::Optional(_) => {
                let arg_type =
                    get_opt_arg_type_unchecked(false, arena.get_core_type(arg.typ), arena);
                // Optional args are never Arg_cst and are kept in `args`.
                (LabelNoname::ArgOptional, arg_type, true)
            }
            ArgLabel::Labelled(_) => {
                let arg_type = refine_arg_type(false, arena.get_core_type(arg.typ), arena);
                let keeps_runtime_arg = !matches!(arg_type, Attr::ArgCst(_));
                (LabelNoname::ArgLabel, arg_type, keeps_runtime_arg)
            }
            ArgLabel::Nolabel => {
                let arg_type = refine_arg_type(true, arena.get_core_type(arg.typ), arena);
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

    (param_specs, arity)
}

fn params_is_single_extern_unit(params: &[Param]) -> bool {
    matches!(
        params,
        [Param {
            arg_type: Attr::ExternUnit,
            ..
        }]
    )
}

fn params_first_arg_is_const(params: &[Param]) -> bool {
    matches!(
        params.first(),
        Some(Param {
            arg_type: Attr::ArgCst(_),
            ..
        })
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
    warnings: &mut Vec<PpxWarning>,
) -> PpxResult<()> {
    let (args, _result) = list_of_arrow(vd_type, arena);
    // `Ast_external_process.process_obj` folds right over the arguments
    // (ast_external_process.ml:440-590), so the last argument is checked first.
    for arg in args.into_iter().rev() {
        let typ = arena.get_core_type(arg.typ).clone();
        match arg.lbl {
            ArgLabel::Labelled(label_loc) => {
                // `Ast_attributes.iter_process_bs_string_as param_type.attrs`
                // (ast_external_process.ml:459-464): an argument-level `@as`
                // must be a single string.
                validate_string_as_attrs(&arg.attrs, arena)?;
                // `refine_obj_arg_type` (ast_external_process.ml:96-116): `_`
                // needs a type-level `@as` constant; any other type goes
                // through `spec_of_ptyp`.
                if matches!(&typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
                    validate_string_or_int_as_attrs(&typ.ptyp_attributes, arena)?;
                    if !typ
                        .ptyp_attributes
                        .iter()
                        .any(|(attr_name, _)| arena.get_string(attr_name.txt) == "as")
                    {
                        return Err(PpxError::at_loc(
                            typ.ptyp_loc,
                            "_ is not allowed in combination with external optional type",
                        ));
                    }
                } else {
                    validate_external_core_type_arg_errors(&typ, arena)?;
                }

                let label = arena.get_string(label_loc.txt).to_string();
                let arg_type = spec_of_ptyp(false, &typ, arena);
                spec_of_ptyp_warning(&typ, arena, warnings);
                match arg_type {
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
                validate_string_as_attrs(&arg.attrs, arena)?;
                let label = arena.get_string(label_loc.txt).to_string();
                // `get_opt_arg_type` (ast_external_process.ml:127-134).
                let arg_type = get_opt_arg_type(false, &typ, arena)?;
                validate_external_core_type_arg_errors(&typ, arena)?;
                spec_of_ptyp_warning(&typ, arena, warnings);
                match arg_type {
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
                    "The @taggedTemplate decorator has been removed. Bind the external with the builtin taggedTemplate<'param, 'output> type instead, e.g. `@module(\"x\") external sql: taggedTemplate<'a, string> = \"sql\"`. The tag can then be used with backtick syntax across module boundaries and as a first-class value.",
                ));
            }
            "val" | "send" | "set" | "get" | "new" => {
                // ast_external_process.ml: an empty payload is fine; otherwise
                // reject a `json` literal, then require a semantic string.
                if !payload_is_empty_str(payload)
                    && payload_semantic_string(payload, arena)?.is_none()
                {
                    return Err(PpxError::at_loc(attr_name.loc, "Invalid payload"));
                }
            }
            "module" => {
                if validate_module_import_attributes_payload(payload, arena)? {
                    continue;
                }
                let strings =
                    match payload_string_literals_or_error_loc(payload, arena, attr_name.loc)? {
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
                    match payload_string_literals_or_error_loc(payload, arena, attr_name.loc)? {
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
                    let mut error = PpxError::at_loc(
                        attr_name.loc,
                        "Unsupported @return directive. Supported directives are `null_to_opt`, `null_undefined_to_opt` (or `nullable`), and `identity`.",
                    );
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
                            "Unsupported @return directive. Supported directives are `null_to_opt`, `null_undefined_to_opt` (or `nullable`), and `identity`.",
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
            "This @return directive requires the external's return type to be an option, e.g. `option<int>`.",
        ));
    }
    Ok(())
}

/// The argument fold of the non-`@obj` branch of OCaml `handle_attributes`
/// (compiler/frontend/ast_external_process.ml:927-983): arguments are visited
/// right to left, the `@variadic` checks apply while no non-ignored argument
/// has been seen, then each argument is classified by `get_opt_arg_type` or
/// `refine_arg_type`.
fn validate_non_obj_arg_type_errors(
    args: &[TypeArg],
    splice: bool,
    external_loc: LocIdx,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) -> PpxResult<()> {
    let mut i = 0;
    for arg in args.iter().rev() {
        let typ = arena.get_core_type(arg.typ).clone();
        if i == 0 && splice {
            validate_variadic_arg_type(arg, &typ, external_loc, arena, warnings)?;
        }
        let arg_type = match arg.lbl {
            ArgLabel::Optional(label_loc) => {
                let arg_type = get_opt_arg_type(false, &typ, arena)?;
                validate_external_core_type_arg_errors(&typ, arena)?;
                spec_of_ptyp_warning(&typ, arena, warnings);
                if matches!(arg_type, Attr::PolyVar { .. }) {
                    let label = arena.get_string(label_loc.txt);
                    return Err(PpxError::at_loc(
                        external_loc,
                        format!(
                            "@string does not work with optional when it has arities in label {label}"
                        ),
                    ));
                }
                arg_type
            }
            ArgLabel::Labelled(_) | ArgLabel::Nolabel => {
                validate_external_core_type_arg_errors(&typ, arena)?;
                let arg_type = refine_arg_type(matches!(arg.lbl, ArgLabel::Nolabel), &typ, arena);
                spec_of_ptyp_warning(&typ, arena, warnings);
                arg_type
            }
        };
        if !matches!(arg_type, Attr::Ignore) {
            i += 1;
        }
    }
    Ok(())
}

/// The `@variadic` checks of `handle_attributes` (ast_external_process.ml:934-950).
fn validate_variadic_arg_type(
    arg: &TypeArg,
    typ: &CoreType,
    external_loc: LocIdx,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) -> PpxResult<()> {
    if matches!(arg.lbl, ArgLabel::Optional(_)) {
        return Err(PpxError::at_loc(
            external_loc,
            "@variadic expect the last type to be a non optional",
        ));
    }
    let array_error = || {
        PpxError::at_loc(
            external_loc,
            "@variadic expect the last type to be an array",
        )
    };
    if matches!(&typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
        return Err(array_error());
    }
    // `spec_of_ptyp true ty` (ast_external_process.ml:943) raises for
    // invalid @string/@int/@unwrap payload types (lines 39-70).
    validate_external_core_type_arg_errors(typ, arena)?;
    let arg_type = refine_arg_type(true, typ, arena);
    spec_of_ptyp_warning(typ, arena, warnings);
    if !matches!(arg_type, Attr::Nothing) {
        return Err(array_error());
    }
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = *inner;
            if args.len() == 1
                && let Longident::Lident(name) = arena.get_longident(lid.txt)
                && arena.get_string(*name) == "array"
            {
                return Ok(());
            }
            Err(array_error())
        }
        _ => Err(array_error()),
    }
}

fn validate_external_core_type_arg_errors(typ: &CoreType, arena: &mut ParseArena) -> PpxResult<()> {
    if matches!(&typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
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
    warnings: &mut Vec<PpxWarning>,
) -> PpxResult<()> {
    if !is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return Ok(());
    }

    let Some(PrimitiveRepr::PrimName(prim_name)) = &vd.pval_prim else {
        return Ok(());
    };
    let prim_name = arena.get_string(*prim_name).to_string();
    let vd_type = arena.get_core_type(vd.pval_type).clone();
    let vd_type = fixed_args_as_attributes(&vd_type, arena);
    let (args, result_type) = list_of_arrow(&vd_type, arena);

    // OCaml `handle_external_in_stru`/`handle_external_in_sig` map the
    // attributes with the builtin mapper before `encode_attributes_as_string`
    // (ast_external.ml:29-39, 58-68), so payload checks see expanded payloads.
    let mapped_attrs = rewrite_attributes(&vd.pval_attributes, arena);
    validate_external_attribute_payload_errors(&mapped_attrs, prim_name.as_str(), arena)?;

    let desc = parse_external_attrs(
        &mapped_attrs,
        prim_name.as_str(),
        args.is_empty(),
        vd.pval_loc,
        arena,
    )?;

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
            validate_plain_obj_arg_type_errors(&vd_type, vd.pval_loc, arena, warnings)?;
            return Ok(());
        }
        return Err(PpxError::at_loc(
            vd.pval_loc,
            "Attribute found that conflicts with @obj",
        ));
    }

    validate_non_obj_arg_type_errors(&args, desc.splice, vd.pval_loc, arena, warnings)?;

    let (params, arity) = build_arg_type_specs(&vd_type, arena);

    if desc.set_index && !external_desc_is_plain_set_index(&desc) {
        return Err(PpxError::at_loc(
            vd.pval_loc,
            "Conflicting attributes: Attribute found that conflicts with @set_index",
        ));
    }

    if desc.get_index && !external_desc_is_plain_get_index(&desc) {
        return Err(PpxError::at_loc(
            vd.pval_loc,
            "Conflicting attributes: Attribute found that conflicts with @get_index",
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
                "Conflicting attributes: Attribute found that conflicts with @val",
            ));
        }

        if desc.val_name.is_some() && !desc.module_as_val && !external_desc_is_plain_val(&desc) {
            return Err(PpxError::at_loc(
                vd.pval_loc,
                "Conflicting attributes: Attribute found that conflicts with @val",
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
                "Conflicting attributes: Attribute found that conflicts with @new",
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

    let decl = build_external_decl(&desc, prim_name.as_str(), arity);
    check_decl(&decl, prim_name.as_str(), vd.pval_loc)?;
    validate_return_wrapper_result_type(&desc.return_wrapper, &result_type, vd.pval_loc, arena)?;

    Ok(())
}

/// Determine the arg type for a non-labeled argument type.
/// Mirrors OCaml's refine_arg_type / spec_of_ptyp.
fn refine_arg_type(nolabel: bool, typ: &CoreType, arena: &ParseArena) -> Attr {
    // For Ptyp_any with @as attribute, handle constant args
    if matches!(&typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
        // Check for @as attribute on the type
        for attr in &typ.ptyp_attributes {
            let (attr_name, payload) = attr;
            if arena.get_string(attr_name.txt) == "as" {
                // OCaml `iter_process_bs_string_or_int_as` marks the first @as used.
                arena.mark_used_attribute(attr);
                // Try int first (mirrors OCaml's is_single_int check first)
                if let Some(i) = get_payload_int(payload, arena) {
                    return Attr::ArgCst(Cst::ArgIntLit(i as i64));
                }
                // Then a semantic string, then a `json` literal.
                match checked(get_payload_string_or_json(payload, arena)) {
                    Some(AsStringPayload::Str(s)) => return Attr::ArgCst(Cst::ArgStringLit(s)),
                    Some(AsStringPayload::Json { source, .. }) => {
                        return Attr::ArgCst(Cst::ArgJsonLit(source));
                    }
                    None => {}
                }
            }
        }
    }
    spec_of_ptyp(nolabel, typ, arena)
}

/// Check for @string, @int, @unwrap, @ignore attributes on a type.
/// Returns `Some(attr_type)` if found, `None` otherwise.
/// Mirrors OCaml's iter_process_bs_string_int_unwrap_uncurry.
/// The FFI type attributes (`@string`, `@int`, `@ignore`, `@unwrap`).
fn ffi_type_attr_name(name: &str) -> Option<&'static str> {
    match name {
        "string" => Some("string"),
        "int" => Some("int"),
        "ignore" => Some("ignore"),
        "unwrap" => Some("unwrap"),
        _ => None,
    }
}

fn check_type_ffi_attrs(typ: &CoreType, arena: &ParseArena) -> Option<&'static str> {
    typ.ptyp_attributes
        .iter()
        .find_map(|(attr_name, _)| ffi_type_attr_name(arena.get_string(attr_name.txt)))
}

fn external_type_ffi_attr(typ: &CoreType, arena: &ParseArena) -> PpxResult<Option<&'static str>> {
    let mut found = Vec::new();
    for (attr_name, _) in &typ.ptyp_attributes {
        if let Some(attr) = ffi_type_attr_name(arena.get_string(attr_name.txt)) {
            found.push((attr, attr_name.loc));
        }
    }
    if found.len() > 1 {
        let names = found
            .iter()
            .map(|(name, _)| format!("@{name}"))
            .collect::<Vec<_>>()
            .join(", ");
        return Err(PpxError::at_loc(
            found[0].1,
            format!("Conflicting attributes: {names} cannot be combined; use only one."),
        ));
    }
    Ok(found.first().map(|(name, _)| *name))
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

/// OCaml `Ast_payload.semantic_string_of_payload`, which raises "Invalid
/// string escape sequence" on a template that does not decode.
fn payload_semantic_string(payload: &Payload, arena: &ParseArena) -> PpxResult<Option<String>> {
    crate::ast_payload::semantic_string_of_payload(arena, payload).map_err(payload_error)
}

/// OCaml `Ast_payload.semantic_string_of_expression`, which raises like
/// [`payload_semantic_string`].
fn expr_semantic_string(expr: &Expression, arena: &ParseArena) -> PpxResult<Option<String>> {
    crate::ast_payload::semantic_string_of_expression(arena, expr).map_err(payload_error)
}

fn payload_error(error: crate::ast_payload::PayloadError) -> PpxError {
    PpxError::at_loc(error.loc, error.message)
}

/// The string payload matched by OCaml `Ast_payload.raw_as_string_exp_exn`:
/// the JavaScript code, the expression location, and the offset Flow errors
/// are shifted by.
fn payload_raw_source_info(payload: &Payload, arena: &ParseArena) -> Option<(String, LocIdx, i32)> {
    let Payload::PStr(items) = payload else {
        return None;
    };
    let [item] = items.as_slice() else {
        return None;
    };
    let StructureItemDesc::Pstr_eval(eval_inner) = &item.pstr_desc else {
        return None;
    };
    let braced = matches!(
        &arena.get_expr(eval_inner.0).pexp_desc,
        ExpressionDesc::Pexp_braces(_)
    );
    // `Ast_payload.unwrap_payload_expression`.
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(eval_inner.0));
    // `Bs_flow_ast_utils.flow_deli_offset (Some "js")`.
    let js_offset = 4;
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_template(template)
            if template.source_segments.len() == 1 && template.values.is_empty() =>
        {
            // ast_payload.ml: `String_literal.decode_raw_template_source`.
            let source = crate::string_literal::decode_raw_template_source(
                arena.get_string(template.source_segments[0].txt),
            );
            Some((source, expr.pexp_loc, js_offset))
        }
        ExpressionDesc::Pexp_constant(c) => match c {
            // A braced payload is an ordinary string expression, so its
            // escapes are decoded.
            Constant::String(payload) if braced => {
                Some((payload.semantic(arena).to_string(), expr.pexp_loc, 0))
            }
            // A raw payload is JavaScript source, so the string is taken as
            // written.
            Constant::String(payload) => {
                Some((payload.source(arena).to_string(), expr.pexp_loc, js_offset))
            }
            _ => None,
        },
        _ => None,
    }
}

fn payload_string_literals(
    payload: &Payload,
    arena: &ParseArena,
) -> PpxResult<Option<Vec<String>>> {
    match payload {
        Payload::PStr(items) if items.is_empty() => Ok(Some(Vec::new())),
        Payload::PStr(items) if items.len() == 1 => {
            let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc else {
                return Ok(None);
            };
            let (expr, _) = &**eval_inner;
            match &crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr)).pexp_desc {
                ExpressionDesc::Pexp_tuple(exprs) => {
                    let mut result = Vec::with_capacity(exprs.len());
                    for expr in arena.expr_list(*exprs).iter() {
                        match expr_semantic_string(arena.get_expr(*expr), arena)? {
                            Some(s) => result.push(s),
                            None => return Ok(None),
                        }
                    }
                    Ok(Some(result))
                }
                _ => Ok(expr_semantic_string(arena.get_expr(*expr), arena)?.map(|s| vec![s])),
            }
        }
        _ => Ok(None),
    }
}

fn payload_string_literals_or_error_loc(
    payload: &Payload,
    arena: &ParseArena,
    default_loc: LocIdx,
) -> PpxResult<Result<Vec<String>, LocIdx>> {
    match payload {
        Payload::PStr(items) if items.is_empty() => Ok(Ok(Vec::new())),
        Payload::PStr(items) if items.len() == 1 => {
            let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc else {
                return Ok(Err(default_loc));
            };
            let (expr, _) = &**eval_inner;
            match &crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr)).pexp_desc {
                ExpressionDesc::Pexp_tuple(exprs) => {
                    let mut result = Vec::with_capacity(exprs.len());
                    for expr in arena.expr_list(*exprs).iter() {
                        match expr_semantic_string(arena.get_expr(*expr), arena)? {
                            Some(s) => result.push(s),
                            None => return Ok(Err(items[0].pstr_loc)),
                        }
                    }
                    Ok(Ok(result))
                }
                _ => Ok(match expr_semantic_string(arena.get_expr(*expr), arena)? {
                    Some(s) => Ok(vec![s]),
                    None => Err(default_loc),
                }),
            }
        }
        _ => Ok(Err(default_loc)),
    }
}

/// Extract @as("string") from attributes.
/// Mirrors OCaml's iter_process_bs_string_as.
fn get_as_string_attr(attrs: &[Attribute], arena: &ParseArena) -> Option<String> {
    for attr in attrs {
        let (attr_name, payload) = attr;
        let name = arena.get_string(attr_name.txt);
        if name == "as" {
            // Try to get string payload
            if let Some(s) = checked(payload_semantic_string(payload, arena)) {
                arena.mark_used_attribute(attr);
                return Some(s);
            }
        }
    }
    None
}

/// Extract @as(int) from attributes.
/// Mirrors OCaml's iter_process_bs_int_as.
fn get_as_int_attr(attrs: &[Attribute], arena: &ParseArena) -> Option<i64> {
    for attr in attrs {
        let (attr_name, payload) = attr;
        let name = arena.get_string(attr_name.txt);
        if name == "as" {
            // Try to get int payload
            if let Some(items) = payload_str_items(payload) {
                if items.len() == 1 {
                    if let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc {
                        let (ref expr, _) = **eval_inner;
                        if let ExpressionDesc::Pexp_constant(Constant::Integer(s, suffix)) =
                            &crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr))
                                .pexp_desc
                        {
                            // Reject bigint suffix
                            if matches!(suffix, Some('n')) {
                                return None;
                            }
                            let v = arena.get_string(*s).parse::<i64>().ok();
                            if v.is_some() {
                                arena.mark_used_attribute(attr);
                            }
                            return v;
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
            return Err(PpxError::at_loc(
                attr_name.loc,
                "Duplicate @as annotation; only one @as is allowed here.",
            ));
        }
        if get_payload_string(payload, arena)?.is_none() {
            return Err(PpxError::at_loc(
                attr_name.loc,
                "Expected a string literal.",
            ));
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
            return Err(PpxError::at_loc(
                attr_name.loc,
                "Duplicate @as annotation; only one @as is allowed here.",
            ));
        }
        if get_payload_int_result(payload, arena)?.is_none() {
            return Err(PpxError::at_loc(
                attr_name.loc,
                "The @as payload on an @int variant must be an integer literal, e.g. @as(42).",
            ));
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
            return Err(PpxError::at_loc(
                attr_name.loc,
                "Duplicate @as annotation; only one @as is allowed here.",
            ));
        }
        if get_payload_int_result(payload, arena)?.is_some() {
            seen_as = true;
            continue;
        }
        let Some(as_payload) = get_payload_string_or_json(payload, arena)? else {
            return Err(PpxError::at_loc(
                attr_name.loc,
                "The @as payload must be an integer, string, or JSON literal.",
            ));
        };
        if let AsStringPayload::Json {
            source: payload,
            loc,
        } = as_payload
            && !matches!(
                classify_js_exp(&payload),
                JsExpClassification::JsLiteral { .. }
            )
        {
            let err = PpxError::at_loc(loc, "an object literal expected");
            // `Bs_flow_ast_utils.flow_deli_offset (Some "json")`.
            let flow_offset = 6;
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
    let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc else {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "Not a valid type for @string",
        ));
    };
    let (row_fields, closed, labels) = &**variant_inner;
    if !matches!(closed, current::ClosedFlag::Closed) || labels.is_some() || row_fields.is_empty() {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "Not a valid type for @string",
        ));
    }

    enum StringRows {
        Nothing,
        Null,
        NonNull,
    }

    // `Ast_polyvar.map_row_fields_into_strings` (ast_polyvar.ml:44-71) folds
    // from the right, so later rows are checked first.
    let mut rows = StringRows::Nothing;
    for row in row_fields.iter().rev() {
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
                    "Not a valid type for @string",
                ));
            }
        }
    }

    Ok(())
}

fn validate_bs_int_type(typ: &CoreType, arena: &ParseArena) -> PpxResult<()> {
    let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc else {
        return Err(PpxError::at_loc(typ.ptyp_loc, "Not a valid type for @int"));
    };
    let (row_fields, closed, labels) = &**variant_inner;
    // `spec_of_ptyp` (ast_external_process.ml:52-59) then
    // `map_row_fields_into_ints` (ast_polyvar.ml:25-38), which accepts `[]`.
    if !matches!(closed, current::ClosedFlag::Closed) || labels.is_some() {
        return Err(PpxError::at_loc(typ.ptyp_loc, "Not a valid type for @int"));
    }

    for row in row_fields {
        let RowField::Rtag(_, attrs, true, types) = row else {
            return Err(PpxError::at_loc(typ.ptyp_loc, "Not a valid type for @int"));
        };
        if !types.is_empty() {
            return Err(PpxError::at_loc(typ.ptyp_loc, "Not a valid type for @int"));
        }
        validate_int_as_attrs(attrs, arena)?;
    }

    Ok(())
}

fn validate_bs_unwrap_type(typ: &CoreType) -> PpxResult<()> {
    let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc else {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "Not a valid type for @unwrap. Type must be an inline variant (closed), and\neach constructor must have an argument.",
        ));
    };
    // compiler/frontend/ast_external_process.ml:60-65 matches
    // `Ptyp_variant (row_fields, Closed, _)`: lower-bound labels are allowed.
    let (row_fields, closed, _) = &**variant_inner;
    if !matches!(closed, current::ClosedFlag::Closed)
        || row_fields.is_empty()
        || !variant_can_unwrap(row_fields)
    {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "Not a valid type for @unwrap. Type must be an inline variant (closed), and\neach constructor must have an argument.",
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
/// OCaml `Ast_attributes.iter_process_bs_string_int_unwrap_uncurry`
/// (ast_attributes.ml:170-190) marks the attribute when exactly one of
/// @string/@int/@ignore/@unwrap is present.
fn mark_single_ffi_type_attr(typ: &CoreType, arena: &ParseArena) {
    let found: Vec<&Attribute> = typ
        .ptyp_attributes
        .iter()
        .filter(|attr| {
            matches!(
                arena.get_string(attr.0.txt),
                "string" | "int" | "ignore" | "unwrap"
            )
        })
        .collect();
    if let [attr] = found.as_slice() {
        arena.mark_used_attribute(attr);
    }
}

fn spec_of_ptyp(nolabel: bool, typ: &CoreType, arena: &ParseArena) -> Attr {
    // Check for special attributes on the type (@string, @int, @unwrap, @ignore)
    mark_single_ffi_type_attr(typ, arena);
    let attr_type = check_type_ffi_attrs(typ, arena);

    match attr_type {
        Some("string") => {
            // @string: must be applied to a closed polyvariant
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc {
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
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc {
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
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc {
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
            match &typ.ptyp_desc {
                CoreTypeDesc::Ptyp_constr(inner) if inner.1.is_empty() => {
                    let lid = &inner.0;
                    let longident = arena.get_longident(lid.txt);
                    if matches!(longident, Longident::Lident(s) if arena.get_string(*s) == "unit")
                        && nolabel
                    {
                        return Attr::ExternUnit;
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
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = *inner;
            args.is_empty() && {
                let longident = arena.get_longident(lid.txt);
                matches!(longident, Longident::Lident(s) if arena.get_string(*s) == "unit")
            }
        }
        _ => false,
    }
}

fn is_user_option_type(typ: &CoreType, arena: &ParseArena) -> bool {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = *inner;
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
    let result = match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => arena.get_core_type(inner.1).clone(),
        _ => typ.clone(),
    };
    (list_of_arrow_args(typ, arena).into_owned(), result)
}

/// The argument half of [`list_of_arrow`], borrowed instead of cloned.
fn list_of_arrow_args<'a>(
    typ: &'a CoreType,
    arena: &'a ParseArena,
) -> std::borrow::Cow<'a, [TypeArg]> {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => arena.nary_arrow_args(&inner.0, inner.2),
        _ => std::borrow::Cow::Borrowed(&[]),
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
            ptyp_desc: CoreTypeDesc::Ptyp_constr((
                Located { txt: unit_lid, loc },
                crate::parse_arena::ArenaList::EMPTY,
            )),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        };
        let arity = arena.push_arity(Some(1));
        let unit_arg = TypeArg {
            fixed: None,
            attrs: Attributes::new(),
            lbl: ArgLabel::Nolabel,
            typ: arena.push_core_type(unit_type),
        };
        return CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((
                Box::new(unit_arg),
                arena.push_core_type(result.clone()),
                arity,
            ))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        };
    }

    let args = filtered_args.into_iter().cloned().collect::<Vec<_>>();
    let arity = arena.push_arity(Some(args.len() as i32));
    let first = args[0].clone();
    arena.set_nary_arrow_args(arity, args);
    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(first),
            arena.push_core_type(result),
            arity,
        ))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// External processing reads a fixed argument `Parg_fixed {value; loc}` as
/// what `@as(value) _` means: ast_external_process.ml `arg_parts` types it as
/// its `_`, and `fixed_arg_type` decodes
/// `Ast_attributes.as_const [Ast_fixed_arg.to_attribute ~loc value]`. This
/// gives each fixed argument's `_` (already located at the underscore) that
/// attribute, so the `@as` readers below decode it unchanged. Fixed
/// arguments always decode to `Arg_cst`, so the rebuilt external type drops
/// them and the attribute never reaches the typed tree.
fn fixed_args_as_attributes(typ: &CoreType, arena: &mut ParseArena) -> CoreType {
    let CoreTypeDesc::Ptyp_arrow(inner) = &typ.ptyp_desc else {
        return typ.clone();
    };
    let (first, ret, arity) = &**inner;
    let args = arena.nary_arrow_args(first, *arity).into_owned();
    if args.iter().all(|arg| arg.fixed.is_none()) {
        return typ.clone();
    }
    let args: Vec<TypeArg> = args
        .into_iter()
        .map(|arg| match arg.fixed {
            None => arg,
            Some(fixed) => {
                let attr = crate::ast_fixed_arg::to_attribute(
                    arena,
                    &fixed.value,
                    fixed.value_loc,
                    fixed.loc,
                );
                let mut any = arena.get_core_type(arg.typ).clone();
                any.ptyp_attributes = Attributes::from_vec(vec![attr]);
                TypeArg {
                    fixed: None,
                    typ: arena.push_core_type(any),
                    ..arg
                }
            }
        })
        .collect();
    let first = args[0].clone();
    arena.set_nary_arrow_args(*arity, args);
    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((Box::new(first), *ret, *arity))),
        ptyp_loc: typ.ptyp_loc,
        ptyp_attributes: typ.ptyp_attributes.clone(),
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
    let typ = &fixed_args_as_attributes(typ, arena);
    // Only process if @obj attribute is present
    if !has_obj_attr(attrs, arena) {
        return reconstruct_arrow_type_with_loc(typ, loc, arena);
    }

    let (args, result) = list_of_arrow(typ, arena);
    if args.is_empty() {
        return typ.clone();
    }

    // Check if result type is Ptyp_any
    let result_is_any = matches!(&result.ptyp_desc, CoreTypeDesc::Ptyp_any);

    // Build result_types (object fields) from labeled arguments
    // Mirrors OCaml's fold_right in process_obj
    let mut filtered_args: Vec<&TypeArg> = Vec::new();
    let mut result_types: Vec<ObjectField> = Vec::new();

    for arg in &args {
        let _nolabel = matches!(arg.lbl, ArgLabel::Nolabel);

        match &arg.lbl {
            ArgLabel::Nolabel => {
                // Nolabel args in @obj: only unit is allowed, doesn't contribute to result_types
                filtered_args.push(arg);
            }
            ArgLabel::Labelled(label_loc) => {
                // Labeled args: check for @as("alias") and arg type
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name = get_as_string_attr(&arg.attrs, arena).unwrap_or(label_name);

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
                                loc,
                            },
                            Attributes::new(),
                            arg.typ,
                        ));
                    }
                    Attr::Int(_) => {
                        // @int polyvariant: add to result_types with int type
                        filtered_args.push(arg);
                        let int_lid = arena.push_lident_static("int");
                        let int_type = CoreType {
                            ptyp_desc: CoreTypeDesc::Ptyp_constr((
                                Located { txt: int_lid, loc },
                                crate::parse_arena::ArenaList::EMPTY,
                            )),
                            ptyp_loc: loc,
                            ptyp_attributes: Attributes::new(),
                        };
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc,
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
                            ptyp_desc: CoreTypeDesc::Ptyp_constr((
                                Located {
                                    txt: string_lid,
                                    loc,
                                },
                                crate::parse_arena::ArenaList::EMPTY,
                            )),
                            ptyp_loc: loc,
                            ptyp_attributes: Attributes::new(),
                        };
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc,
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
                                loc,
                            },
                            Attributes::new(),
                            arg.typ,
                        ));
                    }
                }
            }
            ArgLabel::Optional(label_loc) => {
                // Optional args: add to result_types with Js.undefined wrapper
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name = get_as_string_attr(&arg.attrs, arena).unwrap_or(label_name);

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
                                loc,
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
                            ptyp_desc: CoreTypeDesc::Ptyp_constr((
                                Located { txt: int_lid, loc },
                                crate::parse_arena::ArenaList::EMPTY,
                            )),
                            ptyp_loc: loc,
                            ptyp_attributes: Attributes::new(),
                        };
                        let wrapped_type = to_undefined_type(&int_type, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc,
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
                            ptyp_desc: CoreTypeDesc::Ptyp_constr((
                                Located {
                                    txt: string_lid,
                                    loc,
                                },
                                crate::parse_arena::ArenaList::EMPTY,
                            )),
                            ptyp_loc: loc,
                            ptyp_attributes: Attributes::new(),
                        };
                        let wrapped_type = to_undefined_type(&string_type, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located {
                                txt: arena.push_string(field_name.clone()),
                                loc,
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
                                loc,
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
            ptyp_desc: CoreTypeDesc::Ptyp_object(Box::new((
                result_types,
                current::ClosedFlag::Closed,
            ))),
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
        ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((Box::new(first), ret, arity))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Get optional arg type (for Optional labels).
/// Mirrors OCaml's get_opt_arg_type.
fn get_opt_arg_type(nolabel: bool, typ: &CoreType, arena: &ParseArena) -> PpxResult<Attr> {
    if matches!(&typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
        return Err(PpxError::at_loc(
            typ.ptyp_loc,
            "_ is not allowed in combination with external optional type",
        ));
    }
    Ok(get_opt_arg_type_unchecked(nolabel, typ, arena))
}

/// Same classifier after the validation pass has already rejected Ptyp_any.
fn get_opt_arg_type_unchecked(_nolabel: bool, typ: &CoreType, arena: &ParseArena) -> Attr {
    // OCaml `get_opt_arg_type` calls `spec_of_ptyp`.
    mark_single_ffi_type_attr(typ, arena);
    let attr_type = check_type_ffi_attrs(typ, arena);
    match attr_type {
        Some("ignore") => Attr::Ignore,
        Some("int") => {
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc {
                let (row_fields, closed_flag, labels_opt) = &**variant_inner;
                if matches!(closed_flag, current::ClosedFlag::Closed) && labels_opt.is_none() {
                    let int_list = map_row_fields_into_ints(row_fields, arena);
                    return Attr::Int(int_list);
                }
            }
            Attr::Nothing
        }
        Some("string") => {
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc {
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
            if let CoreTypeDesc::Ptyp_variant(variant_inner) = &typ.ptyp_desc {
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

/// Wrap a type in the predeclared `undefined<T>` constructor.
/// Mirrors OCaml's `Ast_comb.to_undefined_type` and `Ast_literal.Lid.js_undefined`.
fn to_undefined_type(typ: &CoreType, loc: LocIdx, arena: &mut ParseArena) -> CoreType {
    let undefined_str = arena.push_string("undefined");
    let longident = arena.push_longident(Longident::Lident(undefined_str));

    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr((
            Located {
                txt: longident,
                loc,
            },
            {
                let items = [arena.push_core_type(typ.clone())];
                arena.push_type_list(&items)
            },
        )),
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
) -> PpxResult<ExternalDesc> {
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
                    get_payload_string(payload, arena)?.unwrap_or_else(|| prim_name.to_string());
                if no_arguments {
                    desc.val_name = Some(name);
                } else {
                    desc.call_name = Some(name);
                }
            }
            "module" => {
                if let Some((bundle, import_attributes)) =
                    get_module_import_attributes(payload, arena)?
                {
                    desc.external_module_name = Some(bundle);
                    desc.module_bind_name = None;
                    desc.import_attributes = Some(import_attributes);
                    continue;
                }

                let strings = get_payload_strings(payload, arena)?;
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
                    get_payload_string(payload, arena)?.unwrap_or_else(|| prim_name.to_string()),
                );
            }
            "new" => {
                let payload_name = get_payload_string(payload, arena)?;
                desc.new_name_from_payload = payload_name.is_some();
                desc.new_name = Some(payload_name.unwrap_or_else(|| prim_name.to_string()));
            }
            "get" => {
                desc.get_name = Some(
                    get_payload_string(payload, arena)?.unwrap_or_else(|| prim_name.to_string()),
                );
            }
            "set" => {
                desc.set_name = Some(
                    get_payload_string(payload, arena)?.unwrap_or_else(|| prim_name.to_string()),
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
                let scopes = get_payload_strings(payload, arena)?;
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

    Ok(desc)
}

/// OCaml `Ast_payload.semantic_string_of_payload`.
fn get_payload_string(
    payload: &current::Payload,
    arena: &ParseArena,
) -> PpxResult<Option<String>> {
    payload_semantic_string(payload, arena)
}

/// Extract return-wrapper config from payload.
/// Mirrors OCaml's Ast_payload.ident_or_record_as_config shape used by
/// ast_external_process.ml for `@return`:
/// - `@return(nullable)` -> `nullable`
/// - `@return({null_to_opt: null_to_opt})` -> `null_to_opt`
///
/// Non-punned record entries are intentionally rejected here.
fn get_return_wrapper_config(payload: &current::Payload, arena: &ParseArena) -> Option<String> {
    let current::Payload::PStr(items) = payload else {
        return None;
    };
    if items.len() != 1 {
        return None;
    }
    let StructureItemDesc::Pstr_eval(inner) = &items[0].pstr_desc else {
        return None;
    };
    let (expr_idx, _) = &**inner;
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr_idx));

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => {
            let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
                return None;
            };
            Some(arena.get_string(*name_idx).to_string())
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, with_obj) = inner;
            if with_obj.is_some() || fields.len() != 1 {
                return None;
            }
            let field = &arena.expr_field_list(*fields)[0];
            let Longident::Lident(field_name_idx) = arena.get_longident(field.lid.txt) else {
                return None;
            };
            let field_expr = arena.get_expr(field.expr);
            let ExpressionDesc::Pexp_ident(value_lid) = &field_expr.pexp_desc else {
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
    let StructureItemDesc::Pstr_eval(inner) = &items[0].pstr_desc else {
        return Ok(());
    };
    let (expr_idx, _) = &**inner;
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr_idx));
    let ExpressionDesc::Pexp_record(inner) = &expr.pexp_desc else {
        return Ok(());
    };
    let (fields, with_obj) = inner;
    if with_obj.is_some() {
        return Ok(());
    }
    for field in arena.expr_field_list(*fields) {
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
    let StructureItemDesc::Pstr_eval(inner) = &items[0].pstr_desc else {
        return Some((default_loc, "invalid attribute config-record, ignoring"));
    };
    let (expr_idx, _) = &**inner;
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr_idx));
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_record(inner) => {
            let (_fields, with_obj) = inner;
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
            if let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc {
                let (ref expr, _) = **eval_inner;
                if let ExpressionDesc::Pexp_constant(current::Constant::Integer(name, suffix)) =
                    &crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr)).pexp_desc
                {
                    // OCaml's is_single_int rejects 'n' suffix (bigint)
                    if matches!(suffix, Some('n')) {
                        return Ok(None);
                    }
                    return arena
                        .get_string(*name)
                        .parse::<i32>()
                        .map(Some)
                        .map_err(|_| PpxError::int_of_string_failure());
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

/// The string forms OCaml `Ast_attributes.iter_process_bs_string_or_int_as`
/// accepts after `is_single_int`: a semantic string, or a `json` literal.
enum AsStringPayload {
    Str(String),
    Json { source: String, loc: LocIdx },
}

fn get_payload_string_or_json(
    payload: &current::Payload,
    arena: &ParseArena,
) -> PpxResult<Option<AsStringPayload>> {
    if let Some(s) = payload_semantic_string(payload, arena)? {
        return Ok(Some(AsStringPayload::Str(s)));
    }
    Ok(json_as_payload(payload, arena))
}

/// The `json` literal case of [`get_payload_string_or_json`].
fn json_as_payload(payload: &current::Payload, arena: &ParseArena) -> Option<AsStringPayload> {
    let current::Payload::PStr(items) = payload else {
        return None;
    };
    let [item] = items.as_slice() else {
        return None;
    };
    let StructureItemDesc::Pstr_eval(eval_inner) = &item.pstr_desc else {
        return None;
    };
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(eval_inner.0));
    match &expr.pexp_desc {
        // ast_attributes.ml as_const: a non-interpolated `json` tagged template.
        ExpressionDesc::Pexp_tagged_template(template) => {
            let tag = arena.get_expr(template.tag);
            let ExpressionDesc::Pexp_ident(lid) = &tag.pexp_desc else {
                return None;
            };
            match (template.raw_sources.as_slice(), template.values.is_empty()) {
                ([source], true) if arena.is_lident(lid.txt, "json") => {
                    Some(AsStringPayload::Json {
                        source: arena.get_string(source.txt).to_string(),
                        loc: source.loc,
                    })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract multiple strings from attribute payload (mirrors OCaml's Ast_payload.assert_strings)
/// Handles: @attr("str"), @attr(("str1", "str2", ...)), @attr (empty → [])
fn get_payload_strings(payload: &current::Payload, arena: &ParseArena) -> PpxResult<Vec<String>> {
    Ok(payload_string_literals(payload, arena)?.unwrap_or_default())
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
    let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc else {
        return Ok(false);
    };
    let (expr_idx, _) = &**eval_inner;
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr_idx));
    let ExpressionDesc::Pexp_record(record_inner) = &expr.pexp_desc else {
        return Ok(false);
    };
    let (fields, _) = record_inner;

    let mut from_name = false;
    let mut with_fields: Option<&[ExpressionRecordField]> = None;

    for field in arena.expr_field_list(*fields) {
        let Longident::Lident(field_name_idx) = arena.get_longident(field.lid.txt) else {
            continue;
        };
        match arena.get_string(*field_name_idx) {
            "from" => {
                if expr_semantic_string(arena.get_expr(field.expr), arena)?.is_some() {
                    from_name = true;
                }
            }
            "with" => {
                let field_expr =
                    crate::ast_payload::unwrap_braces(arena, arena.get_expr(field.expr));
                if let ExpressionDesc::Pexp_record(with_inner) = &field_expr.pexp_desc {
                    let (import_fields, _) = with_inner;
                    with_fields = Some(arena.expr_field_list(*import_fields));
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
        // OCaml checks the value shape before the key (ast_external_process.ml:283-293).
        let field_expr = arena.get_expr(field.expr);
        let is_string = expr_semantic_string(field_expr, arena)?.is_some();
        if !is_string {
            return Err(PpxError::at_loc(
                field_expr.pexp_loc,
                "Only string values are allowed here.",
            ));
        }
        let Longident::Lident(_) = arena.get_longident(field.lid.txt) else {
            return Err(PpxError::at_loc(
                field_expr.pexp_loc,
                "Field must be a regular key.",
            ));
        };
    }

    Ok(true)
}

/// Extract `@module({from: "...", with: {...}})` payload.
/// Mirrors OCaml `ast_external_process.ml` record-payload path in `parse_external_attributes`.
fn get_module_import_attributes(
    payload: &current::Payload,
    arena: &ParseArena,
) -> PpxResult<Option<(String, ImportAttributes)>> {
    let current::Payload::PStr(items) = payload else {
        return Ok(None);
    };
    if items.len() != 1 {
        return Ok(None);
    }
    let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc else {
        return Ok(None);
    };
    let (expr_idx, _) = &**eval_inner;
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(*expr_idx));
    let ExpressionDesc::Pexp_record(record_inner) = &expr.pexp_desc else {
        return Ok(None);
    };
    let (fields, _) = record_inner;

    let mut from_name: Option<String> = None;
    let mut with_fields: Option<ImportAttributes> = None;

    for field in arena.expr_field_list(*fields) {
        let Longident::Lident(field_name_idx) = arena.get_longident(field.lid.txt) else {
            continue;
        };
        match arena.get_string(*field_name_idx) {
            "from" => {
                if let Some(name) = expr_semantic_string(arena.get_expr(field.expr), arena)? {
                    from_name = Some(name);
                }
            }
            "with" => {
                let field_expr =
                    crate::ast_payload::unwrap_braces(arena, arena.get_expr(field.expr));
                let ExpressionDesc::Pexp_record(with_inner) = &field_expr.pexp_desc else {
                    continue;
                };
                let (import_fields, _) = with_inner;
                let mut import_attributes: ImportAttributes =
                    Vec::with_capacity(import_fields.len());
                for import_field in arena.expr_field_list(*import_fields) {
                    let Longident::Lident(key_idx) = arena.get_longident(import_field.lid.txt)
                    else {
                        continue;
                    };
                    let Some(value) =
                        expr_semantic_string(arena.get_expr(import_field.expr), arena)?
                    else {
                        continue;
                    };
                    let key = match arena.get_string(*key_idx) {
                        "type_" => "type".to_string(),
                        key => key.to_string(),
                    };
                    import_attributes.push((key, value));
                }
                with_fields = Some(import_attributes);
            }
            _ => {}
        }
    }

    Ok(match (from_name, with_fields) {
        (Some(from_name), Some(with_fields)) => Some((from_name, with_fields)),
        _ => None,
    })
}

/// Build FFI type from external description and type info
/// `Ast_external_process.external_decl_of_non_obj` (once the attribute
/// conflicts it rejects have been reported).
fn build_external_decl(desc: &ExternalDesc, prim_name: &str, arity: usize) -> ExternalDecl {
    let mk = |kind: DeclKind, module_: Option<ModuleSource>, scopes: bool, variadic: bool| {
        ExternalDecl {
            kind,
            module_,
            scopes: if scopes {
                desc.scopes.clone()
            } else {
                Vec::new()
            },
            variadic,
            effective_arity: arity as i64,
        }
    };
    // `@module("name")` / `@module("name", "bind")` payload forms.
    let named_module = desc.external_module_name.as_ref().map(|bundle| {
        ModuleSource::ModuleNamed(ExternalModuleName {
            bundle: bundle.clone(),
            module_bind_name: match &desc.module_bind_name {
                Some(name) => ModuleBindName::PhintName(name.clone()),
                None => ModuleBindName::PhintNothing,
            },
            import_attributes: desc.import_attributes.clone(),
        })
    });
    let splice = desc.splice;
    if desc.set_index {
        mk(DeclKind::DeclSetIndex, None, true, false)
    } else if desc.get_index {
        mk(DeclKind::DeclGetIndex, None, true, false)
    } else if desc.module_as_val {
        // A bare `@module`: the external is the module itself.
        let name = prim_name.to_string();
        let kind = if desc.new_name.is_some() {
            DeclKind::DeclNew { name }
        } else {
            DeclKind::DeclVal { name }
        };
        mk(kind, Some(ModuleSource::ModuleItself), false, splice)
    } else if let Some(name) = &desc.send_name {
        mk(
            DeclKind::DeclSend { name: name.clone() },
            None,
            true,
            splice,
        )
    } else if let Some(name) = &desc.new_name {
        mk(
            DeclKind::DeclNew { name: name.clone() },
            named_module,
            true,
            splice,
        )
    } else if let Some(name) = &desc.get_name {
        mk(DeclKind::DeclGet { name: name.clone() }, None, true, false)
    } else if let Some(name) = &desc.set_name {
        mk(DeclKind::DeclSet { name: name.clone() }, None, true, false)
    } else if let Some(name) = &desc.val_name {
        mk(
            DeclKind::DeclVal { name: name.clone() },
            named_module,
            true,
            false,
        )
    } else if let Some(name) = &desc.call_name {
        mk(
            DeclKind::DeclVal { name: name.clone() },
            named_module,
            true,
            splice,
        )
    } else {
        mk(
            DeclKind::DeclVal {
                name: prim_name.to_string(),
            },
            named_module,
            true,
            splice,
        )
    }
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
    valid_first_js_char(first) && chars.all(valid_js_char)
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

/// `External_ffi_types.check_decl`: validate a declaration; returns whether
/// the binding refers to a package-relative path (which disables
/// cross-module inlining). The checks mirror the historical per-runtime-shape
/// checks exactly, including their asymmetries.
fn check_decl(decl: &ExternalDecl, prim_name: &str, loc: LocIdx) -> PpxResult<bool> {
    let mut xrelative = false;
    let mut upgrade = |b: bool| {
        if !xrelative {
            xrelative = b;
        }
    };
    match &decl.module_ {
        Some(ModuleSource::ModuleItself) => {
            upgrade(is_package_relative_path(prim_name));
            if prim_name.is_empty() {
                return Err(PpxError::at_loc(loc, "empty name encountered"));
            }
        }
        module_ => {
            let emn = match module_ {
                Some(ModuleSource::ModuleNamed(emn)) => Some(emn),
                _ => None,
            };
            match &decl.kind {
                DeclKind::DeclVal { name } => {
                    if decl.effective_arity == 0 {
                        upgrade(is_package_relative_path(name));
                        if let Some(emn) = emn {
                            upgrade(is_package_relative_path(&emn.bundle));
                        }
                        validate_global_name(name, loc)?;
                    } else {
                        if let Some(emn) = emn {
                            upgrade(is_package_relative_path(&emn.bundle));
                            validate_external_module_name(emn, Some(loc))?;
                        }
                        validate_global_name(name, loc)?;
                    }
                }
                DeclKind::DeclNew { name } => {
                    if let Some(emn) = emn {
                        upgrade(is_package_relative_path(&emn.bundle));
                        validate_external_module_name(emn, Some(loc))?;
                    }
                    validate_global_name(name, loc)?;
                }
                DeclKind::DeclSend { .. }
                | DeclKind::DeclSet { .. }
                | DeclKind::DeclGet { .. }
                | DeclKind::DeclGetIndex
                | DeclKind::DeclSetIndex => {}
            }
        }
    }
    Ok(xrelative)
}

/// Result of encoding an external: new pval_prim and filtered attributes
pub struct EncodedExternal {
    /// The encoded primitive.
    pub pval_prim: Option<PrimitiveRepr>,
    /// The attributes left after removing the FFI attributes the encoding consumed.
    pub pval_attributes: Vec<Attribute>,
    /// The FFI references a package-relative path, so the external must be
    /// wrapped in `Pstr_include` to prevent cross-module inlining
    /// (ast_external.ml lines 78-98).
    pub has_relative_path: bool,
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
            !EXTERNAL_ATTRS.contains(&name)
        })
        .cloned()
        .collect();
    result.reverse();
    result
}

/// Encode external value description with FFI metadata
pub fn encode_external(vd: &ValueDescription, arena: &mut ParseArena) -> EncodedExternal {
    // `Ast_external_process.handle_attributes_as_prim`.
    let Some(PrimitiveRepr::PrimName(prim_name)) = &vd.pval_prim else {
        return EncodedExternal {
            pval_prim: vd.pval_prim.clone(),
            pval_attributes: vd.pval_attributes.to_vec(),
            has_relative_path: false,
        };
    };
    let prim_name = arena.get_string(*prim_name).to_string();

    if !is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return EncodedExternal {
            pval_prim: vd.pval_prim.clone(),
            pval_attributes: vd.pval_attributes.to_vec(),
            has_relative_path: false,
        };
    }

    // Build arg type specs (mirrors OCaml's fold_right in handle_attributes)
    // Must compute before parse_external_attrs because @val behavior depends on no_arguments
    let vd_type = arena.get_core_type(vd.pval_type).clone();
    let vd_type = fixed_args_as_attributes(&vd_type, arena);
    let (params, arity) = build_arg_type_specs(&vd_type, arena);
    // no_arguments = arg_types_ty = [] in OCaml: checks if there are ANY arrow args,
    // regardless of ignored. Use list_of_arrow directly.
    let no_arguments = list_of_arrow_args(&vd_type, arena).is_empty();

    let desc = checked(parse_external_attrs(
        &vd.pval_attributes,
        prim_name.as_str(),
        no_arguments,
        vd.pval_loc,
        arena,
    ));

    let (ffi, has_relative_path) = if desc.mk_obj {
        // @obj external: build FfiObjCreate with field names
        (build_obj_ffi_type(&vd_type, arena), false)
    } else {
        let decl = build_external_decl(&desc, prim_name.as_str(), arity);
        // `check_ffi` reports whether the FFI references a package-relative
        // path; validation errors were already reported by
        // `validate_external_attribute_errors`.
        let has_relative_path = check_decl(&decl, prim_name.as_str(), vd.pval_loc).unwrap_or(false);
        // `check_return_wrapper` keeps the declared wrapper; whether a
        // unit-returning call is replaced by unit is decided at translation.
        (
            ExternalFfi::FfiBs(params, desc.return_wrapper, decl),
            has_relative_path,
        )
    };

    // Filter out consumed FFI attributes
    let filtered_attrs = filter_ffi_attributes(&vd.pval_attributes, arena);

    EncodedExternal {
        pval_prim: Some(PrimitiveRepr::PrimFfi {
            name: prim_name,
            spec: Box::new(ffi),
        }),
        pval_attributes: filtered_attrs,
        has_relative_path,
    }
}

/// Build FfiObjCreate from the type's labeled arguments.
/// Mirrors OCaml's process_obj which builds arg_kinds from arg_types_ty.
fn build_obj_ffi_type(typ: &CoreType, arena: &mut ParseArena) -> ExternalFfi {
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
                let field_name = get_as_string_attr(&arg.attrs, arena).unwrap_or(label_name);

                let arg_type = refine_arg_type(false, arena.get_core_type(arg.typ), arena);

                match arg_type {
                    Attr::Ignore => {
                        // @ignore: empty_kind with Ignore type (ObjEmpty label)
                        obj_params.push(ObjParam {
                            obj_arg_type: Attr::Ignore,
                            obj_arg_label: Label::ObjEmpty,
                        });
                    }
                    _ => {
                        // Regular arg, or an @as(_) constant (`Attr::ArgCst`),
                        // which also gets an obj_label.
                        obj_params.push(ObjParam {
                            obj_arg_type: arg_type,
                            obj_arg_label: Label::ObjLabel { name: field_name },
                        });
                    }
                }
            }
            ArgLabel::Optional(label_loc) => {
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name = get_as_string_attr(&arg.attrs, arena).unwrap_or(label_name);

                let arg_type =
                    get_opt_arg_type_unchecked(false, arena.get_core_type(arg.typ), arena);

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
                        let for_sure_not_nested = match &arena.get_core_type(arg.typ).ptyp_desc {
                            CoreTypeDesc::Ptyp_constr(inner) if inner.1.is_empty() => {
                                let lid = &inner.0;
                                let longident = arena.get_longident(lid.txt);
                                if let Longident::Lident(s) = longident {
                                    // OCaml `ast_external_process.ml` process_obj uses
                                    // `Ast_core_type.is_builtin_rank0_type`.
                                    is_builtin_rank0_type_name(arena.get_string(*s))
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

    ExternalFfi::FfiObjCreate(obj_params)
}

/// `Ast_external_mk.inline_string`.
pub fn inline_string_primitive(semantic: &str) -> PrimitiveRepr {
    PrimitiveRepr::PrimInlineConst(Box::new(InlineConst::ConstString(semantic.to_string())))
}

/// `Ast_external_mk.inline_bool`.
pub fn inline_bool_primitive(b: bool) -> PrimitiveRepr {
    PrimitiveRepr::PrimInlineConst(Box::new(InlineConst::ConstBool(b)))
}

/// `Ast_external_mk.inline_int`.
pub fn inline_int_primitive(i: i32) -> PrimitiveRepr {
    PrimitiveRepr::PrimInlineConst(Box::new(InlineConst::ConstInt(i)))
}

/// `Ast_external_mk.inline_float`.
pub fn inline_float_primitive(f: &str) -> PrimitiveRepr {
    PrimitiveRepr::PrimInlineConst(Box::new(InlineConst::ConstFloat(f.to_string())))
}

/// `Ast_external_mk.inline_bigint` (compiler/frontend/ast_external_mk.ml):
/// `Bigint_utils.parse_bigint`'s sign flag is true for a positive literal.
pub fn inline_bigint_primitive(s: &str) -> PrimitiveRepr {
    let (positive, digits) = crate::types::typecore::parse_bigint_literal(s);
    PrimitiveRepr::PrimInlineConst(Box::new(InlineConst::ConstBigint { positive, digits }))
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
                    if let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc {
                        let (ref expr, _) = **eval_inner;
                        return Some(crate::ast_payload::unwrap_braces(
                            arena,
                            arena.get_expr(*expr),
                        ));
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

    // bs_builtin_ppx.ml `signature_item_mapper`: an ordinary string or a
    // non-interpolated template becomes an inline string of its semantic value.
    if let Some(semantic) = checked(inline_string_semantic(&expr, arena)) {
        let prim = inline_string_primitive(&semantic);
        return Some(ValueDescription {
            pval_jsx_component: None,
            pval_name: vd.pval_name,
            pval_type: vd.pval_type,
            pval_prim: Some(prim),
            pval_attributes: Attributes::new(), // Clear attributes
            pval_loc: vd.pval_loc,
        });
    }
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(c) => match c {
            Constant::String(_) => None,
            // @inline(42) let x: t
            Constant::Integer(s, None) => {
                let i = arena.get_string(*s).parse::<i32>().ok()?;
                let prim = inline_int_primitive(i);
                Some(ValueDescription {
                    pval_jsx_component: None,
                    pval_name: vd.pval_name,
                    pval_type: vd.pval_type,
                    pval_prim: Some(prim),
                    pval_attributes: Attributes::new(), // Clear attributes
                    pval_loc: vd.pval_loc,
                })
            }
            // @inline(42n) let x: t (bigint)
            Constant::Integer(s, Some('n')) => {
                let prim = inline_bigint_primitive(arena.get_string(*s));
                Some(ValueDescription {
                    pval_jsx_component: None,
                    pval_name: vd.pval_name,
                    pval_type: vd.pval_type,
                    pval_prim: Some(prim),
                    pval_attributes: Attributes::new(), // Clear attributes
                    pval_loc: vd.pval_loc,
                })
            }
            // @inline(3.14) let x: t
            Constant::Float(s, None) => {
                let prim = inline_float_primitive(arena.get_string(*s));
                Some(ValueDescription {
                    pval_jsx_component: None,
                    pval_name: vd.pval_name,
                    pval_type: vd.pval_type,
                    pval_prim: Some(prim),
                    pval_attributes: Attributes::new(), // Clear attributes
                    pval_loc: vd.pval_loc,
                })
            }
            _ => None,
        },
        // @inline(true) or @inline(false) let x: t
        ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => {
            let longident = arena.get_longident(lid.txt);
            if let Longident::Lident(name_idx) = longident {
                let name = arena.get_string(*name_idx);
                if name == "true" || name == "false" {
                    let prim = inline_bool_primitive(name == "true");
                    return Some(ValueDescription {
                        pval_jsx_component: None,
                        pval_name: vd.pval_name,
                        pval_type: vd.pval_type,
                        pval_prim: Some(prim),
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

/// The `Pexp_constant (Pconst_string _) | Pexp_template {source_segments =
/// [_]; values = []}` case of OCaml's `@inline` handling: the expression's
/// semantic string.
fn inline_string_semantic(expr: &Expression, arena: &ParseArena) -> PpxResult<Option<String>> {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(Constant::String(_)) => expr_semantic_string(expr, arena),
        ExpressionDesc::Pexp_template(template)
            if template.source_segments.len() == 1 && template.values.is_empty() =>
        {
            expr_semantic_string(expr, arena)
        }
        _ => Ok(None),
    }
}

/// A payload read in the rewrite, which runs only on a tree the check pass
/// (`ppx/check.rs`) accepted after raising, in the mapper's order, where the
/// OCaml readers raise on the same payload.
fn checked<T>(read: PpxResult<T>) -> T {
    read.expect("the check pass raised on this payload")
}
/// Transform an @inline let binding into a primitive
fn transform_inline_binding(
    pval_name: &Located<StrIdx>,
    expr: &Expression,
    pvb_loc: LocIdx,
    pstr_loc: LocIdx,
    arena: &mut ParseArena,
) -> Option<StructureItem> {
    // bs_builtin_ppx.ml `structure_item_mapper` matches
    // `(Ast_payload.unwrap_braces pvb_expr).pexp_desc`.
    let expr = &crate::ast_payload::unwrap_braces(arena, expr).clone();
    // @inline let x = "string" (or a non-interpolated template)
    if let Some(semantic) = checked(inline_string_semantic(expr, arena)) {
        let prim = inline_string_primitive(&semantic);
        return Some(StructureItem {
            pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(ValueDescription {
                pval_jsx_component: None,
                pval_name: Located {
                    txt: pval_name.txt,
                    loc: pval_name.loc,
                },
                pval_type: arena.ast_literal_type_string(),
                pval_prim: Some(prim),
                pval_attributes: Attributes::new(),
                pval_loc: pvb_loc,
            })),
            pstr_loc,
        });
    }
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(c) => match c {
            Constant::String(_) => None,
            // @inline let x = 42
            Constant::Integer(s, None) => {
                let i = arena.get_string(*s).parse::<i32>().ok()?;
                let prim = inline_int_primitive(i);
                Some(StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(ValueDescription {
                        pval_jsx_component: None,
                        pval_name: Located {
                            txt: pval_name.txt,
                            loc: pval_name.loc,
                        },
                        pval_type: arena.ast_literal_type_int(),
                        pval_prim: Some(prim),
                        pval_attributes: Attributes::new(),
                        pval_loc: pvb_loc,
                    })),
                    pstr_loc,
                })
            }
            // @inline let x = 3.14
            Constant::Float(s, None) => {
                let prim = inline_float_primitive(arena.get_string(*s));
                Some(StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(ValueDescription {
                        pval_jsx_component: None,
                        pval_name: Located {
                            txt: pval_name.txt,
                            loc: pval_name.loc,
                        },
                        pval_type: arena.ast_literal_type_float(),
                        pval_prim: Some(prim),
                        pval_attributes: Attributes::new(),
                        pval_loc: pvb_loc,
                    })),
                    pstr_loc,
                })
            }
            _ => None,
        },
        // @inline let x = true or @inline let x = false
        ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => {
            let longident = arena.get_longident(lid.txt);
            if let Longident::Lident(name_idx) = longident {
                let name = arena.get_string(*name_idx);
                if name == "true" || name == "false" {
                    let prim = inline_bool_primitive(name == "true");
                    return Some(StructureItem {
                        pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(ValueDescription {
                            pval_jsx_component: None,
                            pval_name: Located {
                                txt: pval_name.txt,
                                loc: pval_name.loc,
                            },
                            pval_type: arena.ast_literal_type_bool(),
                            pval_prim: Some(prim),
                            pval_attributes: Attributes::new(),
                            pval_loc: pvb_loc,
                        })),
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
        // A payload the parser did not turn into `Pexp_todo`, or one from a
        // v0 PPX. A payload other than a string gives no message
        // (ast_exp_extension.ml `handle_extension`).
        "todo" => todo(
            checked(payload_semantic_string(payload, arena)),
            arena,
            ext_loc,
        ),
        "raw" => handle_raw(expr, payload, arena, arena.prim_raw_expr(), ext_loc),
        "ffi" => handle_ffi(expr, payload, arena, ext_loc),
        _ => expr.clone(),
    }
}

/// `Ast_exp_extension.todo` (ast_exp_extension.ml:26-50):
/// `Stdlib_JsError.throwWithMessage` applied to
/// `"<file>:<line>:<start>-<end> - Todo[: message]"`, located at `%todo`.
/// The message names the file's base name and columns, like `__LOC__`. The
/// warning is emitted by the warning pre-pass.
fn todo(message: Option<String>, arena: &mut ParseArena, loc: LocIdx) -> Expression {
    // The text embeds source coordinates: a location-free parse is redone
    // with locations, as for `__LOC__`.
    arena.require_locations();
    let start = *arena.loc_start(loc);
    let end = *arena.loc_end(loc);
    // `Location.get_pos_info loc.loc_start`.
    let start_col = start.cnum - start.bol;
    let end_col = end.cnum - start.cnum + start_col;
    let mut text = format!(
        "{}:{}:{}-{}",
        crate::misc::filename_basename(arena.get_string(start.file_name)),
        start.line,
        start_col,
        end_col
    );
    match &message {
        None => text.push_str(" - Todo"),
        Some(msg) => {
            text.push_str(" - Todo: ");
            text.push_str(msg);
        }
    }
    // The compilation unit, not `JsError`: a user module of that name would
    // shadow the `Stdlib` alias.
    let js_error = arena.push_lident("Stdlib_JsError");
    let throw_lid = arena.push_ldot(js_error, "throwWithMessage");
    let funct = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: throw_lid,
            loc,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };
    let argument = Expression {
        pexp_desc: ExpressionDesc::Pexp_constant(arena.string_constant(&text)),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };
    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
            funct: arena.push_expr(funct),
            args: {
                let items = [(ArgLabel::Nolabel, arena.push_expr(argument))];
                arena.push_apply_args(&items)
            },
            partial: false,
            transformed_jsx: false,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// ast_external_mk.ml `local_external_apply loc ~pval_prim ~pval_type:(_ => _) [arg]`
/// for a `#raw_expr`-style primitive: `let module J = struct external
/// unsafe_expr: _ => _ = pval_prim end in J.unsafe_expr(arg)`.
fn raw_local_external_apply(
    arena: &mut ParseArena,
    loc: LocIdx,
    pval_prim: StrIdx,
    str_exp: Expression,
) -> ExpressionDesc {
    // Use none_loc() for types, matching OCaml's Ast_helper.Typ.any()
    // which uses default_loc (= Location.none = in_file "_none_")
    // In the AST, Location is an alias for LocIdx
    let none_loc = arena.none_loc();

    // Create the type: _ -> _
    let any_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_any,
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let pval_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                fixed: None,
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(any_type.clone()),
            }),
            arena.push_core_type(any_type),
            arena.push_arity(Some(1)),
        ))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create strings for the module/function names
    let module_name_idx = arena.intern_string("J");
    let func_name_idx = arena.intern_string("unsafe_expr");

    // Create the value description (external primitive)
    let vd = ValueDescription {
        pval_jsx_component: None,
        pval_name: Located {
            txt: func_name_idx,
            loc,
        },
        pval_type: arena.push_core_type(pval_type),
        pval_prim: Some(PrimitiveRepr::PrimName(pval_prim)),
        pval_attributes: Attributes::new(),
        pval_loc: loc,
    };

    // Create the module structure: struct external unsafe_expr: _ -> _ = "#raw_expr" end
    let mod_structure = vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(vd)),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(Box::new(mod_structure)),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    // Create the longident J.unsafe_expr
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    // Create the function application: J.unsafe_expr("code")
    let func_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: j_unsafe_expr,
            loc,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    let apply_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
            funct: arena.push_expr(func_ident),
            args: {
                let items = [(ArgLabel::Nolabel, arena.push_expr(str_exp))];
                arena.push_apply_args(&items)
            },
            partial: false,
            transformed_jsx: false,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    ExpressionDesc::Pexp_letmodule(Box::new((
        Located {
            txt: module_name_idx,
            loc,
        },
        arena.push_mod_expr(mod_expr),
        arena.push_expr(apply_expr),
    )))
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
    let Some((code, payload_loc, _)) = payload_raw_source_info(payload, arena) else {
        return expr.clone();
    };
    let str_exp = {
        let Payload::PStr(items) = payload else {
            unreachable!("payload_raw_source_info matched a structure payload")
        };
        let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc else {
            unreachable!("payload_raw_source_info matched an eval item")
        };
        let e = crate::ast_payload::unwrap_braces(arena, arena.get_expr(eval_inner.0));
        let (e_loc, e_attributes) = (e.pexp_loc, e.pexp_attributes.clone());
        // `{expression with pexp_desc = Pexp_constant (Pconst_string
        // (String_literal.string_from_semantic str))}`
        Expression {
            pexp_desc: ExpressionDesc::Pexp_constant(arena.string_constant(&code)),
            pexp_loc: e_loc,
            pexp_attributes: e_attributes,
        }
    };
    debug_assert_eq!(str_exp.pexp_loc, payload_loc);
    raw_expression(str_exp, &code, arena, pval_prim, ext_loc)
}

/// `Ast_exp_handle_external.raw_expression`: `str_exp` is the string
/// constant holding the JavaScript source `code`, whose location and
/// attributes the lowered expression keeps.
fn raw_expression(
    str_exp: Expression,
    code: &str,
    arena: &mut ParseArena,
    pval_prim: StrIdx,
    ext_loc: LocIdx,
) -> Expression {
    let payload_loc = str_exp.pexp_loc;
    // Check if the JS string contains a function
    let is_function = is_js_function(code);

    // OCaml's local_external_apply uses `loc` from the extension identifier's location
    // ({txt; loc} pattern in handle_extension), NOT the full expression's pexp_loc
    let loc = ext_loc;

    let none_loc = arena.none_loc();
    let payload_attributes = str_exp.pexp_attributes.clone();
    let desc = raw_local_external_apply(arena, loc, pval_prim, str_exp);

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
            Payload::PStr(Box::default()),
        );
        let mut attrs = vec![internal_expansive];
        attrs.extend(payload_attributes.iter().cloned());
        Attributes::from_vec(attrs)
    } else {
        payload_attributes
    };

    Expression {
        pexp_desc: desc,
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
    let code_str = payload_raw_source_info(payload, arena).map(|(code, _, _)| code);

    let arity = code_str.as_ref().and_then(|s| detect_js_function_arity(s));

    // Create the raw expression (same as %raw with #raw_expr).
    // OCaml passes the extension identifier location into local_external_apply.
    let raw_prim = prim_str(arena, "#raw_expr");
    let raw_expr = handle_raw(expr, payload, arena, raw_prim, ext_loc);
    ffi_expression(raw_expr, arity, arena)
}

/// `Ast_exp_handle_external.ffi_expression`: wrap the lowered `%raw` in a
/// type constraint based on the arity of the JavaScript function.
fn ffi_expression(
    raw_expr: Expression,
    arity: Option<usize>,
    arena: &mut ParseArena,
) -> Expression {
    // Wrap in type constraint based on arity
    if let Some(arity) = arity {
        // OCaml constraints the rewritten expression at e.pexp_loc where e is the
        // payload string expression returned by raw_as_string_exp_exn.
        let loc = raw_expr.pexp_loc;

        let any_type = CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_any,
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        };
        let any_type_idx = arena.push_core_type(any_type);

        // Build arrow type: (_, _, ...) -> _ with effective_arity args
        let effective_arity = if arity == 0 { 1 } else { arity };
        let args: Vec<_> = (0..effective_arity)
            .map(|_| TypeArg {
                fixed: None,
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: any_type_idx,
            })
            .collect();

        // Current Ast_helper.Typ.arrow stores every argument in one n-ary
        // Ptyp_arrow. The same `any` node is shared by all arguments and the
        // return type, matching ast_exp_handle_external.ml:81-90.
        let total_arity = arena.push_arity(Some(effective_arity as i32));
        let first = args[0].clone();
        arena.set_nary_arrow_args(total_arity, args);
        let arrow_type_idx = arena.push_core_type(CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((
                Box::new(first),
                any_type_idx,
                total_arity,
            ))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        });

        let raw_expr_idx = arena.push_expr(raw_expr);
        Expression {
            pexp_desc: ExpressionDesc::Pexp_constraint(Box::new((raw_expr_idx, arrow_type_idx))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        raw_expr
    }
}

/// `Ast_exp_handle_external.raw_source_expression`: the string constant
/// holding the JavaScript source of a raw node, located at its payload. The
/// warning pre-pass validates the source like a raw payload.
fn raw_source_expression(source: &RawSource, arena: &mut ParseArena) -> (Expression, String) {
    let code = crate::ast_raw::js_source(arena, source);
    let loc = crate::ast_raw::payload_loc(arena, source);
    (
        Expression {
            pexp_desc: ExpressionDesc::Pexp_constant(arena.string_constant(&code)),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        },
        code,
    )
}

/// `Ast_exp_handle_external.handle_raw_node`: lower `%raw` or `%ffi`,
/// located at `%raw`/`%ffi`.
fn handle_raw_node(raw: &PexpRaw, arena: &mut ParseArena) -> Expression {
    let (str_exp, code) = raw_source_expression(&raw.source, arena);
    let raw_prim = arena.prim_raw_expr();
    let raw_expr = raw_expression(str_exp, &code, arena, raw_prim, raw.name_loc);
    match raw.kind {
        RawKind::Expression => raw_expr,
        RawKind::Function => ffi_expression(raw_expr, detect_js_function_arity(&code), arena),
    }
}

/// `Ast_exp_handle_external.handle_raw_structure_node`: lower `%%raw`,
/// located at `%%raw`.
fn handle_raw_structure_node(raw: &PstrRaw, arena: &mut ParseArena) -> StructureItem {
    let (str_exp, _) = raw_source_expression(&raw.source, arena);
    raw_structure(str_exp, arena, raw.name_loc)
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
    // (`Ast_payload.raw_as_string_exp_exn ~kind:Raw_program`).
    let Some((code, str_loc, _)) = payload_raw_source_info(payload, arena) else {
        return item.clone();
    };
    let str_exp = {
        let Payload::PStr(items) = payload else {
            unreachable!("payload_raw_source_info matched a structure payload")
        };
        let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc else {
            unreachable!("payload_raw_source_info matched an eval item")
        };
        let expr = arena.get_expr(eval_inner.0);
        let (expr_loc, expr_attributes) = (expr.pexp_loc, expr.pexp_attributes.clone());
        Expression {
            pexp_desc: ExpressionDesc::Pexp_constant(arena.string_constant(&code)),
            pexp_loc: expr_loc,
            pexp_attributes: expr_attributes,
        }
    };
    debug_assert_eq!(str_exp.pexp_loc, str_loc);
    raw_structure(str_exp, arena, ext_loc)
}

/// `Ast_exp_handle_external.raw_structure`: `str_exp` is the string constant
/// holding the JavaScript statements.
fn raw_structure(str_exp: Expression, arena: &mut ParseArena, ext_loc: LocIdx) -> StructureItem {
    let str_loc = str_exp.pexp_loc;
    // OCaml: loc comes from the extension identifier's location ({txt = "raw"; loc})
    let loc = ext_loc;
    let none_loc = arena.none_loc();

    // Create the type: _ -> _
    let any_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_any,
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    let pval_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(TypeArg {
                fixed: None,
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: arena.push_core_type(any_type.clone()),
            }),
            arena.push_core_type(any_type),
            arena.push_arity(Some(1)),
        ))),
        ptyp_loc: none_loc,
        ptyp_attributes: Attributes::new(),
    };

    // Create strings for the module/function names
    let module_name_idx = arena.intern_string("J");
    let func_name_idx = arena.intern_string("unsafe_expr");

    // Create the value description (external primitive) - uses #raw_stmt for structure level
    let vd = ValueDescription {
        pval_jsx_component: None,
        pval_name: Located {
            txt: func_name_idx,
            loc,
        },
        pval_type: arena.push_core_type(pval_type),
        pval_prim: Some(PrimitiveRepr::PrimName(arena.prim_raw_stmt())),
        pval_attributes: Attributes::new(),
        pval_loc: loc,
    };

    // Create the module structure
    let mod_structure = vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(vd)),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(Box::new(mod_structure)),
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
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: j_unsafe_expr,
            loc,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    let apply_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
            funct: arena.push_expr(func_ident),
            args: {
                let items = [(ArgLabel::Nolabel, arena.push_expr(str_exp))];
                arena.push_apply_args(&items)
            },
            partial: false,
            transformed_jsx: false,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // Create the let module expression
    // Inherit the template attribute from the string expression (res.template)
    let letmodule_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_letmodule(Box::new((
            Located {
                txt: module_name_idx,
                loc,
            },
            arena.push_mod_expr(mod_expr),
            arena.push_expr(apply_expr),
        ))),
        pexp_loc: str_loc, // Use the string expression's location for outer expr
        pexp_attributes: payload_attributes,
    };

    // Wrap in Pstr_eval - OCaml's Ast_helper.Str.eval uses default_loc (= Location.none)
    // when no ~loc is passed, so we use none_loc here
    StructureItem {
        pstr_desc: StructureItemDesc::Pstr_eval(Box::new((
            arena.push_expr(letmodule_expr),
            Attributes::new(),
        ))),
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

    // `self.structure_item` on each item: `%%raw`, `%%private` and
    // `Pstr_raw` are only expanded by `structure_mapper`, so here they stay
    // as written (and `Typemod_hide.check` rejects them).
    let rewritten_items: Vec<StructureItem> = items
        .iter()
        .flat_map(|item| {
            if is_structure_mapper_extension(item, arena) {
                vec![item.clone()]
            } else {
                rewrite_structure_item(item, arena)
            }
        })
        .collect();

    check_private_extension_items(&rewritten_items, arena)?;

    Ok(wrap_in_local_module(rewritten_items, loc, arena))
}

fn private_extension_structure_items(
    payload: &Payload,
    loc: LocIdx,
) -> PpxResult<&Vec<StructureItem>> {
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

/// `%%raw`/`%%private` and `Pstr_raw`: the structure items
/// `Bs_builtin_ppx.structure_mapper` expands itself, which `structure_item`
/// leaves alone.
fn is_structure_mapper_extension(item: &StructureItem, arena: &ParseArena) -> bool {
    match &item.pstr_desc {
        StructureItemDesc::Pstr_raw(_) => true,
        StructureItemDesc::Pstr_extension(inner) => {
            matches!(arena.get_string(inner.0.0.txt), "raw" | "private")
        }
        _ => false,
    }
}

/// OCaml `Typemod_hide.check` (typemod_hide.ml:53-57). `expand_reverse` passes
/// the accumulated items in reverse, so the last offending item is reported.
fn check_private_extension_items(items: &[StructureItem], arena: &ParseArena) -> PpxResult<()> {
    for item in items.iter().rev() {
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
    match &item.pstr_desc {
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
    let ModuleExprDesc::Pmod_constraint(inner_idx, _) = &mod_expr.pmod_desc else {
        return false;
    };

    let inner = arena.get_mod_expr(*inner_idx);
    let ModuleExprDesc::Pmod_structure(items) = &inner.pmod_desc else {
        return false;
    };

    matches!(
        items.as_slice(),
        [item] if matches!(&item.pstr_desc, StructureItemDesc::Pstr_primitive(_))
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
        Payload::PStr(Box::default()),
    );

    // Create the module binding:
    // module local_N = { ... } with @internal.local attribute
    let module_binding = current::ModuleBinding {
        pmb_name: Located {
            txt: local_name_idx,
            loc: combined_loc,
        },
        pmb_expr: arena.push_mod_expr(ModuleExpr {
            pmod_desc: ModuleExprDesc::Pmod_structure(Box::new(rewritten_items)),
            pmod_loc: combined_loc,
            pmod_attributes: Attributes::new(),
        }),
        pmb_attributes: Attributes::from_vec(vec![internal_local_attr]),
        pmb_loc: combined_loc,
    };

    let module_item = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_module(Box::new(module_binding)),
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
        pstr_desc: StructureItemDesc::Pstr_open(Box::new(open_desc)),
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
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: unsafe_await_lid,
            loc: ghost_loc,
        }),
        pexp_loc: ghost_loc,
        pexp_attributes: Attributes::new(),
    };

    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
            funct: arena.push_expr(func_ident),
            args: {
                let items = [(ArgLabel::Nolabel, arena.push_expr(inner))];
                arena.push_apply_args(&items)
            },
            partial: false,
            transformed_jsx: false,
        }),
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
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: unsafe_async_lid,
            loc,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
            funct: arena.push_expr(func_ident),
            args: {
                let items = [(ArgLabel::Nolabel, arena.push_expr(inner))];
                arena.push_apply_args(&items)
            },
            partial: false,
            transformed_jsx: false,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Wrap the result of one n-ary function with `unsafe_async`.
/// OCaml: ast_async.ml add_promise_to_result
fn add_promise_to_fun_body(expr: &Expression, loc: LocIdx, arena: &mut ParseArena) -> Expression {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            let body = arena.get_expr(arena.nary_fun_body(inner)).clone();
            let wrapped_body = wrap_with_unsafe_async(body, loc, arena);
            Expression {
                pexp_desc: ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: inner.arg_label,
                    default: inner.default,
                    lhs: inner.lhs,
                    rhs: arena.push_expr(wrapped_body),
                    arity: inner.arity,
                    is_async: inner.is_async,
                })),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        }
        _ => wrap_with_unsafe_async(expr.clone(), loc, arena),
    }
}

// ========== Module-Level Await Transformation ==========

/// `Ast_await.remove_awaits`: `m` without its outer awaits, e.g.
/// `await (await M)`, whose attributes (e.g. `@warning`) stay on the module
/// they wrap, after its own as in the v0 encoding, and whether it had any
/// (`awaited` for the awaits already removed).
fn remove_awaits(
    awaited: bool,
    m: &current::ModuleExpr,
    arena: &ParseArena,
) -> (bool, current::ModuleExpr) {
    match &m.pmod_desc {
        ModuleExprDesc::Pmod_await(inner) => {
            let mut inner = arena.get_mod_expr(*inner).clone();
            let mut attrs = inner.pmod_attributes.to_vec();
            attrs.extend(m.pmod_attributes.iter().cloned());
            inner.pmod_attributes = attrs.into();
            remove_awaits(true, &inner, arena)
        }
        _ => (awaited, m.clone()),
    }
}

/// `Ast_await.awaited_module_path`: an awaited module path, `await M`, and
/// `await (M: S)` or `(await M: S)`, where `await` may be repeated. Returns
/// the path of `M`; the module to import, which is `e` without its awaits,
/// whose attributes stay on the module they wrap; and `S` for the constrained
/// forms. It is a dynamic import when `S` is absent or a module type path.
fn awaited_module_path(
    e: &current::ModuleExpr,
    arena: &mut ParseArena,
) -> Option<(Located<LidentIdx>, current::ModuleExpr, Option<ModTypeIdx>)> {
    match remove_awaits(false, e, arena) {
        (true, imported) => match &imported.pmod_desc {
            ModuleExprDesc::Pmod_ident(lid) => Some((*lid, imported.clone(), None)),
            ModuleExprDesc::Pmod_constraint(m, mty) => {
                awaited_constraint(true, &imported, *m, *mty, arena)
            }
            _ => None,
        },
        (false, constrained) => match &constrained.pmod_desc {
            ModuleExprDesc::Pmod_constraint(m, mty) => {
                awaited_constraint(false, &constrained, *m, *mty, arena)
            }
            _ => None,
        },
    }
}

fn awaited_constraint(
    awaited: bool,
    constrained: &current::ModuleExpr,
    m: ModExprIdx,
    mty: ModTypeIdx,
    arena: &mut ParseArena,
) -> Option<(Located<LidentIdx>, current::ModuleExpr, Option<ModTypeIdx>)> {
    let m = arena.get_mod_expr(m).clone();
    match remove_awaits(awaited, &m, arena) {
        (true, path) => {
            let ModuleExprDesc::Pmod_ident(lid) = &path.pmod_desc else {
                return None;
            };
            let lid = *lid;
            let path_idx = arena.push_mod_expr(path);
            Some((
                lid,
                current::ModuleExpr {
                    pmod_desc: ModuleExprDesc::Pmod_constraint(path_idx, mty),
                    pmod_loc: constrained.pmod_loc,
                    pmod_attributes: constrained.pmod_attributes.clone(),
                },
                Some(mty),
            ))
        }
        (false, _) => None,
    }
}

/// The shape `awaited_module_path` recognizes, without building the module
/// to import: `None` when it is not an awaited module path, else its
/// constraint's module type, if any.
fn awaited_module_path_kind(
    e: &current::ModuleExpr,
    arena: &ParseArena,
) -> Option<Option<ModTypeIdx>> {
    fn strip<'a>(
        awaited: bool,
        m: &'a current::ModuleExpr,
        arena: &'a ParseArena,
    ) -> (bool, &'a current::ModuleExpr) {
        match &m.pmod_desc {
            ModuleExprDesc::Pmod_await(inner) => strip(true, arena.get_mod_expr(*inner), arena),
            _ => (awaited, m),
        }
    }
    let (awaited, m) = strip(false, e, arena);
    match &m.pmod_desc {
        ModuleExprDesc::Pmod_ident(_) if awaited => Some(None),
        ModuleExprDesc::Pmod_constraint(inner, mty) => {
            let (awaited, path) = strip(awaited, arena.get_mod_expr(*inner), arena);
            (awaited && matches!(&path.pmod_desc, ModuleExprDesc::Pmod_ident(_)))
                .then_some(Some(*mty))
        }
        _ => None,
    }
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

/// `Ast_await.create_await_module_expression`: the dynamic import `e` of
/// `imported`, as returned by `awaited_module_path`, becomes
/// `unpack(await import(module(M: __M0__)))`.
fn create_await_module_expression(
    e: &current::ModuleExpr,
    module_type_lid: Located<LidentIdx>,
    imported: current::ModuleExpr,
    arena: &mut ParseArena,
) -> current::ModuleExpr {
    let pmod_loc = e.pmod_loc;

    let pack_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_pack(arena.push_mod_expr(imported)),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    let package_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_package(Box::new((module_type_lid, vec![]))),
        ptyp_loc: pmod_loc,
        ptyp_attributes: Attributes::new(),
    };

    let constrained_pack = Expression {
        pexp_desc: ExpressionDesc::Pexp_constraint(Box::new((
            arena.push_expr(pack_expr),
            arena.push_core_type(package_type),
        ))),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    let module_str = arena.intern_string("Primitive_module");
    let module_lident = arena.push_lident_from_idx(module_str);
    let import_lid = arena.push_ldot_static(module_lident, "import");

    let import_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: import_lid,
            loc: pmod_loc,
        }),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    let import_apply = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
            funct: arena.push_expr(import_ident),
            args: {
                let items = [(ArgLabel::Nolabel, arena.push_expr(constrained_pack))];
                arena.push_apply_args(&items)
            },
            partial: false,
            transformed_jsx: false,
        }),
        pexp_loc: pmod_loc,
        pexp_attributes: Attributes::new(),
    };

    let await_expr = transform_await(import_apply, pmod_loc, arena);

    // `{e with pmod_desc = Pmod_unpack ...}` keeps the await node's attributes.
    current::ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_unpack(arena.push_expr(await_expr)),
        pmod_loc,
        pmod_attributes: e.pmod_attributes.clone(),
    }
}

/// `local_module_type_decl` (bs_builtin_ppx.ml): `module type __List__ =
/// module type of List`, the module type a dynamic import of `List` unpacks
/// to, declared once per module.
fn local_module_type_decl(
    await_context: &mut std::collections::HashSet<String>,
    lid: Located<LidentIdx>,
    me: current::ModuleExpr,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    let name = local_module_type_name(lid.txt, arena);
    if !await_context.insert(name.clone()) {
        return vec![];
    }
    let loc = lid.loc;
    let name_idx = arena.intern_string(&name);
    let me_idx = arena.push_mod_expr(me);
    let module_type_idx = arena.push_mod_type(current::ModuleType {
        pmty_desc: ModuleTypeDesc::Pmty_typeof(me_idx),
        pmty_loc: loc,
        pmty_attributes: Attributes::new(),
    });
    vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_modtype(Box::new(current::ModuleTypeDeclaration {
            pmtd_name: Located { txt: name_idx, loc },
            pmtd_type: Some(module_type_idx),
            pmtd_attributes: Attributes::new(),
            pmtd_loc: loc,
        })),
        pstr_loc: loc,
    }]
}

/// Spelunk through an expression to find dynamic module imports.
///
/// For each found, creates a module type declaration to hoist to structure level.
/// Uses a context HashSet to track already-created module type names to avoid duplicates.
///
/// OCaml `aux` in bs_builtin_ppx.ml `spelunk_vbs` (lines 752-793). OCaml
/// evaluates the right operand of `@` first, so side effects on `context`
/// happen right to left while results keep source order.
fn spelunk_expression_for_await_module_types(
    expr: &Expression,
    context: &mut std::collections::HashSet<String>,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_, ref mod_expr, ref body) = **inner;
            let mod_expr_val = arena.get_mod_expr(*mod_expr).clone();
            match awaited_module_path(&mod_expr_val, arena) {
                Some((module_lid, imported, None)) => {
                    // Before `aux expr`, which may import the same module.
                    let mut results = local_module_type_decl(context, module_lid, imported, arena);
                    let body_expr = arena.get_expr(*body).clone();
                    results.extend(spelunk_expression_for_await_module_types(
                        &body_expr, context, arena,
                    ));
                    results
                }
                _ => vec![],
            }
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (_, ref bindings, ref body) = *inner;
            let bindings = arena.vb_list(*bindings).to_vec();
            let binding_results =
                spelunk_value_bindings_for_await_module_types(&bindings, context, arena);
            let body_expr = arena.get_expr(*body).clone();
            let mut results = spelunk_expression_for_await_module_types(&body_expr, context, arena);
            results.extend(binding_results);
            results
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (_, ref then_idx, ref else_idx) = **inner;
            let Some(else_idx) = else_idx else {
                return vec![];
            };
            let else_expr = arena.get_expr(*else_idx).clone();
            let else_results =
                spelunk_expression_for_await_module_types(&else_expr, context, arena);
            let then_expr = arena.get_expr(*then_idx).clone();
            let mut results = spelunk_expression_for_await_module_types(&then_expr, context, arena);
            results.extend(else_results);
            results
        }
        ExpressionDesc::Pexp_braces(braces) => {
            let inner = arena.get_expr(braces.expr).clone();
            spelunk_expression_for_await_module_types(&inner, context, arena)
        }
        // `aux consequent @ aux alternate`: the alternate is evaluated first.
        ExpressionDesc::Pexp_ternary(inner) => {
            let (_, consequent, alternate) = **inner;
            let alternate = arena.get_expr(alternate).clone();
            let alternate_results =
                spelunk_expression_for_await_module_types(&alternate, context, arena);
            let consequent = arena.get_expr(consequent).clone();
            let mut results =
                spelunk_expression_for_await_module_types(&consequent, context, arena);
            results.extend(alternate_results);
            results
        }
        ExpressionDesc::Pexp_construct(_, args) if args.txt.len() == 1 => {
            let e_expr = arena.get_expr(arena.expr_list(args.txt)[0]).clone();
            spelunk_expression_for_await_module_types(&e_expr, context, arena)
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun { rhs: ref body, .. } = **inner;
            let body_expr = arena.get_expr(*body).clone();
            spelunk_expression_for_await_module_types(&body_expr, context, arena)
        }
        // OCaml keeps newtypes on `Pexp_fun`; Rust wraps them in `Pexp_newtype`.
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
            let (ref scrut_idx, ref cases) = *inner;
            // `List.fold_left (fun acc case -> aux case.pc_rhs @ acc) [] cases`
            let mut case_results = Vec::new();
            for case in arena.case_list(*cases).to_vec() {
                let case_rhs = arena.get_expr(case.pc_rhs).clone();
                let mut results =
                    spelunk_expression_for_await_module_types(&case_rhs, context, arena);
                results.extend(case_results);
                case_results = results;
            }
            let scrut_expr = arena.get_expr(*scrut_idx).clone();
            let mut results =
                spelunk_expression_for_await_module_types(&scrut_expr, context, arena);
            results.extend(case_results);
            results
        }
        _ => vec![],
    }
}

/// OCaml `spelunk_vbs` (bs_builtin_ppx.ml:752-795):
/// `aux pvb_expr @ spelunk_vbs acc tl`, whose tail is evaluated first.
fn spelunk_value_bindings_for_await_module_types(
    bindings: &[ValueBinding],
    context: &mut std::collections::HashSet<String>,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    let Some((first, rest)) = bindings.split_first() else {
        return vec![];
    };
    let rest_results = spelunk_value_bindings_for_await_module_types(rest, context, arena);
    let first_expr = arena.get_expr(first.pvb_expr).clone();
    let mut results = spelunk_expression_for_await_module_types(&first_expr, context, arena);
    results.extend(rest_results);
    results
}

/// The `Pstr_module` case of `structure_mapper` (bs_builtin_ppx.ml) for a
/// dynamic import `module M = await List`: the module type declaration (once
/// per module) and the rewritten binding. `module M = await (List: ListType)`
/// uses `ListType` and declares no module type.
fn transform_module_await(
    mb: &current::ModuleBinding,
    original_pstr_loc: LocIdx,
    await_context: &mut std::collections::HashSet<String>,
    arena: &mut ParseArena,
) -> Option<Vec<StructureItem>> {
    let mod_expr = arena.get_mod_expr(mb.pmb_expr).clone();
    let (mut items, module_type_lid, imported) = match awaited_module_path(&mod_expr, arena)? {
        (module_lid, imported, None) => {
            let module_type_lid = Located {
                txt: arena.push_lident(&local_module_type_name(module_lid.txt, arena)),
                loc: mod_expr.pmod_loc,
            };
            // Before mapping the rest, which may import the same module.
            let items = local_module_type_decl(await_context, module_lid, imported.clone(), arena);
            (items, module_type_lid, imported)
        }
        (_, imported, Some(mty)) => match &arena.get_mod_type(mty).pmty_desc {
            ModuleTypeDesc::Pmty_ident(module_type_lid) => (Vec::new(), *module_type_lid, imported),
            _ => return None,
        },
    };
    let transformed_mod_expr =
        create_await_module_expression(&mod_expr, module_type_lid, imported, arena);
    items.push(StructureItem {
        pstr_desc: StructureItemDesc::Pstr_module(Box::new(current::ModuleBinding {
            pmb_name: mb.pmb_name,
            pmb_expr: arena.push_mod_expr(transformed_mod_expr),
            pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena).into(),
            pmb_loc: mb.pmb_loc,
        })),
        pstr_loc: original_pstr_loc,
    });
    Some(items)
}

// ========== Expression Rewriting ==========

/// Rewrite a single attribute, transforming strings in its payload
fn rewrite_attribute(attr: &Attribute, arena: &mut ParseArena) -> Attribute {
    let (name, payload) = attr;
    (*name, rewrite_payload(payload, arena))
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

/// `Ast_attributes.process_attributes_rev` (ast_attributes.ml:77-81): the last
/// `@this` attribute and the other attributes in reverse order.
fn process_attributes_rev(
    attrs: &[Attribute],
    arena: &ParseArena,
) -> (Option<Attribute>, Vec<Attribute>) {
    let mut this_attr = None;
    let mut acc = Vec::new();
    for attr in attrs {
        if arena.get_string(attr.0.txt) == "this" {
            this_attr = Some(attr.clone());
        } else {
            acc.insert(0, attr.clone());
        }
    }
    (this_attr, acc)
}

/// The `Otag` case of `Ast_core_type_class_type.typ_mapper`
/// (compiler/frontend/ast_core_type_class_type.ml:26-54, 94-134).
fn rewrite_object_fields(fields: &[ObjectField], arena: &mut ParseArena) -> Vec<ObjectField> {
    // `attr +> ty` then `self.typ self ty`.
    fn map_field_type(
        this_attr: Option<Attribute>,
        typ_idx: CoreTypeIdx,
        arena: &mut ParseArena,
    ) -> CoreTypeIdx {
        let mut ty = arena.get_core_type(typ_idx).clone();
        if let Some(attr) = this_attr {
            let mut attrs = vec![attr];
            attrs.extend(ty.ptyp_attributes.iter().cloned());
            ty.ptyp_attributes = attrs.into();
        }
        let rewritten = rewrite_core_type(&ty, arena);
        arena.push_core_type(rewritten)
    }

    let mut result: Vec<ObjectField> = Vec::new();
    for field in fields {
        match field {
            ObjectField::Oinherit(typ_idx) => {
                let typ_ct = arena.get_core_type(*typ_idx).clone();
                let rewritten = rewrite_core_type(&typ_ct, arena);
                result.push(ObjectField::Oinherit(arena.push_core_type(rewritten)));
            }
            ObjectField::Otag(name, attrs, typ_idx) => {
                // Field attributes (including @set, consumed during type
                // checking) stay on the field; only method-callback
                // attributes move onto the field's type.
                let (this_attr, attrs) = process_attributes_rev(attrs, arena);
                let typ = map_field_type(this_attr, *typ_idx, arena);
                result.push(ObjectField::Otag(*name, attrs.into(), typ));
            }
        }
    }
    result
}

/// Rewrite a core type, recursing into nested types and extension payloads.
/// This matches OCaml's default_mapper.typ behavior, ensuring that expressions
/// inside Ptyp_extension payloads get the "js" -> "*j" delimiter transformation.
fn rewrite_core_type_default(typ: &CoreType, arena: &mut ParseArena) -> CoreType {
    let new_desc = match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_extension(ext) => {
            let (name, payload) = &**ext;
            CoreTypeDesc::Ptyp_extension(Box::new((*name, rewrite_payload(payload, arena))))
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
                    fixed: source_arg.fixed,
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
            for t in arena.type_list(*types).to_vec().iter() {
                let ct = arena.get_core_type(*t).clone();
                let rw = rewrite_core_type(&ct, arena);
                rewritten_types.push(arena.push_core_type(rw));
            }
            CoreTypeDesc::Ptyp_tuple(arena.push_type_list(&rewritten_types))
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = *inner;
            let mut rewritten_args = Vec::with_capacity(args.len());
            for t in arena.type_list(*args).to_vec().iter() {
                let ct = arena.get_core_type(*t).clone();
                let rw = rewrite_core_type(&ct, arena);
                rewritten_args.push(arena.push_core_type(rw));
            }
            CoreTypeDesc::Ptyp_constr((*lid, arena.push_type_list(&rewritten_args)))
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
            let rewritten_fields = rewrite_object_fields(fields, arena);
            CoreTypeDesc::Ptyp_object(Box::new((rewritten_fields, *closed)))
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (ref rows, ref closed, ref labels) = **inner;
            let mut rewritten_rows = Vec::with_capacity(rows.len());
            for row in rows.iter() {
                let rewritten_row = match row {
                    RowField::Rtag(label, attrs, empty, types) => {
                        let mut rewritten_types = Vec::with_capacity(types.len());
                        for group in types.iter() {
                            let mut rewritten_group = Vec::with_capacity(group.txt.len());
                            for t in group.txt.iter() {
                                let ct = arena.get_core_type(*t).clone();
                                let rw = rewrite_core_type(&ct, arena);
                                rewritten_group.push(arena.push_core_type(rw));
                            }
                            rewritten_types.push(Located::new(rewritten_group, group.loc));
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
                rewritten_constraints.push((*loc, arena.push_core_type(rw)));
            }
            CoreTypeDesc::Ptyp_package(Box::new((*lid, rewritten_constraints)))
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
        ptyp_desc: new_desc,
        ptyp_loc: typ.ptyp_loc,
        ptyp_attributes: rewrite_attributes(&typ.ptyp_attributes, arena).into(),
    }
}

/// Rewrite core types with the same `@this` callback handling as OCaml's typ_mapper:
/// `@this` on an uncurried arrow wraps the type in
/// `Primitive_js_extern.Callback.arityN`.
fn rewrite_core_type(typ: &CoreType, arena: &mut ParseArena) -> CoreType {
    if let CoreTypeDesc::Ptyp_arrow(inner) = &typ.ptyp_desc {
        let (arg, _ret, arity) = &**inner;
        if has_this_attr(&typ.ptyp_attributes, arena) {
            // OCaml `ast_core_type_class_type.ml` typ_mapper passes
            // `~arity:(List.length params)`; arrows synthesized without a
            // recorded arity fall back to their n-ary parameter count.
            let arity_num = arena
                .get_arity(*arity)
                .unwrap_or_else(|| arena.nary_arrow_args(arg, *arity).len() as i32);
            let meth_type = rewrite_core_type_default(typ, arena);
            let callback = arena.ppx_js_oo_callback_lid();
            let callback_arity =
                arena.push_ldot_tracked(callback, format!("arity{arity_num}").as_str());
            return CoreType {
                ptyp_desc: CoreTypeDesc::Ptyp_constr((
                    Located {
                        txt: callback_arity,
                        loc: typ.ptyp_loc,
                    },
                    {
                        let items = [arena.push_core_type(meth_type)];
                        arena.push_type_list(&items)
                    },
                )),
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
        ptype_name: tdcl.ptype_name,
        ptype_params,
        ptype_cstrs: tdcl.ptype_cstrs.clone(),
        ptype_kind: rewrite_type_kind(&tdcl.ptype_kind, arena),
        ptype_private: tdcl.ptype_private,
        ptype_manifest,
        ptype_origin: tdcl.ptype_origin,
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
    // ast_mapper.ml: the runtime tag goes back into the attributes for the
    // mapper and `Type.constructor` takes it out again.
    let pcd_args = rewrite_constructor_arguments(&ctor.pcd_args, arena);
    let written = crate::ast_helper_type::constructor_attributes_owned(arena, ctor);
    let attrs = rewrite_attributes(&written, arena).into();
    crate::ast_helper_type::constructor(
        arena,
        ctor.pcd_loc,
        attrs,
        pcd_args,
        pcd_res,
        None,
        ctor.pcd_name,
    )
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
    // ast_mapper.ml: the runtime name goes back into the attributes so a
    // mapper sees `@as` where it was written; `Type.field` takes it out again.
    let written = crate::ast_helper_type::field_attributes_owned(arena, label);
    let mut pld_attributes = rewrite_attributes(&written, arena);
    if pld_attributes.len() == 1 && arena.get_string(pld_attributes[0].0.txt) == "internal" {
        let capitalized = capitalize_ascii(arena.get_string(pld_name.txt));
        pld_name.txt = arena.push_string(capitalized);
        pld_attributes.clear();
    }
    let pld_type = arena.push_core_type(rewritten_label_type);
    crate::ast_helper_type::field(
        arena,
        label.pld_loc,
        pld_attributes.into(),
        label.pld_mutable,
        label.pld_optional,
        None,
        pld_name,
        pld_type,
    )
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
/// ast_open_cxt.ml `whole`: a wrapper around a destructured tuple.
enum OpenCtx {
    LetOpen {
        flag: current::OverrideFlag,
        lid: Located<LidentIdx>,
        loc: LocIdx,
        attrs: Vec<Attribute>,
    },
    Braces {
        loc: LocIdx,
        braces_loc: LocIdx,
        attrs: Vec<Attribute>,
    },
}

/// Check if a pattern is "simple" enough for tuple flattening
fn is_simple_pattern(p: &Pattern, arena: &ParseArena) -> bool {
    match &p.ppat_desc {
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
    match &e.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => {
            acc.push(OpenCtx::Braces {
                loc: e.pexp_loc,
                braces_loc: braces.braces_loc,
                attrs: e.pexp_attributes.to_vec(),
            });
            destruct_open_tuple_inner(arena.get_expr(braces.expr), acc, arena)
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (ref flag, ref lid, ref cont) = **inner;
            acc.push(OpenCtx::LetOpen {
                flag: *flag,
                lid: *lid,
                loc: e.pexp_loc,
                attrs: e.pexp_attributes.to_vec(),
            });
            let cont_expr = arena.get_expr(*cont);
            destruct_open_tuple_inner(cont_expr, acc, arena)
        }
        ExpressionDesc::Pexp_tuple(es) => Some((
            acc,
            arena
                .expr_list(*es)
                .iter()
                .map(|e| arena.get_expr(*e).clone())
                .collect(),
        )),
        _ => None,
    }
}

/// ast_open_cxt.ml `restore_exp`: rebuild the wrappers around an expression.
/// `opens` is in source order (outermost first); OCaml's list holds the
/// innermost first and folds from it.
fn restore_exp(expr: Expression, opens: &[OpenCtx], arena: &mut ParseArena) -> Expression {
    opens.iter().rev().fold(expr, |inner, open| match open {
        OpenCtx::LetOpen {
            flag,
            lid,
            loc,
            attrs,
        } => Expression {
            pexp_desc: ExpressionDesc::Pexp_open(Box::new((*flag, *lid, arena.push_expr(inner)))),
            pexp_loc: *loc,
            pexp_attributes: attrs.clone().into(),
        },
        OpenCtx::Braces {
            loc,
            braces_loc,
            attrs,
        } => Expression {
            pexp_desc: ExpressionDesc::Pexp_braces(PexpBraces {
                expr: arena.push_expr(inner),
                braces_loc: *braces_loc,
            }),
            pexp_loc: *loc,
            pexp_attributes: attrs.clone().into(),
        },
    })
}

fn rewrite_value_binding_without_flattening(
    vb: &ValueBinding,
    arena: &mut ParseArena,
) -> ValueBinding {
    let vb_pat = arena.get_pat(vb.pvb_pat).clone();
    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
    let value_constraint = arena.value_constraint(vb.pvb_pat).cloned();
    let pvb_pat = rewrite_pattern(&vb_pat, arena);
    let pvb_expr = rewrite_expression(&vb_expr, arena);
    let pvb_attributes = rewrite_attributes(&vb.pvb_attributes, arena);
    let pvb_pat = arena.push_pat(pvb_pat);
    let pvb_expr = arena.push_expr(pvb_expr);
    if let Some(constraint) = value_constraint {
        let pvc_type = arena.get_core_type(constraint.pvc_type).clone();
        let pvc_type = rewrite_core_type(&pvc_type, arena);
        let constraint = crate::parser::ast::ValueConstraint {
            pvc_newtypes: constraint.pvc_newtypes,
            pvc_type: arena.push_core_type(pvc_type),
            pvc_pattern: None,
            pvc_expression: None,
        };
        arena.set_value_constraint(pvb_pat, constraint, pvb_expr, vb.pvb_loc);
    }
    ValueBinding {
        pvb_jsx_component: vb.pvb_jsx_component.clone(),
        pvb_pat,
        pvb_expr,
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
    if arena.value_constraint(vb.pvb_pat).is_some() {
        return vec![rewrite_value_binding_without_flattening(vb, arena)];
    }
    let vb_pat = arena.get_pat(vb.pvb_pat).clone();
    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
    let pvb_pat = rewrite_pattern(&vb_pat, arena);
    let pvb_expr = rewrite_expression(&vb_expr, arena);
    let pvb_attributes = rewrite_attributes(&vb.pvb_attributes, arena);

    if let PatternDesc::Ppat_tuple(ref pats) = pvb_pat.ppat_desc {
        if arena
            .pat_list(*pats)
            .iter()
            .all(|p| is_simple_pattern(arena.get_pat(*p), arena))
        {
            if let Some((opens, exprs)) = destruct_open_tuple(&pvb_expr, arena) {
                if exprs.len() == pats.len() {
                    return arena
                        .pat_list(*pats)
                        .to_vec()
                        .iter()
                        .zip(exprs.iter())
                        .map(|(pat, expr)| {
                            let restored = restore_exp(expr.clone(), &opens, arena);
                            let restored_idx = arena.push_expr(restored);
                            ValueBinding {
                                pvb_jsx_component: vb.pvb_jsx_component.clone(),
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
    if let (PatternDesc::Ppat_record(record_inner), ExpressionDesc::Pexp_pack(mod_expr_idx)) = (
        &pvb_pat.ppat_desc,
        &crate::ast_payload::unwrap_braces(arena, &pvb_expr).pexp_desc,
    ) {
        let (ref lid_pats, _, _) = **record_inner;
        let mod_expr = arena.get_mod_expr(*mod_expr_idx);
        let module_lid = if let ModuleExprDesc::Pmod_ident(lid) = &mod_expr.pmod_desc {
            *lid
        } else {
            return vec![ValueBinding {
                pvb_jsx_component: vb.pvb_jsx_component.clone(),
                pvb_pat: arena.push_pat(pvb_pat),
                pvb_expr: arena.push_expr(pvb_expr),
                pvb_attributes: pvb_attributes.into(),
                pvb_loc: vb.pvb_loc,
            }];
        };
        let module_longident = arena.get_longident(module_lid.txt).clone();
        let mut flattened = Vec::with_capacity(lid_pats.len());

        for field in arena.pat_field_list(*lid_pats).to_vec() {
            let field_name = match arena.get_longident(field.lid.txt) {
                Longident::Lident(name) => *name,
                _ => {
                    return vec![ValueBinding {
                        pvb_jsx_component: vb.pvb_jsx_component.clone(),
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
                pexp_desc: ExpressionDesc::Pexp_ident(Located {
                    txt: projected_lid,
                    loc: projected_loc,
                }),
                pexp_loc: projected_loc,
                pexp_attributes: Attributes::new(),
            };
            let pat_loc = arena.get_pat(field.pat).ppat_loc;
            flattened.push(ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: field.pat,
                pvb_expr: arena.push_expr(pvb_expr),
                pvb_attributes: Attributes::new(),
                pvb_loc: pat_loc,
            });
        }

        return flattened;
    }

    vec![ValueBinding {
        pvb_jsx_component: vb.pvb_jsx_component.clone(),
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

    let desc = match &pat.ppat_desc {
        PatternDesc::Ppat_constant(c) => match c {
            // Strip 'l' suffix from integer literals
            Constant::Integer(s, Some('l')) => {
                PatternDesc::Ppat_constant(Constant::Integer(*s, None))
            }
            // Other constants: no transformation needed
            _ => PatternDesc::Ppat_constant(*c),
        },

        // Alias pattern: recurse into the aliased pattern
        PatternDesc::Ppat_alias(inner_idx, name) => {
            let inner_pat = arena.get_pat(*inner_idx).clone();
            let rw = rewrite_pattern(&inner_pat, arena);
            PatternDesc::Ppat_alias(arena.push_pat(rw), *name)
        }

        // Tuple pattern: recurse into all elements
        PatternDesc::Ppat_tuple(pats) => {
            let rewritten_pats = arena
                .pat_list(*pats)
                .to_vec()
                .iter()
                .map(|p| {
                    let pat = arena.get_pat(*p).clone();
                    let rw = rewrite_pattern(&pat, arena);
                    arena.push_pat(rw)
                })
                .collect::<Vec<_>>();
            PatternDesc::Ppat_tuple(arena.push_pat_list(&rewritten_pats))
        }

        // Constructor pattern: recurse into optional payload
        PatternDesc::Ppat_construct(lid, args) => {
            let args = *args;
            for p in arena.pat_list(args.txt).to_vec().iter_mut() {
                let pat = arena.get_pat(*p).clone();
                let rw = rewrite_pattern(&pat, arena);
                *p = arena.push_pat(rw);
            }
            PatternDesc::Ppat_construct(*lid, args)
        }

        // Variant pattern: recurse into optional payload
        PatternDesc::Ppat_variant(inner) => {
            let (ref label, ref args) = **inner;
            let mut args = *args;
            // The rewritten node gets its own list; the original keeps its own.
            let mut new_items = arena.pat_list(args.txt).to_vec();
            for p in new_items.iter_mut() {
                let pat = arena.get_pat(*p).clone();
                let rw = rewrite_pattern(&pat, arena);
                *p = arena.push_pat(rw);
            }
            args.txt = arena.push_pat_list(&new_items);
            PatternDesc::Ppat_variant(Box::new((label.clone(), args)))
        }

        // Record pattern: recurse into all field patterns
        PatternDesc::Ppat_record(inner) => {
            let (ref fields, ref flag, ref record_rest) = **inner;
            let record_rest = record_rest.as_ref().map(|rest| {
                let rest_type = rest.rest_type.map(|typ| {
                    let typ = arena.get_core_type(typ).clone();
                    let typ = rewrite_core_type(&typ, arena);
                    arena.push_core_type(typ)
                });
                crate::parser::ast::RecordPatRest {
                    rest_type,
                    ..rest.clone()
                }
            });
            PatternDesc::Ppat_record(Box::new((
                {
                    let items = arena
                        .pat_field_list(*fields)
                        .to_vec()
                        .iter()
                        .map(|f| {
                            let pat = arena.get_pat(f.pat).clone();
                            let rw_pat = rewrite_pattern(&pat, arena);
                            PatternRecordField {
                                lid: f.lid,
                                pat: arena.push_pat(rw_pat),
                                opt: f.opt,
                            }
                        })
                        .collect::<Vec<_>>();
                    arena.push_pat_field_list(&items)
                },
                *flag,
                record_rest,
            )))
        }

        // Array pattern: recurse into all elements
        PatternDesc::Ppat_array(pats) => {
            let rewritten_pats = arena
                .pat_list(*pats)
                .to_vec()
                .iter()
                .map(|p| {
                    let pat = arena.get_pat(*p).clone();
                    let rw = rewrite_pattern(&pat, arena);
                    arena.push_pat(rw)
                })
                .collect::<Vec<_>>();
            PatternDesc::Ppat_array(arena.push_pat_list(&rewritten_pats))
        }

        PatternDesc::Ppat_dict(entries) => {
            let entries = entries
                .iter()
                .map(|entry| {
                    let pat = arena.get_pat(entry.pdp_pattern).clone();
                    let rw = rewrite_pattern(&pat, arena);
                    DictPatternEntry {
                        pdp_pattern: arena.push_pat(rw),
                        ..entry.clone()
                    }
                })
                .collect();
            PatternDesc::Ppat_dict(Box::new(entries))
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

        // Patterns without nested patterns: clone as-is
        PatternDesc::Ppat_any => PatternDesc::Ppat_any,
        PatternDesc::Ppat_var(name) => PatternDesc::Ppat_var(*name),
        PatternDesc::Ppat_interval(inner) => PatternDesc::Ppat_interval(inner.clone()),
        PatternDesc::Ppat_type(lid) => PatternDesc::Ppat_type(*lid),
        PatternDesc::Ppat_variant_spread(lid) => PatternDesc::Ppat_variant_spread(*lid),
        PatternDesc::Ppat_unpack(name) => PatternDesc::Ppat_unpack(*name),
        PatternDesc::Ppat_extension(ext) => {
            let (ref name, ref payload) = **ext;
            PatternDesc::Ppat_extension(Box::new((*name, rewrite_payload(payload, arena))))
        }
    };

    Pattern {
        ppat_desc: desc,
        ppat_loc: pat.ppat_loc,
        ppat_attributes: attrs.into(),
    }
}

/// OCaml async rewriting uses the mapped lhs pattern location, and for
/// `Ppat_var` that location is pointer-identical to `name.loc`. Keep the same
/// identity when arena indices differ but location contents are equal.
fn async_lhs_loc(lhs: &Pattern, _arena: &ParseArena) -> LocIdx {
    if let PatternDesc::Ppat_var(name) = &lhs.ppat_desc {
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
    fun: &PexpFun,
    is_async: bool,
    filtered_attrs: Vec<Attribute>,
    arena: &mut ParseArena,
) -> Expression {
    let loc = expr.pexp_loc;
    let source_params = arena.nary_fun_params(fun).into_owned();
    let source_newtypes = arena.nary_fun_newtypes(fun).to_vec();
    let body = arena.nary_fun_body(fun);

    let mut rewritten_params = Vec::with_capacity(source_params.len());
    for source in source_params {
        let source_pattern = arena.get_pat(source.p_pat).clone();
        let rewritten_pattern = rewrite_pattern(&source_pattern, arena);
        let rewritten_default = source.p_default.map(|default| {
            let default = arena.get_expr(default).clone();
            let default = rewrite_expression(&default, arena);
            arena.push_expr(default)
        });
        rewritten_params.push(FunParam {
            p_attrs: rewrite_attributes(&source.p_attrs, arena).into(),
            p_lbl: source.p_lbl,
            p_default: rewritten_default,
            p_pat: arena.push_pat(rewritten_pattern),
        });
    }

    let result = arena.get_expr(body).clone();
    let result = rewrite_expression(&result, arena);
    let result = arena.push_expr(result);
    let total_arity = rewritten_params.len() as i32;
    let arity = arena.push_arity(Some(total_arity));
    let unknown_arity = arena.nary_fun_unknown_arity(fun);
    let first = rewritten_params[0].clone();
    arena.set_nary_fun_params(arity, rewritten_params, unknown_arity);
    if !source_newtypes.is_empty() {
        let newtypes = source_newtypes
            .into_iter()
            .map(|(name, attrs)| (name, rewrite_attributes(&attrs, arena).into()))
            .collect();
        arena.set_nary_fun_newtypes(first.p_pat, newtypes);
    }

    let mut method_body = Expression {
        pexp_desc: ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: first.p_lbl,
            default: first.p_default,
            lhs: first.p_pat,
            rhs: result,
            arity,
            is_async,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    if is_async {
        let async_loc = match &method_body.pexp_desc {
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
        pexp_desc: ExpressionDesc::Pexp_record((
            {
                let items = [ExpressionRecordField {
                    lid: Located {
                        txt: hidden_field,
                        loc,
                    },
                    expr: arena.push_expr(method_body),
                    opt: false,
                }];
                arena.push_expr_field_list(&items)
            },
            None,
        )),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    let callback_any_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr((
            Located {
                txt: callback_arity,
                loc,
            },
            {
                let items = [arena.push_core_type(CoreType {
                    ptyp_desc: CoreTypeDesc::Ptyp_any,
                    ptyp_loc: loc,
                    ptyp_attributes: Attributes::new(),
                })];
                arena.push_type_list(&items)
            },
        )),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    };

    let constrained_method = Expression {
        pexp_desc: ExpressionDesc::Pexp_constraint(Box::new((
            arena.push_expr(method_record),
            arena.push_core_type(callback_any_type),
        ))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
            funct: arena.push_expr(Expression {
                pexp_desc: ExpressionDesc::Pexp_ident(Located {
                    txt: unsafe_to_method,
                    loc,
                }),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }),
            args: {
                let items = [(ArgLabel::Nolabel, arena.push_expr(constrained_method))];
                arena.push_apply_args(&items)
            },
            partial: false,
            transformed_jsx: false,
        }),
        pexp_loc: loc,
        pexp_attributes: filtered_attrs.into(),
    }
}

/// Rewrite an expression, desugaring pipe operators
/// A child expression after the mapper: itself when the mapper leaves it as
/// it is, so the caller keeps its arena node instead of pushing a copy.
enum Rewritten {
    Same(ExprIdx),
    New(Expression),
}

/// Keep certified rewrite-free subtrees by index. Their descendants have no
/// attributes, so they do not need the marshal attribute-sharing marker.
/// Diagnostics still traverse the original tree in `check::Checker`.
fn rewrite_child(idx: ExprIdx, arena: &mut ParseArena) -> Rewritten {
    if arena.expr_needs_no_rewrite(idx) {
        let loc = arena.get_expr(idx).pexp_loc;
        arena.mark_rewritten_expr_loc(loc);
        return Rewritten::Same(idx);
    }
    let expr = arena.get_expr(idx);
    let expr = expr.clone();
    Rewritten::New(rewrite_expression(&expr, arena))
}

/// The arena index of a [`rewrite_child`] result.
fn push_rewritten(arena: &mut ParseArena, rewritten: Rewritten) -> ExprIdx {
    match rewritten {
        Rewritten::Same(idx) => idx,
        Rewritten::New(expr) => arena.push_expr(expr),
    }
}

fn rewrite_expression(expr: &Expression, arena: &mut ParseArena) -> Expression {
    // Handle integer literal suffix stripping ('l' suffix)
    // OCaml: {e with pexp_desc = Pexp_constant (Pconst_integer (s, None))}
    // This is an early-return case that preserves attributes without remapping.
    if let ExpressionDesc::Pexp_constant(Constant::Integer(s, Some('l'))) = &expr.pexp_desc {
        return Expression {
            pexp_desc: ExpressionDesc::Pexp_constant(Constant::Integer(*s, None)),
            pexp_loc: expr.pexp_loc,
            pexp_attributes: expr.pexp_attributes.clone(),
        };
    }

    // First check if this is a pipe or #= application
    if let ExpressionDesc::Pexp_apply(inner) = &expr.pexp_desc {
        let PexpApply { ref funct, .. } = *inner;
        let args = arena.apply_args(inner.args);
        // Check if this is a binary op: -> or #= with two args
        if args.len() == 2
            && matches!(&args[0].0, ArgLabel::Nolabel)
            && matches!(&args[1].0, ArgLabel::Nolabel)
        {
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(lid) = &funct_expr.pexp_desc {
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
                }
            }
        }
    }

    // Not a pipe - recursively rewrite sub-expressions
    rewrite_expression_generic(expr, arena)
}

/// Check if an expression doesn't need to be bound in a let-binding
/// (i.e., it's a simple identifier or a constraint on a simple identifier).
/// Matches OCaml's `no_need_bound` in ast_exp_apply.ml.
fn no_need_bound(exp: &Expression, arena: &ParseArena) -> bool {
    match &exp.pexp_desc {
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

/// ast_exp_apply.ml `fresh_bound_name`: `__tuple_internal_obj`, or the
/// first numbered variant of it, that no identifier or variable pattern in
/// `avoid` uses.
fn fresh_bound_name(avoid: &Expression, arena: &mut ParseArena) -> String {
    struct Names {
        names: std::collections::HashSet<String>,
    }
    impl crate::binary_ast::ast_iter::AstIter for Names {
        fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
            if let ExpressionDesc::Pexp_ident(lid) = &arena.get_expr(idx).pexp_desc
                && let Longident::Lident(name) = arena.get_longident(lid.txt)
            {
                self.names.insert(arena.get_string(*name).to_string());
            }
            crate::binary_ast::ast_iter::walk_expr(self, arena, idx);
        }
        fn pat(&mut self, arena: &ParseArena, idx: PatIdx) {
            match &arena.get_pat(idx).ppat_desc {
                PatternDesc::Ppat_var(name) | PatternDesc::Ppat_alias(_, name) => {
                    self.names.insert(arena.get_string(name.txt).to_string());
                }
                _ => {}
            }
            crate::binary_ast::ast_iter::walk_pat(self, arena, idx);
        }
    }
    let avoid_idx = arena.push_expr(avoid.clone());
    let mut names = Names {
        names: std::collections::HashSet::new(),
    };
    crate::binary_ast::ast_iter::AstIter::expr(&mut names, arena, avoid_idx);
    let mut suffix = 0;
    loop {
        let name = if suffix == 0 {
            "__tuple_internal_obj".to_string()
        } else {
            format!("__tuple_internal_obj{suffix}")
        };
        if !names.names.contains(&name) {
            return name;
        }
        suffix += 1;
    }
}

/// ast_exp_apply.ml `bound ~force ~avoid e cb`: pass `e` to `cb`, binding it
/// to a fresh name first unless it is a plain identifier and `force` is off.
fn pipe_bound(
    force: bool,
    avoid: &Expression,
    e: Expression,
    arena: &mut ParseArena,
    cb: impl FnOnce(Expression, &mut ParseArena) -> Expression,
) -> Expression {
    if !force && no_need_bound(&e, arena) {
        return cb(e, arena);
    }
    let loc = e.pexp_loc;
    let name = fresh_bound_name(avoid, arena);
    let name_idx = arena.intern(&name);
    let lid = arena.push_lident_from_idx(name_idx);
    let ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: lid, loc }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };
    let pat = arena.push_pat(Pattern {
        ppat_desc: PatternDesc::Ppat_var(Located { txt: name_idx, loc }),
        ppat_loc: loc,
        ppat_attributes: Attributes::new(),
    });
    let e_idx = arena.push_expr(e);
    let body = cb(ident, arena);
    let body_idx = arena.push_expr(body);
    Expression {
        pexp_desc: ExpressionDesc::Pexp_let((
            RecFlag::Nonrecursive,
            arena.push_vb_list(&[ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: pat,
                pvb_expr: e_idx,
                pvb_attributes: Attributes::new(),
                pvb_loc: loc,
            }]),
            body_idx,
        )),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Map each tuple element to apply the piped argument.
/// For each element fn in the tuple:
/// - Pexp_construct(ctor, None) -> Pexp_construct(ctor, Some(a))
/// - Pexp_apply(fn1, args) -> Pexp_apply(fn1, (Nolabel, a) :: args)
/// - otherwise -> fn(a) = Pexp_apply(fn, [(Nolabel, a)])
///
/// Matches the `Pexp_tuple` arm of ast_exp_apply.ml `rewrite_pipe_rhs`.
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
            let result = match &fn_expr.pexp_desc {
                ExpressionDesc::Pexp_construct(ctor, args) if args.txt.is_empty() => {
                    let a_loc = a.pexp_loc;
                    let a_idx = arena.push_expr(a.clone());
                    Expression {
                        pexp_desc: ExpressionDesc::Pexp_construct(
                            *ctor,
                            arena.expr_ctor_args(&[a_idx], a_loc),
                        ),
                        pexp_loc: fn_expr.pexp_loc,
                        pexp_attributes: fn_expr.pexp_attributes.clone(),
                    }
                }
                ExpressionDesc::Pexp_apply(inner) => {
                    let PexpApply {
                        ref funct,

                        transformed_jsx,
                        ..
                    } = *inner;
                    let mut new_args = Vec::with_capacity(inner.args.len() + 1);
                    let a_idx = arena.push_expr(a.clone());
                    new_args.push((ArgLabel::Nolabel, a_idx));
                    new_args.extend_from_slice(arena.apply_args(inner.args));
                    let funct_loc = arena.get_expr(*funct).pexp_loc;
                    Expression {
                        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
                            funct: *funct,
                            args: arena.push_apply_args(&new_args),
                            partial: false,
                            transformed_jsx,
                        }),
                        pexp_loc: funct_loc,
                        pexp_attributes: Attributes::new(),
                    }
                }
                _ => {
                    let fn_expr_idx_for_funct = arena.push_expr(fn_expr.clone());
                    let a_idx = arena.push_expr(a.clone());
                    Expression {
                        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
                            funct: fn_expr_idx_for_funct,
                            args: arena.push_apply_args(&[(ArgLabel::Nolabel, a_idx)]),
                            partial: false,
                            transformed_jsx: false,
                        }),
                        pexp_loc: fn_expr.pexp_loc,
                        pexp_attributes: Attributes::new(),
                    }
                }
            };
            arena.push_expr(result)
        })
        .collect();

    Expression {
        pexp_desc: ExpressionDesc::Pexp_tuple(arena.push_expr_list(&mapped)),
        pexp_attributes: f.pexp_attributes.clone(),
        pexp_loc: f.pexp_loc,
    }
}

/// Desugar pipe expression `a -> f` (ast_exp_apply.ml `app_exp_mapper`).
/// A braced pipeline right-hand side may contain local bindings or opens
/// before its final call: the left-hand expression is bound before entering
/// that context.
fn desugar_pipe(
    original: &Expression,
    a: Expression,
    f: Expression,
    arena: &mut ParseArena,
) -> Expression {
    let loc = original.pexp_loc;
    let attrs = original.pexp_attributes.clone();
    match &f.pexp_desc {
        ExpressionDesc::Pexp_braces(_)
        | ExpressionDesc::Pexp_open(_)
        | ExpressionDesc::Pexp_let(_)
        | ExpressionDesc::Pexp_sequence(_, _) => pipe_bound(true, &f, a, arena, |a, arena| {
            rewrite_pipe_rhs(loc, &attrs, a, f.clone(), arena)
        }),
        _ => rewrite_pipe_rhs(loc, &attrs, a, f, arena),
    }
}

/// ast_exp_apply.ml `rewrite_pipe_rhs`.
fn rewrite_pipe_rhs(
    loc: LocIdx,
    attrs: &Attributes,
    a: Expression,
    f: Expression,
    arena: &mut ParseArena,
) -> Expression {
    // `{f with pexp_desc = ...}` around a rewritten inner expression.
    let rewrap = |f: &Expression, desc: ExpressionDesc| Expression {
        pexp_desc: desc,
        pexp_loc: f.pexp_loc,
        pexp_attributes: f.pexp_attributes.clone(),
    };
    match &f.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => {
            let inner = arena.get_expr(braces.expr).clone();
            let rewritten = rewrite_pipe_rhs(loc, attrs, a, inner, arena);
            let expr = arena.push_expr(rewritten);
            rewrap(
                &f,
                ExpressionDesc::Pexp_braces(PexpBraces {
                    expr,
                    braces_loc: braces.braces_loc,
                }),
            )
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (flag, lid, body) = (inner.0, inner.1, inner.2);
            let body = arena.get_expr(body).clone();
            let rewritten = rewrite_pipe_rhs(loc, attrs, a, body, arena);
            let body = arena.push_expr(rewritten);
            rewrap(&f, ExpressionDesc::Pexp_open(Box::new((flag, lid, body))))
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (flag, bindings, body) = (inner.0, inner.1, inner.2);
            let body = arena.get_expr(body).clone();
            let rewritten = rewrite_pipe_rhs(loc, attrs, a, body, arena);
            let body = arena.push_expr(rewritten);
            rewrap(&f, ExpressionDesc::Pexp_let((flag, bindings, body)))
        }
        ExpressionDesc::Pexp_sequence(first, second) => {
            let first = *first;
            let second = arena.get_expr(*second).clone();
            let rewritten = rewrite_pipe_rhs(loc, attrs, a, second, arena);
            let second = arena.push_expr(rewritten);
            rewrap(&f, ExpressionDesc::Pexp_sequence(first, second))
        }
        // a -> #Variant becomes #Variant(a), keeping `f`'s attributes.
        ExpressionDesc::Pexp_variant(inner) if inner.1.txt.is_empty() => {
            let label = inner.0.clone();
            let a_loc = a.pexp_loc;
            Expression {
                pexp_desc: ExpressionDesc::Pexp_variant(Box::new((label, {
                    let a = arena.push_expr(a);
                    arena.expr_ctor_args(&[a], a_loc)
                }))),
                pexp_loc: loc,
                pexp_attributes: f.pexp_attributes.clone(),
            }
        }
        // a -> Constructor becomes Constructor(a)
        ExpressionDesc::Pexp_construct(ctor, args) if args.txt.is_empty() => Expression {
            pexp_desc: ExpressionDesc::Pexp_construct(*ctor, {
                let a_loc = a.pexp_loc;
                let a = arena.push_expr(a);
                arena.expr_ctor_args(&[a], a_loc)
            }),
            pexp_loc: loc,
            pexp_attributes: f.pexp_attributes.clone(),
        },
        // a -> f(b, c) becomes f(a, b, c)
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref partial,
                ref transformed_jsx,
                ..
            } = *inner;
            let mut new_args = Vec::with_capacity(inner.args.len() + 1);
            new_args.push((ArgLabel::Nolabel, arena.push_expr(a)));
            new_args.extend_from_slice(arena.apply_args(inner.args));
            Expression {
                pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
                    funct: *funct,
                    args: arena.push_apply_args(&new_args),
                    partial: *partial,
                    transformed_jsx: *transformed_jsx,
                }),
                pexp_loc: loc,
                pexp_attributes: {
                    let mut all = attrs.clone();
                    all.extend(f.pexp_attributes.iter().cloned());
                    all
                },
            }
        }
        // a -> (x, y) distributes the pipe: becomes (x(a), y(a)), binding a
        // non-identifier `a` first.
        ExpressionDesc::Pexp_tuple(xs) => {
            let xs = arena.expr_list(*xs).to_vec();
            pipe_bound(false, &f, a, arena, |a, arena| {
                pipe_tuple_map(a, &xs, &f, arena)
            })
        }
        // Default: a -> f becomes f(a)
        _ => Expression {
            pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
                funct: arena.push_expr(f),
                args: {
                    let items = [(ArgLabel::Nolabel, arena.push_expr(a))];
                    arena.push_apply_args(&items)
                },
                partial: false,
                transformed_jsx: false,
            }),
            pexp_loc: loc,
            pexp_attributes: attrs.clone(),
        },
    }
}

/// bs_builtin_ppx.ml `add_this_to_braced_function`: prepend `attrs` to the
/// function under (possibly nested) braces, rebuilding the braces chain.
fn add_this_to_braced_function(
    attrs: &[Attribute],
    idx: ExprIdx,
    arena: &mut ParseArena,
) -> Option<ExprIdx> {
    let e = arena.get_expr(idx).clone();
    match &e.pexp_desc {
        ExpressionDesc::Pexp_fun(_) => {
            let mut all = attrs.to_vec();
            all.extend(e.pexp_attributes.iter().cloned());
            Some(arena.push_expr(Expression {
                pexp_desc: e.pexp_desc.clone(),
                pexp_loc: e.pexp_loc,
                pexp_attributes: Attributes::from_vec(all),
            }))
        }
        ExpressionDesc::Pexp_braces(braces) => {
            let inner = add_this_to_braced_function(attrs, braces.expr, arena)?;
            Some(arena.push_expr(Expression {
                pexp_desc: ExpressionDesc::Pexp_braces(PexpBraces {
                    expr: inner,
                    braces_loc: braces.braces_loc,
                }),
                pexp_loc: e.pexp_loc,
                pexp_attributes: e.pexp_attributes.clone(),
            }))
        }
        _ => None,
    }
}

/// Generic expression rewriting - recurses into sub-expressions
fn rewrite_expression_generic(expr: &Expression, arena: &mut ParseArena) -> Expression {
    arena.mark_rewritten_expr_loc(expr.pexp_loc);

    let new_desc = match &expr.pexp_desc {
        // bs_builtin_ppx.ml `Pexp_regexp`: `(%raw("/pattern/flags") : RegExp.t)`.
        // Its output is not rewritten anymore; the literal is validated by
        // the warning pre-pass.
        ExpressionDesc::Pexp_regexp(regexp) => {
            let loc = expr.pexp_loc;
            let source = format!("/{}/{}", regexp.pattern, regexp.flags);
            let arg = Expression {
                pexp_desc: ExpressionDesc::Pexp_constant(arena.string_constant(&source)),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            };
            let prim = arena.prim_raw_expr();
            let raw_desc = raw_local_external_apply(arena, loc, prim, arg);
            let raw = Expression {
                pexp_desc: raw_desc,
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            };
            let regexp_t = arena.regexp_t_lident();
            let regexp_type = CoreType {
                ptyp_desc: CoreTypeDesc::Ptyp_constr((
                    Located { txt: regexp_t, loc },
                    crate::parse_arena::ArenaList::EMPTY,
                )),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            };
            let typ = arena.push_core_type(regexp_type);
            let raw = arena.push_expr(raw);
            return Expression {
                pexp_desc: ExpressionDesc::Pexp_constraint(Box::new((raw, typ))),
                pexp_loc: loc,
                pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena).into(),
            };
        }

        // bs_builtin_ppx.ml `Pexp_braces`: the method callback rewrite runs on
        // `Pexp_fun`, so forward `@this` through braces before mapping the
        // function, keeping unrelated attributes on the braces.
        ExpressionDesc::Pexp_braces(braces) => {
            let (this_attrs, other_attrs): (Vec<Attribute>, Vec<Attribute>) = expr
                .pexp_attributes
                .iter()
                .cloned()
                .partition(|(name, _)| arena.get_string(name.txt) == "this");
            let forwarded = if this_attrs.is_empty() {
                None
            } else {
                add_this_to_braced_function(&this_attrs, braces.expr, arena)
            };
            let (inner_idx, attrs) = match forwarded {
                Some(inner) => (inner, Attributes::from_vec(other_attrs)),
                None => (braces.expr, expr.pexp_attributes.clone()),
            };
            let inner = arena.get_expr(inner_idx).clone();
            let rw = rewrite_expression(&inner, arena);
            // Ast_mapper rebuilds braces with `Exp.braces`, whose location is
            // the mapped inner expression's (ast_helper.ml:166-167): a
            // rewritten `{await e}` takes the ghost location of the await.
            let pexp_loc = rw.pexp_loc;
            return Expression {
                pexp_desc: ExpressionDesc::Pexp_braces(PexpBraces {
                    expr: arena.push_expr(rw),
                    braces_loc: braces.braces_loc,
                }),
                pexp_loc,
                pexp_attributes: rewrite_attributes(&attrs, arena).into(),
            };
        }

        ExpressionDesc::Pexp_ternary(inner) => {
            let (cond, consequent, alternate) = **inner;
            let rw_cond = rewrite_child(cond, arena);
            let rw_consequent = rewrite_child(consequent, arena);
            let rw_alternate = rewrite_child(alternate, arena);
            ExpressionDesc::Pexp_ternary(Box::new((
                push_rewritten(arena, rw_cond),
                push_rewritten(arena, rw_consequent),
                push_rewritten(arena, rw_alternate),
            )))
        }
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
            let (ref rec_flag, ref bindings, ref body) = *inner;
            // Check for record pattern destructuring: convert to match expression
            // OCaml's bs_builtin_ppx.ml (lines 295-319) converts:
            //   let {field1, field2} = expr in body
            // to:
            //   match expr with {field1, field2} -> body
            if *rec_flag == RecFlag::Nonrecursive && bindings.len() == 1 {
                let vb = &arena.vb_list(*bindings).to_vec()[0];
                if has_unwrap_attr(&vb.pvb_attributes, arena) {
                    // OCaml bs_builtin_ppx: rewrite supported let? forms into a match with
                    // an early-return case and a continuation case.
                    if !matches!(
                        &crate::parser::parsetree_viewer::unwrap_braces(
                            arena,
                            arena.get_expr(vb.pvb_expr)
                        )
                        .pexp_desc,
                        ExpressionDesc::Pexp_pack(_)
                    ) {
                        let vb_pat = arena.get_pat(vb.pvb_pat);
                        if let Some((variant, var_name_idx)) =
                            classify_let_unwrap_pattern(vb_pat, arena)
                        {
                            let loc = arena.mk_ghost_loc(vb_pat.ppat_loc);

                            let (early_ctor_name, early_ctor_payload) = match variant {
                                LetUnwrapVariant::ResultOk => ("Error", true),
                                LetUnwrapVariant::ResultError => ("Ok", true),
                                LetUnwrapVariant::OptionSome => ("None", false),
                                LetUnwrapVariant::OptionNone => ("Some", true),
                            };
                            let early_ctor_idx = arena.intern(early_ctor_name);
                            // This constructor comes from a static literal in
                            // bs_builtin_ppx.ml, so OCaml reuses its Longident
                            // wrapper each time this rewrite branch runs.
                            let early_ctor_lid = arena.push_lident_from_idx(early_ctor_idx);
                            let early_ctor_payload_pat = if early_ctor_payload {
                                vec![arena.push_pat(Pattern {
                                    ppat_desc: PatternDesc::Ppat_any,
                                    ppat_loc: loc,
                                    ppat_attributes: Attributes::new(),
                                })]
                            } else {
                                Vec::new()
                            };
                            let early_ctor_pat = Pattern {
                                ppat_desc: PatternDesc::Ppat_construct(
                                    Located {
                                        txt: early_ctor_lid,
                                        loc,
                                    },
                                    arena.pat_ctor_args(&early_ctor_payload_pat, loc),
                                ),
                                ppat_loc: loc,
                                ppat_attributes: Attributes::new(),
                            };
                            let early_ctor_pat_idx = arena.push_pat(early_ctor_pat);
                            let early_rhs_lid = arena.fresh_lident_from_idx(var_name_idx);
                            let early_case = Case {
                                pc_bar: None,
                                pc_lhs: arena.push_pat(Pattern {
                                    ppat_desc: PatternDesc::Ppat_alias(
                                        early_ctor_pat_idx,
                                        Located {
                                            txt: var_name_idx,
                                            loc,
                                        },
                                    ),
                                    ppat_loc: arena.none_loc(),
                                    ppat_attributes: Attributes::new(),
                                }),
                                pc_guard: None,
                                pc_rhs: arena.push_expr(Expression {
                                    pexp_desc: ExpressionDesc::Pexp_ident(Located {
                                        txt: early_rhs_lid,
                                        loc,
                                    }),
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
                                pexp_desc: ExpressionDesc::Pexp_match((
                                    vb.pvb_expr,
                                    arena.push_case_list(&[early_case, cont_case]),
                                )),
                                pexp_loc: expr.pexp_loc,
                                pexp_attributes: attrs,
                            };
                            return rewrite_expression_generic(&rewritten, arena);
                        }
                    }
                }
                let is_record_pat = match &arena.get_pat(vb.pvb_pat).ppat_desc {
                    PatternDesc::Ppat_record(..) | PatternDesc::Ppat_dict(_) => true,
                    PatternDesc::Ppat_alias(inner, _) => {
                        matches!(
                            &arena.get_pat(*inner).ppat_desc,
                            PatternDesc::Ppat_record(..) | PatternDesc::Ppat_dict(_)
                        )
                    }
                    _ => false,
                };
                // Don't convert if the expression is Pexp_pack (module unpacking)
                let is_pack = matches!(
                    &crate::parser::parsetree_viewer::unwrap_braces(
                        arena,
                        arena.get_expr(vb.pvb_expr)
                    )
                    .pexp_desc,
                    ExpressionDesc::Pexp_pack(_)
                );
                if is_record_pat && !is_pack {
                    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
                    let vb_pat = arena.get_pat(vb.pvb_pat).clone();
                    let rewritten_expr = rewrite_expression(&vb_expr, arena);
                    let rewritten_pat = rewrite_pattern(&vb_pat, arena);
                    let rewritten_body = rewrite_child(*body, arena);
                    // Merge attributes: expression attrs + binding attrs
                    let mut attrs = expr.pexp_attributes.clone();
                    attrs.extend(vb.pvb_attributes.iter().cloned());
                    let attrs = rewrite_attributes(&attrs, arena);
                    let scrutinee = arena.push_expr(rewritten_expr);
                    let case = Case {
                        pc_bar: None,
                        pc_lhs: arena.push_pat(rewritten_pat),
                        pc_guard: None,
                        pc_rhs: push_rewritten(arena, rewritten_body),
                    };
                    return Expression {
                        pexp_desc: ExpressionDesc::Pexp_match((
                            scrutinee,
                            arena.push_case_list(&[case]),
                        )),
                        pexp_loc: expr.pexp_loc,
                        pexp_attributes: attrs.into(),
                    };
                }
            }

            let old_bindings = arena.vb_list(*bindings).to_vec();
            let new_bindings = if *rec_flag == RecFlag::Recursive {
                rewrite_value_bindings_without_flattening(&old_bindings, arena)
            } else {
                flatten_value_bindings(&old_bindings, arena)
            };
            let rw_body = rewrite_child(*body, arena);
            ExpressionDesc::Pexp_let((
                *rec_flag,
                arena.push_vb_list(&new_bindings),
                push_rewritten(arena, rw_body),
            ))
        }

        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun {
                ref arity,
                ref is_async,
                ..
            } = **inner;
            let (has_this_attr, filtered_attrs) = split_this_attrs(&expr.pexp_attributes, arena);
            if has_this_attr {
                return rewrite_method_callback_expression(
                    expr,
                    inner,
                    *is_async,
                    filtered_attrs,
                    arena,
                );
            }
            // First, recursively rewrite the complete n-ary function shape.
            let source_params = arena.nary_fun_params(inner).into_owned();
            let source_newtypes = arena.nary_fun_newtypes(inner).to_vec();
            let mut rewritten_params = Vec::with_capacity(source_params.len());
            for source in source_params {
                let rewritten_default = source.p_default.map(|e| {
                    let rw = rewrite_child(e, arena);
                    push_rewritten(arena, rw)
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
            let rw_rhs = rewrite_child(body, arena);
            let rewritten_rhs = push_rewritten(arena, rw_rhs);
            let first = rewritten_params[0].clone();
            let unknown_arity = arena.nary_fun_unknown_arity(inner);
            arena.set_nary_fun_params(*arity, rewritten_params, unknown_arity);
            if !source_newtypes.is_empty() {
                let rewritten_newtypes = source_newtypes
                    .into_iter()
                    .map(|(name, attrs)| (name, rewrite_attributes(&attrs, arena).into()))
                    .collect();
                arena.set_nary_fun_newtypes(first.p_pat, rewritten_newtypes);
            }

            // Create the rewritten fun expression
            let mut rewritten_fun = Expression {
                pexp_desc: ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: first.p_lbl,
                    default: first.p_default,
                    lhs: first.p_pat,
                    rhs: rewritten_rhs,
                    arity: *arity,
                    is_async: *is_async,
                })),
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
                ref partial,
                ref transformed_jsx,
                ..
            } = *inner;
            let rw_funct = rewrite_child(*funct, arena);
            let funct = push_rewritten(arena, rw_funct);
            // Index the arena's argument list: rewriting pushes new nodes but
            // never changes an existing list.
            let mut args: smallvec::SmallVec<[_; 8]> = smallvec::SmallVec::new();
            for i in 0..arena.apply_args(inner.args).len() {
                let (lbl, e) = arena.apply_args(inner.args)[i];
                let rw = rewrite_child(e, arena);
                args.push((lbl, push_rewritten(arena, rw)));
            }
            ExpressionDesc::Pexp_apply(PexpApply {
                funct,
                args: arena.push_apply_args(&args),
                partial: *partial,
                transformed_jsx: *transformed_jsx,
            })
        }

        ExpressionDesc::Pexp_match(inner) => {
            let (ref scrutinee, ref cases) = *inner;
            // Boolean match → if-then-else conversion
            // OCaml's bs_builtin_ppx.ml (lines 138-167) converts:
            //   switch b { | true => t | false => f }
            // to:
            //   if b { t } else { f }
            if cases.len() == 2
                && arena.case_list(*cases)[0].pc_guard.is_none()
                && arena.case_list(*cases)[1].pc_guard.is_none()
            {
                let is_true = |pat: &Pattern| -> bool {
                    if let PatternDesc::Ppat_construct(lid, args) = &pat.ppat_desc
                        && args.txt.is_empty()
                    {
                        matches!(arena.get_longident(lid.txt), Longident::Lident(s) if arena.get_string(*s) == "true")
                    } else {
                        false
                    }
                };
                let is_false = |pat: &Pattern| -> bool {
                    if let PatternDesc::Ppat_construct(lid, args) = &pat.ppat_desc
                        && args.txt.is_empty()
                    {
                        matches!(arena.get_longident(lid.txt), Longident::Lident(s) if arena.get_string(*s) == "false")
                    } else {
                        false
                    }
                };
                let (t_exp, f_exp) = if is_true(arena.get_pat(arena.case_list(*cases)[0].pc_lhs))
                    && is_false(arena.get_pat(arena.case_list(*cases)[1].pc_lhs))
                {
                    (
                        Some(&arena.case_list(*cases)[0].pc_rhs),
                        Some(&arena.case_list(*cases)[1].pc_rhs),
                    )
                } else if is_false(arena.get_pat(arena.case_list(*cases)[0].pc_lhs))
                    && is_true(arena.get_pat(arena.case_list(*cases)[1].pc_lhs))
                {
                    (
                        Some(&arena.case_list(*cases)[1].pc_rhs),
                        Some(&arena.case_list(*cases)[0].pc_rhs),
                    )
                } else {
                    (None, None)
                };
                if let (Some(&t_exp), Some(&f_exp)) = (t_exp, f_exp) {
                    let rw_scrutinee = rewrite_child(*scrutinee, arena);
                    let rw_t = rewrite_child(t_exp, arena);
                    let rw_f = rewrite_child(f_exp, arena);
                    return Expression {
                        pexp_desc: ExpressionDesc::Pexp_ifthenelse(Box::new((
                            push_rewritten(arena, rw_scrutinee),
                            push_rewritten(arena, rw_t),
                            Some(push_rewritten(arena, rw_f)),
                        ))),
                        pexp_loc: expr.pexp_loc,
                        pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena).into(),
                    };
                }
            }

            let rw_scrutinee = rewrite_child(*scrutinee, arena);
            let old_cases = arena.case_list(*cases).to_vec();
            let rw_cases = rewrite_cases(&old_cases, arena);
            ExpressionDesc::Pexp_match((
                push_rewritten(arena, rw_scrutinee),
                arena.push_case_list(&rw_cases),
            ))
        }

        ExpressionDesc::Pexp_try(inner) => {
            let (ref body, ref cases, ref finally) = *inner;
            let rw_body = rewrite_child(*body, arena);
            let old_cases = arena.case_list(*cases).to_vec();
            let rw_cases = rewrite_cases(&old_cases, arena);
            let rw_finally = finally.map(|finally| {
                let rw = rewrite_child(finally, arena);
                push_rewritten(arena, rw)
            });
            ExpressionDesc::Pexp_try((
                push_rewritten(arena, rw_body),
                arena.push_case_list(&rw_cases),
                rw_finally,
            ))
        }

        ExpressionDesc::Pexp_tuple(exprs) => ExpressionDesc::Pexp_tuple({
            let items = arena
                .expr_list(*exprs)
                .to_vec()
                .iter()
                .map(|e| {
                    let rw = rewrite_child(*e, arena);
                    push_rewritten(arena, rw)
                })
                .collect::<Vec<_>>();
            arena.push_expr_list(&items)
        }),

        // Ast_mapper: `Exp.template (List.map map_loc source_segments)
        // (List.map (sub.expr sub) values)`.
        ExpressionDesc::Pexp_template(template) => {
            let values = template
                .values
                .iter()
                .map(|e| {
                    let rw = rewrite_child(*e, arena);
                    push_rewritten(arena, rw)
                })
                .collect();
            ExpressionDesc::Pexp_template(Box::new(current::PexpTemplate {
                source_segments: template.source_segments.clone(),
                values,
            }))
        }
        // Ast_mapper: `Exp.tagged_template (sub.expr sub tag) raw_sources
        // (List.map (sub.expr sub) values)`; OCaml evaluates the arguments
        // right to left, so the values are mapped before the tag.
        ExpressionDesc::Pexp_tagged_template(template) => {
            let values = template
                .values
                .iter()
                .map(|e| {
                    let rw = rewrite_child(*e, arena);
                    push_rewritten(arena, rw)
                })
                .collect();
            let tag_expr = arena.get_expr(template.tag).clone();
            let tag = rewrite_expression(&tag_expr, arena);
            ExpressionDesc::Pexp_tagged_template(Box::new(current::PexpTaggedTemplate {
                tag: arena.push_expr(tag),
                raw_sources: template.raw_sources.clone(),
                values,
            }))
        }

        ExpressionDesc::Pexp_construct(ctor, args) => {
            let mut args = *args;
            // The rewritten node gets its own list; the original keeps its own.
            let mut new_items = arena.expr_list(args.txt).to_vec();
            for e in new_items.iter_mut() {
                let rw = rewrite_child(*e, arena);
                *e = push_rewritten(arena, rw);
            }
            args.txt = arena.push_expr_list(&new_items);
            ExpressionDesc::Pexp_construct(*ctor, args)
        }

        ExpressionDesc::Pexp_variant(inner) => {
            let (ref label, ref args) = **inner;
            let mut args = *args;
            // The rewritten node gets its own list; the original keeps its own.
            let mut new_items = arena.expr_list(args.txt).to_vec();
            for e in new_items.iter_mut() {
                let rw = rewrite_child(*e, arena);
                *e = push_rewritten(arena, rw);
            }
            args.txt = arena.push_expr_list(&new_items);
            ExpressionDesc::Pexp_variant(Box::new((label.clone(), args)))
        }

        ExpressionDesc::Pexp_record(inner) => {
            let (ref fields, ref spread) = *inner;
            let new_fields = arena
                .expr_field_list(*fields)
                .to_vec()
                .iter()
                .map(|f| current::ExpressionRecordField {
                    lid: f.lid,
                    expr: {
                        let rw = rewrite_child(f.expr, arena);
                        push_rewritten(arena, rw)
                    },
                    opt: f.opt,
                })
                .collect::<Vec<_>>();
            let rw_spread = spread.map(|e| {
                let rw = rewrite_child(e, arena);
                push_rewritten(arena, rw)
            });
            ExpressionDesc::Pexp_record((arena.push_expr_field_list(&new_fields), rw_spread))
        }

        ExpressionDesc::Pexp_field(e, lid) => {
            let rw = rewrite_child(*e, arena);
            ExpressionDesc::Pexp_field(push_rewritten(arena, rw), *lid)
        }

        ExpressionDesc::Pexp_setfield(inner) => {
            let (ref e1, ref lid, ref e2) = **inner;
            let rw1 = rewrite_child(*e1, arena);
            let rw2 = rewrite_child(*e2, arena);
            ExpressionDesc::Pexp_setfield(Box::new((
                push_rewritten(arena, rw1),
                *lid,
                push_rewritten(arena, rw2),
            )))
        }

        // ast_mapper.ml `Pexp_spread`: map the items and spreads in order.
        ExpressionDesc::Pexp_spread(kind, elements) => {
            let elements = arena.spread_element_list(*elements).to_vec();
            let elements: Vec<SpreadElement> = elements
                .into_iter()
                .map(|element| {
                    let mut rewrite = |e: ExprIdx| {
                        let e = arena.get_expr(e).clone();
                        let rw = rewrite_expression(&e, arena);
                        arena.push_expr(rw)
                    };
                    match element {
                        SpreadElement::Pspread_item(e) => SpreadElement::Pspread_item(rewrite(e)),
                        SpreadElement::Pspread(e) => SpreadElement::Pspread(rewrite(e)),
                    }
                })
                .collect();
            ExpressionDesc::Pexp_spread(*kind, arena.push_spread_element_list(&elements))
        }

        ExpressionDesc::Pexp_dict(entries) => ExpressionDesc::Pexp_dict(Box::new(
            entries
                .iter()
                .map(|entry| {
                    let mut rewrite = |e: ExprIdx| {
                        let e = arena.get_expr(e).clone();
                        let rw = rewrite_expression(&e, arena);
                        arena.push_expr(rw)
                    };
                    match entry {
                        DictEntry::Pdict_entry(key, e) => DictEntry::Pdict_entry(*key, rewrite(*e)),
                        DictEntry::Pdict_spread(e) => DictEntry::Pdict_spread(rewrite(*e)),
                    }
                })
                .collect(),
        )),
        ExpressionDesc::Pexp_array(exprs) => ExpressionDesc::Pexp_array({
            let items = arena
                .expr_list(*exprs)
                .to_vec()
                .iter()
                .map(|e| {
                    let rw = rewrite_child(*e, arena);
                    push_rewritten(arena, rw)
                })
                .collect::<Vec<_>>();
            arena.push_expr_list(&items)
        }),

        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (ref cond, ref then_branch, ref else_branch) = **inner;
            let rw_cond = rewrite_child(*cond, arena);
            let rw_then = rewrite_child(*then_branch, arena);
            let rw_else = else_branch.map(|e| {
                let rw = rewrite_child(e, arena);
                push_rewritten(arena, rw)
            });
            ExpressionDesc::Pexp_ifthenelse(Box::new((
                push_rewritten(arena, rw_cond),
                push_rewritten(arena, rw_then),
                rw_else,
            )))
        }

        ExpressionDesc::Pexp_sequence(e1, e2) => {
            let rw1 = rewrite_child(*e1, arena);
            let rw2 = rewrite_child(*e2, arena);
            ExpressionDesc::Pexp_sequence(push_rewritten(arena, rw1), push_rewritten(arena, rw2))
        }

        ExpressionDesc::Pexp_while(cond, body) => {
            let rw_cond = rewrite_child(*cond, arena);
            let rw_body = rewrite_child(*body, arena);
            ExpressionDesc::Pexp_while(push_rewritten(arena, rw_cond), push_rewritten(arena, rw_body))
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
            match &expr.pexp_desc {
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

        ExpressionDesc::Pexp_object_get(inner) => {
            let (ref e, ref method) = **inner;
            let rw = rewrite_child(*e, arena);
            ExpressionDesc::Pexp_object_get(Box::new((push_rewritten(arena, rw), method.clone())))
        }

        // `object_set ~loc ~attrs (sub.expr sub e) (map_loc sub s) (sub.expr sub v)`
        // (ast_mapper.ml): arguments right to left.
        ExpressionDesc::Pexp_object_set(inner) => {
            let (ref e, ref name, ref v) = **inner;
            let rw_v = rewrite_child(*v, arena);
            let v_idx = push_rewritten(arena, rw_v);
            let rw_e = rewrite_child(*e, arena);
            ExpressionDesc::Pexp_object_set(Box::new((push_rewritten(arena, rw_e), name.clone(), v_idx)))
        }

        ExpressionDesc::Pexp_object_literal(fields) => {
            let fields = fields
                .iter()
                .map(|(name, e)| {
                    let rw = rewrite_child(*e, arena);
                    (name.clone(), push_rewritten(arena, rw))
                })
                .collect();
            ExpressionDesc::Pexp_object_literal(Box::new(fields))
        }

        ExpressionDesc::Pexp_assert(e) => {
            let rw = rewrite_child(*e, arena);
            ExpressionDesc::Pexp_assert(push_rewritten(arena, rw))
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
            // The default mapper maps the packed module with `sub.module_expr`
            // (ast_mapper.ml), so externals inside are processed.
            let me = arena.get_mod_expr(*mod_expr_idx).clone();
            let rw = rewrite_module_expr(&me, arena);
            ExpressionDesc::Pexp_pack(arena.push_mod_expr(rw))
        }

        ExpressionDesc::Pexp_letmodule(inner) => {
            let (ref name, ref mod_expr, ref body) = **inner;
            let mod_expr_val = arena.get_mod_expr(*mod_expr).clone();
            // bs_builtin_ppx.ml `expr_mapper`: `module M = await List` and
            // `module M = await (List: ListType)` are dynamic imports.
            let module_type_lid = match awaited_module_path(&mod_expr_val, arena) {
                Some((module_lid, imported, None)) => {
                    let name = local_module_type_name(module_lid.txt, arena);
                    Some((
                        Located {
                            txt: arena.push_lident(&name),
                            loc: module_lid.loc,
                        },
                        imported,
                    ))
                }
                Some((_, imported, Some(mty))) => match &arena.get_mod_type(mty).pmty_desc {
                    ModuleTypeDesc::Pmty_ident(mtyp_lid) => Some((*mtyp_lid, imported)),
                    _ => None,
                },
                None => None,
            };
            if let Some((module_type_lid, imported)) = module_type_lid {
                let transformed_mod_expr =
                    create_await_module_expression(&mod_expr_val, module_type_lid, imported, arena);
                let rw_body = rewrite_child(*body, arena);
                return Expression {
                    pexp_desc: ExpressionDesc::Pexp_letmodule(Box::new((
                        *name,
                        arena.push_mod_expr(transformed_mod_expr),
                        push_rewritten(arena, rw_body),
                    ))),
                    pexp_loc: expr.pexp_loc,
                    pexp_attributes: expr.pexp_attributes.clone(),
                };
            }

            // Default: no await transformation needed, but DO recurse into module structure
            // to handle externals inside the module
            let body_expr = arena.get_expr(*body).clone();
            let rw_mod = rewrite_module_expr(&mod_expr_val, arena);
            let rw_body = rewrite_expression(&body_expr, arena);
            ExpressionDesc::Pexp_letmodule(Box::new((
                *name,
                arena.push_mod_expr(rw_mod),
                arena.push_expr(rw_body),
            )))
        }

        ExpressionDesc::Pexp_letexception(inner) => {
            let (ref exn, ref body) = **inner;
            let rw_body = rewrite_child(*body, arena);
            ExpressionDesc::Pexp_letexception(Box::new((exn.clone(), push_rewritten(arena, rw_body))))
        }

        ExpressionDesc::Pexp_open(inner) => {
            let (ref override_flag, ref mod_name, ref body) = **inner;
            let rw_body = rewrite_child(*body, arena);
            ExpressionDesc::Pexp_open(Box::new((
                *override_flag,
                *mod_name,
                push_rewritten(arena, rw_body),
            )))
        }

        // Pexp_newtype is an early-return case in OCaml's expr_mapper:
        // {e with pexp_desc = Pexp_newtype (s, self.expr self body)}
        // It preserves the original expression's attributes without remapping.
        ExpressionDesc::Pexp_newtype(inner) => {
            let (ref name, ref body) = **inner;
            let rw_body = rewrite_child(*body, arena);
            return Expression {
                pexp_desc: ExpressionDesc::Pexp_newtype(Box::new((
                    *name,
                    push_rewritten(arena, rw_body),
                ))),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            };
        }

        // Extensions - handle %raw, others just clone
        ExpressionDesc::Pexp_extension(ext) => {
            return handle_extension(expr, ext, arena);
        }
        // bs_builtin_ppx.ml `Pexp_raw`.
        ExpressionDesc::Pexp_raw(raw) => {
            return handle_raw_node(raw, arena);
        }
        // bs_builtin_ppx.ml `Pexp_todo`: the message is read as
        // `Ast_payload.semantic_string_of_expression`; the warning pre-pass
        // raised on an invalid one.
        ExpressionDesc::Pexp_todo(todo_node) => {
            let message = todo_node
                .message
                .and_then(|message| checked(expr_semantic_string(arena.get_expr(message), arena)));
            return todo(message, arena, todo_node.name_loc);
        }

        // JSX - recurse into children and props
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            ExpressionDesc::Pexp_jsx_element(Box::new(rewrite_jsx_element(jsx, arena)))
        }
    };

    Expression {
        pexp_desc: new_desc,
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
                let rw = rewrite_child(*e, arena);
                push_rewritten(arena, rw)
            });
            let rw_rhs = rewrite_child(c.pc_rhs, arena);
            Case {
                pc_bar: c.pc_bar,
                pc_lhs: arena.push_pat(rw_lhs),
                pc_guard: rw_guard,
                pc_rhs: push_rewritten(arena, rw_rhs),
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
            let rw = rewrite_child(*e, arena);
            push_rewritten(arena, rw)
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
                name: *name,
            },
            JsxProp::Value {
                name,
                optional,
                value,
            } => JsxProp::Value {
                name: *name,
                optional: *optional,
                value: {
                    let rw = rewrite_child(*value, arena);
                    push_rewritten(arena, rw)
                },
            },
            JsxProp::Spreading { loc, expr } => JsxProp::Spreading {
                loc: *loc,
                expr: {
                    let rw = rewrite_child(*expr, arena);
                    push_rewritten(arena, rw)
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
}

struct DeriveActionConfig {
    name: String,
    name_loc: LocIdx,
    config: Option<ExprIdx>,
}

fn expr_lident_name(expr_idx: ExprIdx, arena: &ParseArena) -> Option<String> {
    let expr = arena.get_expr(expr_idx);
    let ExpressionDesc::Pexp_ident(lid_loc) = &expr.pexp_desc else {
        return None;
    };
    let Longident::Lident(name_idx) = arena.get_longident(lid_loc.txt) else {
        return None;
    };
    Some(arena.get_string(*name_idx).to_string())
}

/// `Ast_payload.ident_or_record_as_config` for `@deriving`
/// (compiler/ml/ast_payload.ml:168-209, via
/// Ast_attributes.process_derive_type). Shapes other than a single
/// unqualified identifier or a record without `...` produce no actions (their
/// warnings are reported by `unrecognized_config_record_warning`).
fn deriving_config_actions(
    payload: &Payload,
    arena: &ParseArena,
) -> PpxResult<Vec<DeriveActionConfig>> {
    let Payload::PStr(items) = payload else {
        return Ok(Vec::new());
    };
    let [item] = items.as_slice() else {
        return Ok(Vec::new());
    };
    let StructureItemDesc::Pstr_eval(inner) = &item.pstr_desc else {
        return Ok(Vec::new());
    };
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(inner.0));
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_record(record) => {
            let (fields, with_obj) = record;
            if with_obj.is_some() {
                return Ok(Vec::new());
            }
            arena
                .expr_field_list(*fields)
                .iter()
                .map(|field| {
                    let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) else {
                        return Err(PpxError::at_loc(
                            expr.pexp_loc,
                            "Qualified label is not allowed",
                        ));
                    };
                    let name = arena.get_string(*name_idx).to_string();
                    let config =
                        if expr_lident_name(field.expr, arena).as_deref() == Some(name.as_str()) {
                            None
                        } else {
                            Some(field.expr)
                        };
                    Ok(DeriveActionConfig {
                        name,
                        name_loc: field.lid.loc,
                        config,
                    })
                })
                .collect()
        }
        ExpressionDesc::Pexp_ident(lid_loc) => match arena.get_longident(lid_loc.txt) {
            Longident::Lident(name_idx) => Ok(vec![DeriveActionConfig {
                name: arena.get_string(*name_idx).to_string(),
                name_loc: lid_loc.loc,
                config: None,
            }]),
            _ => Ok(Vec::new()),
        },
        _ => Ok(Vec::new()),
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

/// Parse @deriving attribute to extract derive actions
fn has_deriving_attribute(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs
        .iter()
        .any(|(name, _)| arena.get_string(name.txt) == "deriving")
}

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
            for config in deriving_config_actions(payload, arena).unwrap_or_default() {
                if config.name == "accessors" {
                    actions.push(DeriveAction::Accessors);
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

/// Uncapitalize the first character of a string
fn uncapitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_lowercase().chain(chars).collect(),
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
        pmod_desc: ModuleExprDesc::Pmod_structure(Box::new(structure_items)),
        pmod_loc: outer_loc,
        pmod_attributes: Attributes::new(),
    };

    let sig_mod_type = ModuleType {
        pmty_desc: ModuleTypeDesc::Pmty_signature(Box::new(signature_items)),
        pmty_loc: outer_loc,
        pmty_attributes: Attributes::new(),
    };

    let constrained_mod = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_constraint(
            arena.push_mod_expr(inner_mod),
            arena.push_mod_type(sig_mod_type),
        ),
        pmod_loc: outer_loc,
        pmod_attributes: Attributes::new(),
    };

    let include_decl = IncludeDeclaration {
        pincl_mod: arena.push_mod_expr(constrained_mod),
        pincl_loc: outer_loc,
        pincl_attributes: Attributes::new(),
    };

    StructureItem {
        pstr_desc: StructureItemDesc::Pstr_include(Box::new(include_decl)),
        pstr_loc: outer_loc,
    }
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
    // Get the last type declaration's attributes (where @deriving should be)
    let Some(last_tdcl) = tdcls.last() else {
        return vec![item.clone()];
    };
    let (actions, new_attrs) = parse_deriving_actions(&last_tdcl.ptype_attributes, arena);

    // `process_derive_type` gives `bs_deriving = Some actions` for any
    // `@deriving`, even with no actions (ast_tdcls.ml:76-105).
    if !has_deriving_attribute(&last_tdcl.ptype_attributes, arena) {
        // No @deriving, but still rewrite type declarations for string transformations in attributes
        let rewritten_tdcls: Vec<TypeDeclaration> = tdcls
            .iter()
            .map(|tdcl| rewrite_type_declaration(tdcl, arena))
            .collect();
        return vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_type(Box::new((rec_flag, rewritten_tdcls))),
            pstr_loc: item.pstr_loc,
        }];
    }

    let loc = item.pstr_loc;

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

    let type_str_item = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_type(Box::new((rec_flag, new_tdcls))),
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
        }
    }

    // Step 3: Wrap everything in `include (struct <type_decl> <includes> end)`
    let mut inner_structure = vec![type_str_item];
    inner_structure.extend(include_items);

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(Box::new(inner_structure)),
        pmod_loc: loc,
        pmod_attributes: Attributes::new(),
    };

    let include_decl = current::IncludeDeclaration {
        pincl_mod: arena.push_mod_expr(mod_expr),
        pincl_loc: loc,
        pincl_attributes: Attributes::new(),
    };

    vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_include(Box::new(include_decl)),
        pstr_loc: loc,
    }]
}

/// `Ast_attributes.process_derive_type` (compiler/frontend/ast_attributes.ml:146-160)
/// over the last declaration's attributes: the first `@deriving` payload is read
/// with `ident_or_record_as_config`, a second one raises `Duplicated_bs_deriving`.
/// Returns the first `@deriving` payload.
fn deriving_process_derive_type<'t>(
    tdcls: &'t [TypeDeclaration],
    arena: &ParseArena,
    warnings: &mut Vec<PpxWarning>,
) -> PpxResult<Option<&'t Payload>> {
    let Some(last_tdcl) = tdcls.last() else {
        return Ok(None);
    };
    let mut first_deriving = None;
    for (attr_name, payload) in &last_tdcl.ptype_attributes {
        if arena.get_string(attr_name.txt) == "deriving" {
            if first_deriving.is_some() {
                return Err(PpxError::at_loc(
                    attr_name.loc,
                    "Duplicate @deriving attribute; a type can only have one.",
                ));
            }
            deriving_config_actions(payload, arena)?;
            // `Ast_payload.ident_or_record_as_config` warns about payloads it
            // cannot use (ast_payload.ml:194-209).
            if let Some((loc, message)) =
                return_wrapper_config_warning(payload, arena, attr_name.loc)
            {
                warnings.push(PpxWarning {
                    loc,
                    warning: Warning::BsDeriveWarning {
                        message: message.to_string(),
                    },
                });
            }
            first_deriving = Some(payload);
        }
    }
    Ok(first_deriving)
}

/// `Ast_tdcls.handle_tdcls_in_stru`/`handle_tdcls_in_sigi`
/// (ast_tdcls.ml:38-108) after the declarations are mapped: action by action,
/// `Ast_derive.dispatch` (ast_derive.ml:48-64) and the deriver's
/// `structure_gen` (structures only) and `signature_gen`.
fn run_derivers(
    tdcls: &[TypeDeclaration],
    arena: &ParseArena,
    in_structure: bool,
    payload: &Payload,
    warnings: &mut Vec<PpxWarning>,
) -> PpxResult<()> {
    if tdcls.is_empty() {
        return Ok(());
    }
    let actions = deriving_config_actions(payload, arena)?;
    for action in &actions {
        // `Ast_derive.dispatch`: the derivers `@deriving(...)` supports, by
        // name.
        match action.name.as_str() {
            "accessors" => {
                // `Ast_derive_projector.check_config`
                // (ast_derive_projector.ml:3-8).
                if let Some(config) = action.config {
                    return Err(PpxError::at_loc(
                        arena.get_expr(config).pexp_loc,
                        "@deriving(accessors) takes no configuration.",
                    ));
                }
                // `Ast_derive_projector.structure_gen` and `signature_gen`
                // (ast_derive_projector.ml:20-146).
                if in_structure {
                    accessors_gen(tdcls, warnings)?;
                }
                accessors_gen(tdcls, warnings)?;
            }
            // The derivers that used to be built in get a dedicated error.
            name => {
                return Err(PpxError::at_loc(
                    action.name_loc,
                    match removed_deriver_hint(name) {
                        Some(hint) => format!("@deriving({name}) has been removed. {hint}"),
                        None => format!(
                            "@deriving({name}) is not supported. The only deriver is @deriving(accessors)."
                        ),
                    },
                ));
            }
        }
    }
    Ok(())
}

/// `Ast_derive.removed_deriver_hint` (compiler/frontend/ast_derive.ml).
fn removed_deriver_hint(name: &str) -> Option<&'static str> {
    match name {
        "abstract" => Some(
            "Use a record type instead. Records compile to plain JavaScript objects and support optional fields (`field?: t`), mutable fields and `@as` field renaming.",
        ),
        "jsConverter" => Some(
            "Records already compile to plain JavaScript objects and polymorphic variants to their (`@as`-renamed) names, so the conversion functions are no longer needed.",
        ),
        _ => None,
    }
}

/// `structure_gen`/`signature_gen` of `Ast_derive_projector`: both raise on a
/// variant constructor with an inline record and warn on abstract and open
/// types.
fn accessors_gen(tdcls: &[TypeDeclaration], warnings: &mut Vec<PpxWarning>) -> PpxResult<()> {
    for tdcl in tdcls {
        match &tdcl.ptype_kind {
            TypeKind::Ptype_record(_) => {}
            TypeKind::Ptype_variant(constructors) => {
                for constructor in constructors {
                    if matches!(constructor.pcd_args, ConstructorArguments::Pcstr_record(_)) {
                        return Err(PpxError::at_loc(
                            constructor.pcd_loc,
                            ACCESSORS_VARIANT_RECORD_ARG_ERROR,
                        ));
                    }
                }
            }
            TypeKind::Ptype_abstract | TypeKind::Ptype_open => {
                push_deriving_not_applicable_warning(tdcl.ptype_loc, "accessors", warnings);
            }
        }
    }
    Ok(())
}

fn is_config_attribute(attr: &Attribute, arena: &ParseArena) -> bool {
    arena.get_string(attr.0.txt) == "config"
}

fn is_builtin_rank0_type_name(name: &str) -> bool {
    matches!(
        name,
        "int" | "char" | "float" | "bool" | "unit" | "exn" | "string"
    )
}

fn core_type_get_uncurry_arity_aux(typ_idx: CoreTypeIdx, acc: i32, arena: &ParseArena) -> i32 {
    let typ = arena.get_core_type(typ_idx);
    match &typ.ptyp_desc {
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
    match &typ.ptyp_desc {
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

fn validate_expression_extension_payload_error(
    extension: &current::Extension,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let (ext_name, payload) = extension;
    let name = arena.get_string(ext_name.txt);
    match name {
        "raw" if payload_raw_source_info(payload, arena).is_none() => Err(PpxError::at_loc(
            ext_name.loc,
            "%raw extension can only be applied to a string",
        )),
        "ffi" => match payload_raw_source_info(payload, arena) {
            Some((code, _, _)) if is_js_function(&code) => Ok(()),
            _ => Err(PpxError::at_loc(
                ext_name.loc,
                "%ffi extension can only be applied to a string containing a JavaScript function such as \"(x) => ...\"",
            )),
        },
        _ => Ok(()),
    }
}

/// The warning pre-pass for a raw node: `Ast_exp_handle_external.
/// raw_source_expression` validates its source like a raw payload
/// (`Ast_payload.validate_raw_source ~kind:Raw_exp`), and `ffi_expression`
/// then rejects a `%ffi` source that is not a function.
fn check_raw_node(
    raw: &PexpRaw,
    arena: &mut ParseArena,
    warnings: &mut Vec<PpxWarning>,
) -> PpxResult<()> {
    let code = crate::ast_raw::js_source(arena, &raw.source);
    let loc = crate::ast_raw::payload_loc(arena, &raw.source);
    // `Bs_flow_ast_utils.flow_deli_offset (Some "js")`.
    if let Some(warning) = raw_js_expression_parse_warning(&code, loc, 4, arena) {
        warnings.push(PpxWarning {
            loc: warning.loc,
            warning: Warning::BsFfiWarning {
                message: warning.message,
            },
        });
    }
    if raw.kind == RawKind::Function && !is_js_function(&code) {
        return Err(PpxError::at_loc(
            raw.name_loc,
            "%ffi extension can only be applied to a string containing a JavaScript function such as \"(x) => ...\"",
        ));
    }
    Ok(())
}

/// The warning pre-pass for `%%raw`: `validate_raw_source ~kind:Raw_program`.
fn check_raw_structure_node(raw: &PstrRaw, arena: &mut ParseArena, warnings: &mut Vec<PpxWarning>) {
    let code = crate::ast_raw::js_source(arena, &raw.source);
    let loc = crate::ast_raw::payload_loc(arena, &raw.source);
    if let Some(warning) = raw_js_program_parse_warning(&code, loc, 4, arena) {
        warnings.push(PpxWarning {
            loc: warning.loc,
            warning: Warning::BsFfiWarning {
                message: warning.message,
            },
        });
    }
}

fn validate_structure_extension_payload_error(
    extension: &current::Extension,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let (ext_name, payload) = extension;
    let name = arena.get_string(ext_name.txt);
    if name == "raw" && payload_raw_source_info(payload, arena).is_none() {
        Err(PpxError::at_loc(
            ext_name.loc,
            "%%raw extension can only be applied to a string",
        ))
    } else {
        Ok(())
    }
}

fn validate_module_record_pattern_binding_error(
    vb: &ValueBinding,
    arena: &ParseArena,
) -> PpxResult<()> {
    let pat = arena.get_pat(vb.pvb_pat);
    let expr = crate::ast_payload::unwrap_braces(arena, arena.get_expr(vb.pvb_expr));

    let (PatternDesc::Ppat_record(record_inner), ExpressionDesc::Pexp_pack(mod_expr_idx)) =
        (&pat.ppat_desc, &expr.pexp_desc)
    else {
        return Ok(());
    };

    let mod_expr = arena.get_mod_expr(*mod_expr_idx);
    if !matches!(&mod_expr.pmod_desc, ModuleExprDesc::Pmod_ident(_)) {
        return Ok(());
    }

    // compiler/frontend/ast_tuple_pattern_flatten.ml rejects record-rest
    // module destructuring before attempting to project any module fields.
    if let Some(rest) = &record_inner.2 {
        return Err(PpxError::at_loc(
            rest.rest_loc,
            "Record rest patterns are not supported when destructuring modules. Bind the module fields explicitly.",
        ));
    }

    let (lid_pats, _, _) = &**record_inner;
    for field in arena.pat_field_list(*lid_pats) {
        if !matches!(arena.get_longident(field.lid.txt), Longident::Lident(_)) {
            return Err(PpxError::at_loc(
                field.lid.loc,
                "Not supported pattern match on modules",
            ));
        }
    }

    Ok(())
}

fn letmodule_expr_has_await_payload(mod_expr: &current::ModuleExpr, arena: &ParseArena) -> bool {
    awaited_module_path_kind(mod_expr, arena).is_some()
}

fn expression_is_lident(expr_idx: ExprIdx, expected: &str, arena: &ParseArena) -> bool {
    let expr = arena.get_expr(expr_idx);
    let ExpressionDesc::Pexp_ident(lid) = &expr.pexp_desc else {
        return false;
    };
    let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
        return false;
    };
    arena.get_string(*name_idx) == expected
}

/// The errors `Ast_exp_apply.app_exp_mapper` (ast_exp_apply.ml:70-135) raises
/// for an infix `->` application before mapping its arguments.
fn app_exp_mapper_error(expr: &Expression, arena: &ParseArena) -> Option<PpxError> {
    // `view_as_app e infix_ops` (ast_exp_apply.ml:61-68).
    let ExpressionDesc::Pexp_apply(inner) = &expr.pexp_desc else {
        return None;
    };
    let PexpApply { funct, args, .. } = inner;
    let args = arena.apply_args(*args);
    if !expression_is_lident(*funct, "->", arena) {
        return None;
    }
    let loc = expr.pexp_loc;
    // `check_and_discard` (ast_exp_apply.ml:47-51): `Bs_syntaxerr.err_if_label`.
    for (label, arg) in args {
        if !matches!(label, ArgLabel::Nolabel) {
            return Some(PpxError::at_loc(
                arena.get_expr(*arg).pexp_loc,
                "Label syntax is not supported in this position",
            ));
        }
    }
    (args.len() != 2).then(|| {
        PpxError::at_loc(
            loc,
            "Invalid pipe syntax. The pipe symbol (->) can only be used as a binary operator.",
        )
    })
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
            Payload::PStr(Box::default()),
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
    _loc: LocIdx,
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
            ppat_desc: PatternDesc::Ppat_var(Located {
                txt: param_str,
                loc: label_loc,
            }),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        };
        let inner_pat_idx = arena.push_pat(inner_pat);
        let param_pat = Pattern {
            ppat_desc: PatternDesc::Ppat_constraint(Box::new((
                inner_pat_idx,
                arena.push_core_type(structure_core_type.clone()),
            ))),
            ppat_loc: none_loc,
            ppat_attributes: Attributes::new(),
        };

        // OCaml: Exp.field (Exp.ident {txt = Lident txt; loc}) {txt = Longident.Lident pld_label; loc}
        // Exp.field and Exp.ident have no ~loc, use default_loc (ghost)
        let fa_lid = arena.push_lident_from_idx(param_str);
        let fa_ident = Expression {
            pexp_desc: ExpressionDesc::Pexp_ident(Located {
                txt: fa_lid,
                loc: label_loc,
            }),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };
        let fa_idx = arena.push_expr(fa_ident);
        let fa_field_lid = arena.push_longident(Longident::Lident(label.pld_name.txt));
        let field_access = Expression {
            pexp_desc: ExpressionDesc::Pexp_field(
                fa_idx,
                Located {
                    txt: fa_field_lid,
                    loc: label_loc,
                },
            ),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };

        // OCaml: Ast_compatible.fun_ ~arity:(Some 1) pat exp - no ~loc
        let fun_expr = Expression {
            pexp_desc: ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label: ArgLabel::Nolabel,
                default: None,
                lhs: arena.push_pat(param_pat),
                rhs: arena.push_expr(field_access),
                is_async: false,
                arity: arena.static_ppx_arity_1(),
            })),
            pexp_loc: none_loc,
            pexp_attributes: Attributes::new(),
        };

        // OCaml: Ast_comb.single_non_rec_value pld_name ...
        // single_non_rec_value = Str.value Nonrecursive [Vb.mk (Pat.var name) exp]
        // - Vb.mk has no ~loc, so pvb_loc = ghost
        // - Str.value has no ~loc, so pstr_loc = ghost
        let binding = ValueBinding {
            pvb_jsx_component: None,
            pvb_pat: arena.push_pat(Pattern {
                ppat_desc: PatternDesc::Ppat_var(Located {
                    txt: label.pld_name.txt,
                    loc: label_loc,
                }),
                ppat_loc: none_loc,
                ppat_attributes: Attributes::new(),
            }),
            pvb_expr: arena.push_expr(fun_expr),
            pvb_attributes: gentype_attrs.clone(),
            pvb_loc: none_loc,
        };

        structure_items.push(StructureItem {
            pstr_desc: StructureItemDesc::Pstr_value((
                RecFlag::Nonrecursive,
                arena.push_vb_list(&[binding]),
            )),
            pstr_loc: none_loc,
        });

        // Signature item: val fieldName: t -> fieldType
        // OCaml: Ast_helper.Typ.arrows [{attrs; lbl; typ}] pld_type - no ~loc
        let arrow_type = CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((
                Box::new(TypeArg {
                    fixed: None,
                    attrs: Attributes::new(),
                    lbl: ArgLabel::Nolabel,
                    typ: arena.push_core_type(signature_core_type.clone()),
                }),
                label.pld_type,
                arena.push_arity(Some(1)),
            ))),
            ptyp_loc: none_loc,
            ptyp_attributes: Attributes::new(),
        };

        // OCaml: Ast_comb.single_non_rec_val pld_name arrow_type
        // single_non_rec_val = Sig.value (Val.mk name ty)
        // - Val.mk has no ~loc, so pval_loc = ghost
        // - Sig.value has no ~loc, so psig_loc = ghost
        let val_desc = ValueDescription {
            pval_jsx_component: None,
            pval_name: Located {
                txt: label.pld_name.txt,
                loc: label_loc,
            },
            pval_type: arena.push_core_type(arrow_type),
            pval_prim: None,
            pval_attributes: gentype_attrs.clone(),
            pval_loc: none_loc,
        };

        signature_items.push(SignatureItem {
            psig_desc: SignatureItemDesc::Psig_value(Box::new(val_desc)),
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
                pexp_desc: ExpressionDesc::Pexp_construct(
                    Located {
                        txt: ctor_lid,
                        loc: ctor_loc,
                    },
                    crate::parse_arena::Located::new(crate::parse_arena::ExprList::EMPTY, ctor_loc),
                ),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };
            let construct_idx = arena.push_expr(construct_expr);
            let ctor_expr = Expression {
                pexp_desc: ExpressionDesc::Pexp_constraint(Box::new((
                    construct_idx,
                    structure_annotate_type,
                ))),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };

            let binding = ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: arena.push_pat(Pattern {
                    ppat_desc: PatternDesc::Ppat_var(Located {
                        txt: fn_name_idx,
                        loc: ctor_loc,
                    }),
                    ppat_loc: none_loc,
                    ppat_attributes: Attributes::new(),
                }),
                pvb_expr: arena.push_expr(ctor_expr),
                pvb_attributes: gentype_attrs.clone(),
                pvb_loc: none_loc,
            };

            structure_items.push(StructureItem {
                pstr_desc: StructureItemDesc::Pstr_value((
                    RecFlag::Nonrecursive,
                    arena.push_vb_list(&[binding]),
                )),
                pstr_loc: none_loc,
            });

            // val ctorName: t
            let val_desc = ValueDescription {
                pval_jsx_component: None,
                pval_name: Located {
                    txt: fn_name_idx,
                    loc: ctor_loc,
                },
                pval_type: arena.push_core_type(signature_annotate_type),
                pval_prim: None,
                pval_attributes: gentype_attrs.clone(),
                pval_loc: none_loc,
            };

            signature_items.push(SignatureItem {
                psig_desc: SignatureItemDesc::Psig_value(Box::new(val_desc)),
                psig_loc: none_loc,
            });
        } else {
            // Has args: let ctorName = (p0, p1, ...) => CtorName(p0, p1, ...)
            let params: Vec<StrIdx> = (0..arity)
                .map(|i| arena.intern_string(&format!("param_{}", i)))
                .collect();

            // ast_derive_projector.ml: one argument per parameter.
            let ctor_args: Vec<ExprIdx> = params
                .iter()
                .map(|&p| {
                    let expr = Expression {
                        pexp_desc: ExpressionDesc::Pexp_ident(Located {
                            txt: arena.push_lident_from_idx(p),
                            loc: ctor_loc,
                        }),
                        pexp_loc: none_loc,
                        pexp_attributes: Attributes::new(),
                    };
                    arena.push_expr(expr)
                })
                .collect();

            let ctor_lid = arena.push_longident(Longident::Lident(ctor.pcd_name.txt));
            let construct_expr = Expression {
                pexp_desc: ExpressionDesc::Pexp_construct(
                    Located {
                        txt: ctor_lid,
                        loc: ctor_loc,
                    },
                    arena.expr_ctor_args(&ctor_args, ctor_loc),
                ),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };
            let construct_idx = arena.push_expr(construct_expr);
            let ctor_expr = Expression {
                pexp_desc: ExpressionDesc::Pexp_constraint(Box::new((
                    construct_idx,
                    structure_annotate_type,
                ))),
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
                        ppat_desc: PatternDesc::Ppat_var(Located {
                            txt: param,
                            loc: ctor_loc,
                        }),
                        ppat_loc: none_loc,
                        ppat_attributes: Attributes::new(),
                    }),
                })
                .collect::<Vec<_>>();
            let first = fun_params[0].clone();
            arena.set_nary_fun_params(arity_id, fun_params, unknown_arity);
            let final_expr = Expression {
                pexp_desc: ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: first.p_lbl,
                    default: None,
                    lhs: first.p_pat,
                    rhs: body,
                    is_async: false,
                    arity: arity_id,
                })),
                pexp_loc: none_loc,
                pexp_attributes: Attributes::new(),
            };

            let binding = ValueBinding {
                pvb_jsx_component: None,
                pvb_pat: arena.push_pat(Pattern {
                    ppat_desc: PatternDesc::Ppat_var(Located {
                        txt: fn_name_idx,
                        loc: ctor_loc,
                    }),
                    ppat_loc: none_loc,
                    ppat_attributes: Attributes::new(),
                }),
                pvb_expr: arena.push_expr(final_expr),
                pvb_attributes: gentype_attrs.clone(),
                pvb_loc: none_loc,
            };

            structure_items.push(StructureItem {
                pstr_desc: StructureItemDesc::Pstr_value((
                    RecFlag::Nonrecursive,
                    arena.push_vb_list(&[binding]),
                )),
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
                    fixed: None,
                    attrs: Attributes::new(),
                    lbl: ArgLabel::Nolabel,
                    typ: *arg_type,
                })
                .collect();
            let arrow_type = make_arrows(args, signature_annotate_type, ctor_loc, arena);

            let val_desc = ValueDescription {
                pval_jsx_component: None,
                pval_name: Located {
                    txt: fn_name_idx,
                    loc: ctor_loc,
                },
                pval_type: arena.push_core_type(arrow_type),
                pval_prim: None,
                pval_attributes: gentype_attrs.clone(),
                pval_loc: none_loc,
            };

            signature_items.push(SignatureItem {
                psig_desc: SignatureItemDesc::Psig_value(Box::new(val_desc)),
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
        ptyp_desc: CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(first),
            arena.push_core_type(ret),
            arity,
        ))),
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
        .map(|(core_type, _)| *core_type)
        .collect();

    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr((
            Located {
                txt: name_lid,
                loc: name_loc,
            },
            arena.push_type_list(&type_args),
        )),
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
///
/// `let_unwrap` is `Experimental_features.is_enabled LetUnwrap`.
pub fn rewrite_structure(
    structure: &[StructureItem],
    arena: &mut ParseArena,
    let_unwrap: bool,
) -> PpxResult<Vec<StructureItem>> {
    rewrite_structure_with_warnings(structure, arena, let_unwrap).0
}

/// [`rewrite_structure`] together with the warnings the builtin mapper
/// prints while mapping, which precede its error when it fails.
pub fn rewrite_structure_with_warnings(
    structure: &[StructureItem],
    arena: &mut ParseArena,
    let_unwrap: bool,
) -> (PpxResult<Vec<StructureItem>>, Vec<PpxWarning>) {
    let mut warnings = Vec::new();
    arena.set_experimental_let_unwrap(let_unwrap);
    let result = rewrite_structure_impl(structure, arena, true, Some(&mut warnings));
    let result = with_deferred_ppx_error(result, arena);
    (result, warnings)
}

/// A nested rewrite error was raised before any error returned directly, so
/// it takes precedence (OCaml's mapper raises at the first failure).
fn with_deferred_ppx_error<T>(result: PpxResult<T>, arena: &mut ParseArena) -> PpxResult<T> {
    match arena.take_ppx_deferred_error() {
        Some(error) => Err(error),
        None => result,
    }
}

/// The order in which OCaml `Bs_builtin_ppx.structure_mapper`
/// (bs_builtin_ppx.ml:676-802) maps the items of `structure`: it recurses as
/// `head :: structure_mapper rest`, evaluated right to left, so most items
/// are mapped after the rest of the structure; `let` items and `@res.await`
/// module aliases bind their mapped item first, and a run of `%%private`
/// items maps its payload before the rest.
/// Whether `structure_mapper` maps `item` before the rest of its structure:
/// a `%%private` run, a `let` item or an `await` module alias
/// (bs_builtin_ppx.ml:747-829); it maps every other item after the rest.
fn structure_mapper_maps_head_first(item: &StructureItem, arena: &ParseArena) -> bool {
    match &item.pstr_desc {
        StructureItemDesc::Pstr_value(_) => true,
        StructureItemDesc::Pstr_module(mb) => is_await_module_alias(mb, arena),
        _ => is_private_extension(item, arena),
    }
}

fn structure_mapper_order(structure: &[StructureItem], arena: &ParseArena) -> Vec<usize> {
    let mut order = std::collections::VecDeque::with_capacity(structure.len());
    let mut units = Vec::new();
    let mut i = 0;
    while i < structure.len() {
        if is_private_extension(&structure[i], arena) {
            let start = i;
            while i < structure.len() && is_private_extension(&structure[i], arena) {
                i += 1;
            }
            units.push((start, i, true));
        } else {
            units.push((i, i + 1, false));
            i += 1;
        }
    }
    for &(start, end, private) in units.iter().rev() {
        if private || structure_mapper_maps_head_first(&structure[start], arena) {
            for index in (start..end).rev() {
                order.push_front(index);
            }
        } else {
            order.push_back(start);
        }
    }
    order.into_iter().collect()
}

/// `warnings` receives the mapper's warnings; it is `None` for the nested
/// structures, which the top-level check has already walked.
fn rewrite_structure_impl(
    structure: &[StructureItem],
    arena: &mut ParseArena,
    apply_spice: bool,
    mut warnings: Option<&mut Vec<PpxWarning>>,
) -> PpxResult<Vec<StructureItem>> {
    // Context for tracking already-created module type names (per-structure scope)
    let mut await_context = std::collections::HashSet::new();
    let spice_mapper_active =
        apply_spice && derive::structure_uses_spice_mapper(structure, arena);

    // OCaml `Bs_builtin_ppx.structure_mapper` (bs_builtin_ppx.ml:676-802)
    // recurses as `head :: structure_mapper rest`. Constructor arguments are
    // evaluated right to left, so most items are mapped after the rest of the
    // structure; `let` items and `@res.await` module aliases bind their mapped
    // item first. A run of `%%private` items maps its payload items first and is
    // wrapped by `expand_reverse` after the rest, which fixes the `local_N`
    // numbering. Plan that order, run it, then assemble results by position.
    enum Unit {
        Item(usize),
        Private(usize, usize),
    }
    enum Event {
        Map(usize),
        MapPrivate(usize),
        WrapPrivate(usize),
    }
    let mut units = Vec::new();
    let mut i = 0;
    while i < structure.len() {
        if is_private_extension(&structure[i], arena) {
            let start = i;
            while i < structure.len() && is_private_extension(&structure[i], arena) {
                i += 1;
            }
            units.push(Unit::Private(start, i));
        } else {
            units.push(Unit::Item(i));
            i += 1;
        }
    }
    let mut order = std::collections::VecDeque::with_capacity(units.len());
    for (unit_index, unit) in units.iter().enumerate().rev() {
        match *unit {
            Unit::Private(..) => {
                order.push_front(Event::MapPrivate(unit_index));
                order.push_back(Event::WrapPrivate(unit_index));
            }
            Unit::Item(index) => {
                let head_first = match &structure[index].pstr_desc {
                    StructureItemDesc::Pstr_value(_) => true,
                    StructureItemDesc::Pstr_module(mb) => is_await_module_alias(mb, arena),
                    _ => false,
                };
                if head_first {
                    order.push_front(Event::Map(unit_index));
                } else {
                    order.push_back(Event::Map(unit_index));
                }
            }
        }
    }

    let mut slots: Vec<Vec<StructureItem>> = (0..units.len()).map(|_| Vec::new()).collect();
    for event in order {
        match event {
            Event::Map(unit_index) => {
                let Unit::Item(index) = units[unit_index] else {
                    unreachable!("item event for a %%private run")
                };
                let mut checker = check::Checker::new(arena);
                let result = checker.structure_mapper_item(&structure[index]);
                if let Some(warnings) = warnings.as_deref_mut() {
                    warnings.append(&mut checker.warnings);
                }
                result?;
                slots[unit_index] = rewrite_structure_unit(
                    &structure[index],
                    arena,
                    apply_spice,
                    spice_mapper_active,
                    &mut await_context,
                )?;
            }
            Event::MapPrivate(unit_index) => {
                let Unit::Private(start, end) = units[unit_index] else {
                    unreachable!("%%private event for an item")
                };
                for item in &structure[start..end] {
                    let mut checker = check::Checker::new(arena);
                    let result = checker.structure_mapper_item(item);
                    if let Some(warnings) = warnings.as_deref_mut() {
                        warnings.append(&mut checker.warnings);
                    }
                    result?;
                }
                let mut mapped = Vec::new();
                for item in &structure[start..end] {
                    let StructureItemDesc::Pstr_extension(inner) = &item.pstr_desc else {
                        unreachable!("%%private run holds extensions")
                    };
                    let ((ext_name, payload), _attrs) = &**inner;
                    // `self.structure_item` on each payload item. `%%raw` and
                    // `%%private` are only expanded by `structure_mapper`, so
                    // here they stay extensions (and `Typemod_hide.check`
                    // rejects them).
                    for work in private_extension_structure_items(payload, ext_name.loc)? {
                        if is_structure_mapper_extension(work, arena) {
                            mapped.push(work.clone());
                        } else if apply_spice {
                            mapped.extend(try_rewrite_structure_item(
                                work,
                                arena,
                                spice_mapper_active,
                            )?);
                        } else {
                            mapped.extend(rewrite_structure_item_no_spice(work, arena));
                        }
                    }
                }
                slots[unit_index] = mapped;
            }
            Event::WrapPrivate(unit_index) => {
                let Unit::Private(start, _) = units[unit_index] else {
                    unreachable!("%%private event for an item")
                };
                let mapped = std::mem::take(&mut slots[unit_index]);
                // `expand_reverse`: `Typemod_hide.check`, then a fresh `local_N`.
                check_private_extension_items(&mapped, arena)?;
                slots[unit_index] = wrap_in_local_module(mapped, structure[start].pstr_loc, arena);
            }
        }
    }
    let result: Vec<StructureItem> = slots.into_iter().flatten().collect();

    Ok(result)
}

/// Map one structure item as `Bs_builtin_ppx.structure_mapper` does outside
/// `%%private` runs: `@res.await` module aliases and `let` items may emit module
/// type declarations (deduplicated per structure) ahead of the item.
fn rewrite_structure_unit(
    item: &StructureItem,
    arena: &mut ParseArena,
    apply_spice: bool,
    spice_mapper_active: bool,
    await_context: &mut std::collections::HashSet<String>,
) -> PpxResult<Vec<StructureItem>> {
    let mut result = Vec::new();
    match &item.pstr_desc {
        StructureItemDesc::Pstr_module(mb) => {
            // OCaml structure_mapper handles module-level await here (not in structure_item mapper)
            // and deduplicates generated module type declarations per structure.
            if let Some(items) = transform_module_await(mb, item.pstr_loc, await_context, arena) {
                result.extend(items);
            } else if apply_spice {
                result.extend(try_rewrite_structure_item(
                    item,
                    arena,
                    spice_mapper_active,
                )?);
            } else {
                result.extend(rewrite_structure_item_no_spice(item, arena));
            }
        }
        StructureItemDesc::Pstr_value(inner) => {
            let (ref _rec_flag, ref bindings) = *inner;
            // Spelunk through the ORIGINAL bindings to find await module types
            // (before expression rewriting transforms them)
            let original_bindings = arena.vb_list(*bindings).to_vec();
            let module_type_decls = spelunk_value_bindings_for_await_module_types(
                &original_bindings,
                await_context,
                arena,
            );

            // Add hoisted module type declarations first
            result.extend(module_type_decls);

            // Then process the structure item normally
            if apply_spice {
                result.extend(try_rewrite_structure_item(
                    item,
                    arena,
                    spice_mapper_active,
                )?);
            } else {
                result.extend(rewrite_structure_item_no_spice(item, arena));
            }
        }
        _ => {
            // Non-Pstr_value items: just process normally
            if apply_spice {
                result.extend(try_rewrite_structure_item(
                    item,
                    arena,
                    spice_mapper_active,
                )?);
            } else {
                result.extend(rewrite_structure_item_no_spice(item, arena));
            }
        }
    }
    Ok(result)
}

/// `module M = await Path` and `module M = await (Path: ModuleType)`, the
/// structure_mapper cases that map their item before the rest of the
/// structure (bs_builtin_ppx.ml `structure_mapper`, `Pstr_module`).
fn is_await_module_alias(mb: &current::ModuleBinding, arena: &ParseArena) -> bool {
    match awaited_module_path_kind(arena.get_mod_expr(mb.pmb_expr), arena) {
        Some(None) => true,
        Some(Some(mty)) => matches!(
            &arena.get_mod_type(mty).pmty_desc,
            ModuleTypeDesc::Pmty_ident(_)
        ),
        None => false,
    }
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
                if let StructureItemDesc::Pstr_extension(inner) = &structure[i].pstr_desc {
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
    if let StructureItemDesc::Pstr_extension(inner) = &item.pstr_desc {
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
    match &item.pstr_desc {
        StructureItemDesc::Pstr_raw(raw) => Ok(vec![handle_raw_structure_node(raw, arena)]),
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
                pstr_desc: StructureItemDesc::Pstr_eval(Box::new((new_expr_idx, attrs.clone()))),
                pstr_loc: item.pstr_loc,
            }])
        }
        StructureItemDesc::Pstr_value(inner) => {
            let (ref rec, ref bindings) = *inner;
            let new_bindings: Vec<_> = arena
                .vb_list(*bindings)
                .to_vec()
                .iter()
                .map(|vb| {
                    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
                    let new_expr = expand_extensions_expr(&vb_expr, arena);
                    let new_expr_idx = arena.push_expr(new_expr);
                    crate::parser::ast::ValueBinding {
                        pvb_jsx_component: vb.pvb_jsx_component.clone(),
                        pvb_pat: vb.pvb_pat,
                        pvb_expr: new_expr_idx,
                        pvb_attributes: vb.pvb_attributes.clone(),
                        pvb_loc: vb.pvb_loc,
                    }
                })
                .collect();
            Ok(vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_value((*rec, arena.push_vb_list(&new_bindings))),
                pstr_loc: item.pstr_loc,
            }])
        }
        StructureItemDesc::Pstr_module(mb) => {
            let new_expr_idx = expand_extensions_mod_expr(mb.pmb_expr, arena)?;
            Ok(vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_module(Box::new(
                    crate::parser::ast::ModuleBinding {
                        pmb_name: mb.pmb_name,
                        pmb_expr: new_expr_idx,
                        pmb_attributes: mb.pmb_attributes.clone(),
                        pmb_loc: mb.pmb_loc,
                    },
                )),
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
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_extension(ext) => {
            let (ref ext_name, ref payload) = **ext;
            let name = arena.get_string(ext_name.txt).to_string();
            match name.as_str() {
                "raw" => {
                    let raw_prim = prim_str(arena, "#raw_expr");
                    handle_raw(expr, payload, arena, raw_prim, ext_name.loc)
                }
                _ => expr.clone(),
            }
        }
        ExpressionDesc::Pexp_raw(raw) if raw.kind == RawKind::Expression => {
            handle_raw_node(raw, arena)
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (ref rec_flag, ref bindings, ref body) = *inner;
            let new_bindings: Vec<_> = arena
                .vb_list(*bindings)
                .to_vec()
                .iter()
                .map(|vb| {
                    let vb_expr = arena.get_expr(vb.pvb_expr).clone();
                    let new_expr = expand_extensions_expr(&vb_expr, arena);
                    let new_expr_idx = arena.push_expr(new_expr);
                    crate::parser::ast::ValueBinding {
                        pvb_jsx_component: vb.pvb_jsx_component.clone(),
                        pvb_pat: vb.pvb_pat,
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
                pexp_desc: ExpressionDesc::Pexp_let((
                    *rec_flag,
                    arena.push_vb_list(&new_bindings),
                    new_body_idx,
                )),
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
                pexp_desc: ExpressionDesc::Pexp_sequence(new_e1_idx, new_e2_idx),
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
    match &me.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => {
            let new_items = expand_extensions(items, arena)?;
            let new_me = ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_structure(Box::new(new_items)),
                pmod_loc: me.pmod_loc,
                pmod_attributes: me.pmod_attributes.clone(),
            };
            Ok(arena.push_mod_expr(new_me))
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (ref name, ref mty, ref body) = **inner;
            let new_body_idx = expand_extensions_mod_expr(*body, arena)?;
            let new_me = ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_functor(Box::new((*name, *mty, new_body_idx))),
                pmod_loc: me.pmod_loc,
                pmod_attributes: me.pmod_attributes.clone(),
            };
            Ok(arena.push_mod_expr(new_me))
        }
        ModuleExprDesc::Pmod_apply(me1, me2) => {
            let new_me1_idx = expand_extensions_mod_expr(*me1, arena)?;
            let new_me2_idx = expand_extensions_mod_expr(*me2, arena)?;
            let new_me = ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_apply(new_me1_idx, new_me2_idx),
                pmod_loc: me.pmod_loc,
                pmod_attributes: me.pmod_attributes.clone(),
            };
            Ok(arena.push_mod_expr(new_me))
        }
        ModuleExprDesc::Pmod_constraint(inner_idx, mty) => {
            let new_inner_idx = expand_extensions_mod_expr(*inner_idx, arena)?;
            let new_me = ModuleExpr {
                pmod_desc: ModuleExprDesc::Pmod_constraint(new_inner_idx, *mty),
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
    let_unwrap: bool,
) -> PpxResult<Vec<SignatureItem>> {
    rewrite_signature_with_warnings(signature, arena, let_unwrap).0
}

/// [`rewrite_signature`] together with the warnings the builtin mapper
/// prints while mapping, which precede its error when it fails.
pub fn rewrite_signature_with_warnings(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
    let_unwrap: bool,
) -> (PpxResult<Vec<SignatureItem>>, Vec<PpxWarning>) {
    arena.set_experimental_let_unwrap(let_unwrap);
    let mut checker = check::Checker::new(arena);
    let checked = checker.signature(signature);
    let warnings = std::mem::take(&mut checker.warnings);
    if let Err(error) = checked {
        return (Err(error), warnings);
    }
    let rewritten = with_deferred_ppx_error(try_rewrite_signature_items(signature, arena), arena);
    (rewritten, warnings)
}

/// Externals nested below a top-level item (in submodules, module types, local
/// modules, or functor bodies). OCaml's builtin mapper validates every external
/// it reaches (compiler/frontend/bs_builtin_ppx.ml structure_item /
/// signature_item mappers), not just top-level ones.
#[derive(Default)]
struct NestedExternals {
    externals: Vec<ValueDescription>,
}

impl super::ast_iter::AstIter for NestedExternals {
    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        if !arena.expr_needs_no_rewrite(idx) {
            super::ast_iter::walk_expr(self, arena, idx);
        }
    }

    fn structure_item(&mut self, arena: &ParseArena, item: &StructureItem) {
        if let StructureItemDesc::Pstr_primitive(vd) = &item.pstr_desc {
            self.externals.push((**vd).clone());
        }
        super::ast_iter::walk_structure_item(self, arena, item);
    }

    fn signature_item(&mut self, arena: &ParseArena, item: &SignatureItem) {
        if let SignatureItemDesc::Psig_value(vd) = &item.psig_desc {
            self.externals.push((**vd).clone());
        }
        super::ast_iter::walk_signature_item(self, arena, item);
    }
}

fn validate_nested_structure_externals(
    item: &StructureItem,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let mut nested = NestedExternals::default();
    super::ast_iter::walk_structure_item(&mut nested, arena, item);
    for vd in &nested.externals {
        validate_external_attribute_errors(vd, arena, &mut Vec::new())?;
    }
    Ok(())
}

fn validate_nested_signature_externals(
    item: &SignatureItem,
    arena: &mut ParseArena,
) -> PpxResult<()> {
    let mut nested = NestedExternals::default();
    super::ast_iter::walk_signature_item(&mut nested, arena, item);
    for vd in &nested.externals {
        validate_external_attribute_errors(vd, arena, &mut Vec::new())?;
    }
    Ok(())
}

fn try_rewrite_signature_items(
    items: &[SignatureItem],
    arena: &mut ParseArena,
) -> PpxResult<Vec<SignatureItem>> {
    let mut rewritten = Vec::new();
    let spice_mapper_active = derive::signature_uses_spice_mapper(items, arena);
    for item in items {
        let expanded_items =
            derive::expand_signature_item_with_mapper(item, arena, spice_mapper_active)
                .map_err(PpxError::message)?;
        for expanded in expanded_items {
            if let SignatureItemDesc::Psig_value(vd) = &expanded.psig_desc {
                validate_external_attribute_errors(vd, arena, &mut Vec::new())?;
            }
            validate_nested_signature_externals(&expanded, arena)?;
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
    try_rewrite_signature_items(items, arena).unwrap_or_else(|error| {
        arena.defer_ppx_error(error);
        items
            .iter()
            .flat_map(|item| {
                let rewritten_item = rewrite_signature_item_no_spice(item, arena);
                expand_signature_deriving_items(item, rewritten_item, arena)
            })
            .collect()
    })
}

/// `Ast_tdcls.handle_tdcls_in_sigi` (compiler/frontend/ast_tdcls.ml:38-72).
fn expand_signature_deriving_items(
    original: &SignatureItem,
    rewritten: SignatureItem,
    arena: &mut ParseArena,
) -> Vec<SignatureItem> {
    let SignatureItemDesc::Psig_type(inner) = &original.psig_desc else {
        return vec![rewritten];
    };
    let (rec_flag, tdcls) = &**inner;
    let Some(last_tdcl) = tdcls.last() else {
        return vec![rewritten];
    };
    let (actions, new_attrs) = parse_deriving_actions(&last_tdcl.ptype_attributes, arena);
    if actions.is_empty() {
        return vec![rewritten];
    }
    let loc = original.psig_loc;

    // `new_tdcls tdcls new_attrs`: the processed `@deriving` is removed from
    // the last declaration; `new_tdcls_new_attrs` is that list mapped.
    let SignatureItemDesc::Psig_type(rewritten_inner) = &rewritten.psig_desc else {
        return vec![rewritten];
    };
    let mut new_tdcls: Vec<TypeDeclaration> = rewritten_inner.1.clone();
    if let Some(last) = new_tdcls.last_mut() {
        last.ptype_attributes = rewrite_attributes(&new_attrs, arena).into();
    }
    let items = {
        // `Sig.type_ ~loc rf new_tdcls_new_attrs ::
        //  Ast_derive.gen_signature tdcls actions rf` (ast_derive.ml:54-58).
        let mut items = vec![SignatureItem {
            psig_desc: SignatureItemDesc::Psig_type(Box::new((*rec_flag, new_tdcls))),
            psig_loc: loc,
        }];
        for action in &actions {
            match action {
                DeriveAction::Accessors => {
                    for tdcl in tdcls.iter() {
                        if let Some((_structure_items, signature_items)) =
                            generate_accessor_items_for_tdcl(tdcl, tdcl.ptype_loc, arena)
                        {
                            items.extend(signature_items);
                        }
                    }
                }
            }
        }
        items
    };

    // `Ast_signature.fuse_all ~loc`: `include sig ... end`.
    let fused = arena.push_mod_type(current::ModuleType {
        pmty_desc: current::ModuleTypeDesc::Pmty_signature(Box::new(items)),
        pmty_loc: loc,
        pmty_attributes: Attributes::new(),
    });
    vec![SignatureItem {
        psig_desc: SignatureItemDesc::Psig_include(Box::new(current::IncludeDescription {
            pincl_mod: fused,
            pincl_loc: loc,
            pincl_attributes: Attributes::new(),
        })),
        psig_loc: loc,
    }]
}

fn try_rewrite_structure_item(
    item: &StructureItem,
    arena: &mut ParseArena,
    spice_mapper_active: bool,
) -> PpxResult<Vec<StructureItem>> {
    let mut result = Vec::new();
    for expanded in derive::expand_structure_item_with_mapper(item, arena, spice_mapper_active)
        .map_err(PpxError::message)?
    {
        if let StructureItemDesc::Pstr_primitive(vd) = &expanded.pstr_desc {
            validate_external_attribute_errors(vd, arena, &mut Vec::new())?;
        }
        validate_nested_structure_externals(&expanded, arena)?;
        let derived = derive::is_derived_item(&expanded, arena);
        let rewritten = rewrite_structure_item_no_spice(&expanded, arena);
        if derived {
            for item in &rewritten {
                derive::mark_generated_item(item, arena);
            }
        }
        result.extend(rewritten);
    }
    Ok(result)
}

/// Rewrite a structure item, potentially returning multiple items for @deriving.
fn rewrite_structure_item(item: &StructureItem, arena: &mut ParseArena) -> Vec<StructureItem> {
    let spice_mapper_active =
        derive::structure_uses_spice_mapper(std::slice::from_ref(item), arena);
    try_rewrite_structure_item(item, arena, spice_mapper_active).unwrap_or_else(|error| {
        arena.defer_ppx_error(error);
        rewrite_structure_item_no_spice(item, arena)
    })
}

fn rewrite_structure_item_no_spice(
    item: &StructureItem,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    match &item.pstr_desc {
        StructureItemDesc::Pstr_primitive(vd) => {
            if is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
                // OCaml rewrites attributes (e.g. "js" -> "*j" in strings) before
                // encoding the external (ast_external.ml line 59).
                let rewritten_attrs = rewrite_attributes(&vd.pval_attributes, arena);
                // Rewrite the type to transform string delimiters in @as attributes
                let vd_type = arena.get_core_type(vd.pval_type).clone();
                let rewritten_type = rewrite_core_type(&vd_type, arena);
                let rewritten_vd = ValueDescription {
                    pval_jsx_component: vd.pval_jsx_component.clone(),
                    pval_name: vd.pval_name,
                    pval_type: arena.push_core_type(rewritten_type.clone()),
                    pval_prim: vd.pval_prim.clone(),
                    pval_attributes: rewritten_attrs.into(),
                    pval_loc: vd.pval_loc,
                };

                let encoded = encode_external(&rewritten_vd, arena);
                let no_inline = encoded.has_relative_path;
                // OCaml's FFI processing (ast_external_process.ml handle_attributes)
                // reconstructs the arrow type with ptyp_loc = pval_loc.
                // For @obj externals, also reconstructs Ptyp_any -> Ptyp_object.
                let pval_type =
                    process_obj_type(&rewritten_type, vd.pval_loc, &vd.pval_attributes, arena);
                let external_result = StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(ValueDescription {
                        pval_jsx_component: vd.pval_jsx_component.clone(),
                        pval_prim: encoded.pval_prim,
                        pval_attributes: encoded.pval_attributes.clone().into(),
                        pval_name: vd.pval_name,
                        pval_type: arena.push_core_type(pval_type.clone()),
                        pval_loc: vd.pval_loc,
                    })),
                    pstr_loc: item.pstr_loc,
                };

                if no_inline {
                    // Wrap in Pstr_include to prevent cross-module inlining
                    // of relative path externals (ast_external.ml lines 78-98)
                    let loc = vd.pval_loc;
                    let sig_value = ValueDescription {
                        pval_jsx_component: vd.pval_jsx_component.clone(),
                        pval_name: vd.pval_name,
                        pval_type: arena.push_core_type(pval_type.clone()),
                        pval_prim: None,
                        pval_attributes: encoded.pval_attributes.clone().into(),
                        pval_loc: vd.pval_loc,
                    };
                    let inner_mod_idx = arena.push_mod_expr(ModuleExpr {
                        pmod_desc: ModuleExprDesc::Pmod_structure(Box::new(vec![external_result])),
                        pmod_loc: loc,
                        pmod_attributes: Attributes::new(),
                    });
                    let sig_mod_type_idx = arena.push_mod_type(ModuleType {
                        pmty_desc: ModuleTypeDesc::Pmty_signature(Box::new(vec![SignatureItem {
                            psig_desc: SignatureItemDesc::Psig_value(Box::new(sig_value)),
                            // This signature describes the same declaration as the
                            // implementation, not a second unused value. Preserve
                            // its identity even when source spans are not retained.
                            // compiler/frontend/ast_external.ml:78-98 gives both
                            // declarations the same source span.
                            psig_loc: item.pstr_loc,
                        }])),
                        pmty_loc: loc,
                        pmty_attributes: Attributes::new(),
                    });
                    let constrained_idx = arena.push_mod_expr(ModuleExpr {
                        pmod_desc: ModuleExprDesc::Pmod_constraint(inner_mod_idx, sig_mod_type_idx),
                        pmod_loc: loc,
                        pmod_attributes: Attributes::new(),
                    });
                    vec![StructureItem {
                        pstr_desc: StructureItemDesc::Pstr_include(Box::new(IncludeDeclaration {
                            pincl_mod: constrained_idx,
                            pincl_loc: loc,
                            pincl_attributes: Attributes::new(),
                        })),
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
                // ast_mapper.ml `value_description`: the component annotation
                // goes back into the attributes, and `Val.mk` takes it out
                // again.
                let written = crate::ast_jsx_component::description_attributes(arena, vd);
                let attrs = Attributes::from_vec(rewrite_attributes(&written, arena));
                let (pval_jsx_component, pval_attributes) =
                    crate::ast_jsx_component::take(arena, attrs);
                vec![StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_primitive(Box::new(ValueDescription {
                        pval_name: vd.pval_name,
                        pval_type: arena.push_core_type(rewritten_type),
                        pval_prim: vd.pval_prim.clone(),
                        pval_jsx_component,
                        pval_attributes,
                        pval_loc: vd.pval_loc,
                    })),
                    pstr_loc: item.pstr_loc,
                }]
            }
        }
        // Handle value bindings - need to rewrite expressions and patterns
        // Also handle @inline transformation
        StructureItemDesc::Pstr_value(inner) => {
            let (ref rec_flag, ref bindings) = *inner;
            // Check for @inline on a single non-recursive let binding.
            // Value constraints must go through the mapper that preserves their
            // current-Parsetree side-table payload.
            if *rec_flag == RecFlag::Nonrecursive
                && bindings.len() == 1
                && arena
                    .value_constraint(arena.vb_list(*bindings)[0].pvb_pat)
                    .is_none()
            {
                let vb = &arena.vb_list(*bindings)[0].clone();
                let maybe_pval_name = match &arena.get_pat(vb.pvb_pat).ppat_desc {
                    PatternDesc::Ppat_var(pval_name) => Some(*pval_name),
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
                        pstr_desc: StructureItemDesc::Pstr_value((*rec_flag, {
                            let items = [ValueBinding {
                                pvb_jsx_component: vb.pvb_jsx_component.clone(),
                                pvb_expr: arena.push_expr(pvb_expr),
                                pvb_pat: arena.push_pat(rewritten_pat),
                                pvb_attributes: rewrite_attributes(&vb.pvb_attributes, arena)
                                    .into(),
                                pvb_loc: vb.pvb_loc,
                            }];
                            arena.push_vb_list(&items)
                        })),
                        pstr_loc: item.pstr_loc,
                    }];
                }
            }

            // Default case: rewrite all bindings. Recursive bindings must keep
            // their original patterns so Typecore can raise Illegal_letrec_pat,
            // matching OCaml.
            let old_bindings = arena.vb_list(*bindings).to_vec();
            let new_bindings = if *rec_flag == RecFlag::Recursive {
                rewrite_value_bindings_without_flattening(&old_bindings, arena)
            } else {
                flatten_value_bindings(&old_bindings, arena)
            };
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_value((
                    *rec_flag,
                    arena.push_vb_list(&new_bindings),
                )),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Handle eval expressions
        StructureItemDesc::Pstr_eval(inner) => {
            let (ref expr, ref attrs) = **inner;
            let rewritten_expr = rewrite_child(*expr, arena);
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_eval(Box::new((
                    push_rewritten(arena, rewritten_expr),
                    rewrite_attributes(attrs, arena).into(),
                ))),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Module - recurse into module structure.
        // Module-level @res.await transformation is handled in rewrite_structure.
        StructureItemDesc::Pstr_module(mb) => {
            let mb_expr = arena.get_mod_expr(mb.pmb_expr).clone();
            let rewritten_mb_expr = rewrite_module_expr(&mb_expr, arena);
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_module(Box::new(current::ModuleBinding {
                    pmb_name: mb.pmb_name,
                    pmb_expr: arena.push_mod_expr(rewritten_mb_expr),
                    pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena).into(),
                    pmb_loc: mb.pmb_loc,
                })),
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
                        pmb_name: mb.pmb_name,
                        pmb_expr: arena.push_mod_expr(rewritten_mb_expr),
                        pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena).into(),
                        pmb_loc: mb.pmb_loc,
                    }
                })
                .collect();
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_recmodule(Box::new(new_mbs)),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Include - recurse into module expression
        StructureItemDesc::Pstr_include(incl) => {
            let incl_mod = arena.get_mod_expr(incl.pincl_mod).clone();
            let rewritten_incl_mod = rewrite_module_expr(&incl_mod, arena);
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_include(Box::new(current::IncludeDeclaration {
                    pincl_mod: arena.push_mod_expr(rewritten_incl_mod),
                    pincl_loc: incl.pincl_loc,
                    pincl_attributes: rewrite_attributes(&incl.pincl_attributes, arena).into(),
                })),
                pstr_loc: item.pstr_loc,
            }]
        }
        // bs_builtin_ppx.ml structure_mapper `Pstr_raw`.
        StructureItemDesc::Pstr_raw(raw) => vec![handle_raw_structure_node(raw, arena)],
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
                handle_private_extension(payload, ext_name.loc, arena).unwrap_or_else(|error| {
                    arena.defer_ppx_error(error);
                    Vec::new()
                })
            } else {
                // Rewrite payload for string transformation
                vec![StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_extension(Box::new((
                        (*ext_name, rewrite_payload(payload, arena)),
                        rewrite_attributes(attrs, arena).into(),
                    ))),
                    pstr_loc: item.pstr_loc,
                }]
            }
        }
        // Handle floating attributes (@@attr) - need to transform strings in payload
        // Bs_builtin_ppx.structure_item_mapper leaves `@@config` untouched
        // (bs_builtin_ppx.ml:633).
        StructureItemDesc::Pstr_attribute(attr) if is_config_attribute(attr, arena) => {
            vec![item.clone()]
        }
        StructureItemDesc::Pstr_attribute(attr) => {
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_attribute(Box::new(rewrite_attribute(
                    attr, arena,
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
            pstr_desc: StructureItemDesc::Pstr_open(Box::new(current::OpenDescription {
                popen_lid: od.popen_lid,
                popen_override: od.popen_override,
                popen_loc: od.popen_loc,
                popen_attributes: rewrite_attributes(&od.popen_attributes, arena).into(),
            })),
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
                pstr_desc: StructureItemDesc::Pstr_modtype(Box::new(
                    current::ModuleTypeDeclaration {
                        pmtd_name: mtd.pmtd_name,
                        pmtd_type,
                        pmtd_attributes: rewrite_attributes(&mtd.pmtd_attributes, arena).into(),
                        pmtd_loc: mtd.pmtd_loc,
                    },
                )),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Handle exception - rewrite attributes
        StructureItemDesc::Pstr_exception(ec) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_exception(Box::new(current::ExtensionConstructor {
                pext_name: ec.pext_name,
                pext_kind: ec.pext_kind.clone(),
                pext_loc: ec.pext_loc,
                pext_attributes: rewrite_attributes(&ec.pext_attributes, arena).into(),
            })),
            pstr_loc: item.pstr_loc,
        }],
        // Handle type extension - rewrite attributes
        StructureItemDesc::Pstr_typext(te) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_typext(Box::new(current::TypeExtension {
                ptyext_path: te.ptyext_path,
                ptyext_params: te.ptyext_params.clone(),
                ptyext_constructors: te
                    .ptyext_constructors
                    .iter()
                    .map(|ec| current::ExtensionConstructor {
                        pext_name: ec.pext_name,
                        pext_kind: ec.pext_kind.clone(),
                        pext_loc: ec.pext_loc,
                        pext_attributes: rewrite_attributes(&ec.pext_attributes, arena).into(),
                    })
                    .collect(),
                ptyext_private: te.ptyext_private,
                ptyext_attributes: rewrite_attributes(&te.ptyext_attributes, arena).into(),
            })),
            pstr_loc: item.pstr_loc,
        }],
    }
}

/// Rewrite a module expression, recursing into structure
fn rewrite_module_expr(
    mod_expr: &current::ModuleExpr,
    arena: &mut ParseArena,
) -> current::ModuleExpr {
    // `module_expr_mapper` (bs_builtin_ppx.ml): outside the dynamic import
    // forms, which the expression and structure mappers rewrite before
    // mapping their children, `await` on a module has no effect. Remove it,
    // keeping its attributes on the module it wraps, so the type checker sees
    // the same module expressions as without it.
    let (_, stripped) = remove_awaits(false, mod_expr, arena);
    let mod_expr = &stripped;
    let new_desc = match &mod_expr.pmod_desc {
        current::ModuleExprDesc::Pmod_structure(items) => {
            let rewritten_items =
                rewrite_structure_impl(items, arena, false, None).unwrap_or_else(|error| {
                    arena.defer_ppx_error(error);
                    items
                        .iter()
                        .flat_map(|item| rewrite_structure_item_no_spice(item, arena))
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
                *param,
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
                *ext_name,
                rewrite_payload(payload, arena),
            )))
        }
        // The default mapper (ast_mapper.ml `M.map`) maps the unpacked
        // expression with `sub.expr`, so `%raw` etc. inside are expanded.
        current::ModuleExprDesc::Pmod_unpack(e) => {
            let rw = rewrite_child(*e, arena);
            current::ModuleExprDesc::Pmod_unpack(push_rewritten(arena, rw))
        }
        // Ident - just clone
        _ => return mod_expr.clone(),
    };

    current::ModuleExpr {
        pmod_desc: new_desc,
        pmod_loc: mod_expr.pmod_loc,
        pmod_attributes: rewrite_attributes(&mod_expr.pmod_attributes, arena).into(),
    }
}

/// Rewrite a module type, recursing into signature and nested module types
fn rewrite_module_type(
    mod_type: &current::ModuleType,
    arena: &mut ParseArena,
) -> current::ModuleType {
    let new_desc = match &mod_type.pmty_desc {
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
                *name,
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
                *ext_name,
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
        pmty_desc: new_desc,
        pmty_loc: mod_type.pmty_loc,
        pmty_attributes: rewrite_attributes(&mod_type.pmty_attributes, arena).into(),
    }
}

fn rewrite_signature_item_no_spice(item: &SignatureItem, arena: &mut ParseArena) -> SignatureItem {
    match &item.psig_desc {
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
                    pval_jsx_component: vd.pval_jsx_component.clone(),
                    pval_name: vd.pval_name,
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
                    psig_desc: SignatureItemDesc::Psig_value(Box::new(ValueDescription {
                        pval_jsx_component: vd.pval_jsx_component.clone(),
                        pval_prim: encoded.pval_prim,
                        pval_attributes: encoded.pval_attributes.into(),
                        pval_name: vd.pval_name,
                        pval_type: arena.push_core_type(pval_type),
                        pval_loc: vd.pval_loc,
                    })),
                    psig_loc: item.psig_loc,
                }
            } else if let Some(inline_vd) = transform_inline_sig_value(vd, arena) {
                // Handle @inline("value") let x: t in signature
                // (bs_builtin_ppx.ml line 413-478)
                SignatureItem {
                    psig_desc: SignatureItemDesc::Psig_value(Box::new(inline_vd)),
                    psig_loc: item.psig_loc,
                }
            } else {
                // Ast_mapper.default_mapper.value_description maps `pval_type`
                // through `typ_mapper` (Ast_core_type_class_type.typ_mapper),
                // which expands `@get`/`@set` object fields.
                let vd_type = arena.get_core_type(vd.pval_type).clone();
                let rewritten_type = rewrite_core_type(&vd_type, arena);
                // ast_mapper.ml `value_description`: the component annotation
                // goes back into the attributes, and `Val.mk` takes it out
                // again.
                let written = crate::ast_jsx_component::description_attributes(arena, vd);
                let attrs = Attributes::from_vec(rewrite_attributes(&written, arena));
                let (pval_jsx_component, pval_attributes) =
                    crate::ast_jsx_component::take(arena, attrs);
                SignatureItem {
                    psig_desc: SignatureItemDesc::Psig_value(Box::new(ValueDescription {
                        pval_name: vd.pval_name,
                        pval_type: arena.push_core_type(rewritten_type),
                        pval_prim: vd.pval_prim.clone(),
                        pval_jsx_component,
                        pval_attributes,
                        pval_loc: vd.pval_loc,
                    })),
                    psig_loc: item.psig_loc,
                }
            }
        }
        // Handle floating attributes (@@attr) - need to transform strings in payload
        SignatureItemDesc::Psig_attribute(attr) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_attribute(Box::new(rewrite_attribute(attr, arena))),
            psig_loc: item.psig_loc,
        },
        // Handle extensions - need to transform strings in payload
        SignatureItemDesc::Psig_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            let (ext_name, payload) = ext;
            SignatureItem {
                psig_desc: SignatureItemDesc::Psig_extension(Box::new((
                    (*ext_name, rewrite_payload(payload, arena)),
                    rewrite_attributes(attrs, arena).into(),
                ))),
                psig_loc: item.psig_loc,
            }
        }
        // Handle open - rewrite attributes
        SignatureItemDesc::Psig_open(od) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_open(Box::new(current::OpenDescription {
                popen_lid: od.popen_lid,
                popen_override: od.popen_override,
                popen_loc: od.popen_loc,
                popen_attributes: rewrite_attributes(&od.popen_attributes, arena).into(),
            })),
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
                psig_desc: SignatureItemDesc::Psig_modtype(Box::new(
                    current::ModuleTypeDeclaration {
                        pmtd_name: mtd.pmtd_name,
                        pmtd_type,
                        pmtd_attributes: rewrite_attributes(&mtd.pmtd_attributes, arena).into(),
                        pmtd_loc: mtd.pmtd_loc,
                    },
                )),
                psig_loc: item.psig_loc,
            }
        }
        // Handle exception - rewrite attributes
        SignatureItemDesc::Psig_exception(ec) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_exception(Box::new(current::ExtensionConstructor {
                pext_name: ec.pext_name,
                pext_kind: ec.pext_kind.clone(),
                pext_loc: ec.pext_loc,
                pext_attributes: rewrite_attributes(&ec.pext_attributes, arena).into(),
            })),
            psig_loc: item.psig_loc,
        },
        // Handle type extension - rewrite attributes
        SignatureItemDesc::Psig_typext(te) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_typext(Box::new(current::TypeExtension {
                ptyext_path: te.ptyext_path,
                ptyext_params: te.ptyext_params.clone(),
                ptyext_constructors: te
                    .ptyext_constructors
                    .iter()
                    .map(|ec| current::ExtensionConstructor {
                        pext_name: ec.pext_name,
                        pext_kind: ec.pext_kind.clone(),
                        pext_loc: ec.pext_loc,
                        pext_attributes: rewrite_attributes(&ec.pext_attributes, arena).into(),
                    })
                    .collect(),
                ptyext_private: te.ptyext_private,
                ptyext_attributes: rewrite_attributes(&te.ptyext_attributes, arena).into(),
            })),
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
                psig_desc: SignatureItemDesc::Psig_type(Box::new((*rec_flag, rewritten_tdcls))),
                psig_loc: item.psig_loc,
            }
        }
        // Handle include - recurse into module type
        SignatureItemDesc::Psig_include(incl) => {
            let incl_mod = arena.get_mod_type(incl.pincl_mod).clone();
            let rewritten_incl_mod = rewrite_module_type(&incl_mod, arena);
            SignatureItem {
                psig_desc: SignatureItemDesc::Psig_include(Box::new(current::IncludeDescription {
                    pincl_mod: arena.push_mod_type(rewritten_incl_mod),
                    pincl_loc: incl.pincl_loc,
                    pincl_attributes: rewrite_attributes(&incl.pincl_attributes, arena).into(),
                })),
                psig_loc: item.psig_loc,
            }
        }
        // Handle module - recurse into module type
        SignatureItemDesc::Psig_module(md) => {
            let mod_type = arena.get_mod_type(md.pmd_type).clone();
            let rewritten_mod_type = rewrite_module_type(&mod_type, arena);
            SignatureItem {
                psig_desc: SignatureItemDesc::Psig_module(Box::new(current::ModuleDeclaration {
                    pmd_name: md.pmd_name,
                    pmd_type: arena.push_mod_type(rewritten_mod_type),
                    pmd_attributes: rewrite_attributes(&md.pmd_attributes, arena).into(),
                    pmd_loc: md.pmd_loc,
                })),
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
                        pmd_name: md.pmd_name,
                        pmd_type: arena.push_mod_type(rewritten_mod_type),
                        pmd_attributes: rewrite_attributes(&md.pmd_attributes, arena).into(),
                        pmd_loc: md.pmd_loc,
                    }
                })
                .collect();
            SignatureItem {
                psig_desc: SignatureItemDesc::Psig_recmodule(Box::new(new_mds)),
                psig_loc: item.psig_loc,
            }
        } // All SignatureItemDesc variants are covered above
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{Parser, module};

    /// `Builtin_attributes.warning_attribute` reads `@@warning` with
    /// `string_of_payload`, which raises on a PPX's template with an invalid
    /// escape (ast_payload.ml:39-51): the frontend reports it instead of
    /// treating the payload as no string.
    #[test]
    fn leading_warning_attribute_with_invalid_template_is_an_error() {
        let mut parser = crate::parser::Parser::new("test.res", "@@warning(\"BAD\")\nlet x = 1\n");
        let structure = crate::parser::module::parse_structure(&mut parser);
        let mut arena = parser.into_arena();
        let StructureItemDesc::Pstr_attribute(attr) = &structure[0].pstr_desc else {
            panic!("expected a floating attribute");
        };
        let Payload::PStr(items) = &attr.1 else {
            panic!("expected a structure payload");
        };
        let StructureItemDesc::Pstr_eval(eval) = &items[0].pstr_desc else {
            panic!("expected an expression payload");
        };
        let expr_idx = eval.0;
        let source_idx = arena.intern("Fo\\xo");
        let expr = arena.get_expr_mut(expr_idx);
        let loc = expr.pexp_loc;
        expr.pexp_desc = ExpressionDesc::Pexp_template(Box::new(crate::parser::ast::PexpTemplate {
            source_segments: vec![Located { txt: source_idx, loc }],
            values: vec![],
        }));
        let error = collect_leading_builtin_warning_attributes(&structure, &arena)
            .expect_err("an invalid escape is an error");
        assert_eq!(error.message_text(), "Invalid string escape sequence");
        assert_eq!(error.loc(), Some(loc));
    }

    fn parse_structure(source: &str) -> (ParseArena, Vec<StructureItem>) {
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(
            !parser.has_errors(),
            "parser errors: {:?}",
            parser.diagnostics()
        );
        (parser.into_arena(), structure)
    }

    /// The `%todo` calls of the `let x = () => %todo...` bindings of a
    /// rewritten structure: the called function and the message text.
    fn todo_calls(arena: &ParseArena, structure: &[StructureItem]) -> Vec<(String, String)> {
        let print = |lid: &crate::parser::longident::Longident| -> String {
            match lid {
                crate::parser::longident::Longident::Ldot(prefix, name) => {
                    let crate::parser::longident::Longident::Lident(prefix) = &**prefix else {
                        panic!("expected Module.name");
                    };
                    format!("{}.{}", arena.get_string(*prefix), arena.get_string(*name))
                }
                _ => panic!("expected Module.name"),
            }
        };
        structure
            .iter()
            .filter_map(|item| match &item.pstr_desc {
                StructureItemDesc::Pstr_value((_, bindings)) => {
                    Some(arena.vb_list(*bindings)[0].pvb_expr)
                }
                _ => None,
            })
            .filter_map(|expr| match &arena.get_expr(expr).pexp_desc {
                ExpressionDesc::Pexp_fun(fun) => Some(fun.rhs),
                _ => None,
            })
            .map(|body| {
                let ExpressionDesc::Pexp_apply(apply) = &arena.get_expr(body).pexp_desc else {
                    panic!("expected the %todo call");
                };
                let ExpressionDesc::Pexp_ident(funct) = &arena.get_expr(apply.funct).pexp_desc
                else {
                    panic!("expected a function name");
                };
                let (_, message) = arena.apply_args(apply.args)[0];
                let ExpressionDesc::Pexp_constant(Constant::String(text)) =
                    arena.get_expr(message).pexp_desc
                else {
                    panic!("expected the message");
                };
                (
                    print(arena.get_longident(funct.txt)),
                    text.semantic(arena).to_string(),
                )
            })
            .collect()
    }

    /// ast_exp_extension.ml `todo`: `Stdlib_JsError.throwWithMessage`, not a
    /// `JsError` a user module could shadow, with the message located like
    /// `__LOC__` (the file's base name, the line and the columns of `%todo`).
    /// A payload other than a string gives no message.
    #[test]
    fn todo_calls_stdlib_js_error_with_base_name_and_columns() {
        let source = "let a = () => %todo
let b = 1
let c = () => %todo(\"later\")
let d = () => %todo(`tmpl`)
let e = () =>
    %todo(1)
";
        let mut parser = Parser::new("/home/me/app/src/D.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "{:?}", parser.diagnostics());
        let mut arena = parser.into_arena();
        let rewritten = rewrite_structure(&structure, &mut arena, false).expect("no error");
        let call = |text: &str| {
            (
                "Stdlib_JsError.throwWithMessage".to_string(),
                text.to_string(),
            )
        };
        assert_eq!(
            todo_calls(&arena, &rewritten),
            [
                call("D.res:1:14-19 - Todo"),
                call("D.res:3:14-19 - Todo: later"),
                call("D.res:4:14-19 - Todo: tmpl"),
                call("D.res:6:4-9 - Todo"),
            ]
        );
    }

    /// The message embeds source coordinates, so a location-free parse asks
    /// for a located one, as `__LOC__` does.
    #[test]
    fn todo_requires_source_locations() {
        let mut parser = Parser::with_locations("D.res", "let a = () => %todo\n", false);
        let structure = module::parse_structure(&mut parser);
        let mut arena = parser.into_arena();
        assert!(!arena.locations_required());
        rewrite_structure(&structure, &mut arena, false).expect("no error");
        assert!(arena.locations_required());
    }

    fn let_unwrap_case_lidents(
        expr_idx: ExprIdx,
        arena: &ParseArena,
    ) -> (LidentIdx, LidentIdx, ExprIdx) {
        // A `let?` block keeps its `Pexp_braces` node around the rewrite.
        let expr = crate::parser::parsetree_viewer::unwrap_braces(arena, arena.get_expr(expr_idx));
        let ExpressionDesc::Pexp_match(match_expr) = &expr.pexp_desc else {
            panic!("expected rewritten let? match");
        };
        let (_, cases) = match_expr;
        let [early_case, continue_case] = arena.case_list(*cases) else {
            panic!("expected early-return and continuation cases");
        };
        let PatternDesc::Ppat_alias(ctor_pat, _) = &arena.get_pat(early_case.pc_lhs).ppat_desc
        else {
            panic!("expected aliased early-return constructor");
        };
        let PatternDesc::Ppat_construct(ctor, _) = &arena.get_pat(*ctor_pat).ppat_desc else {
            panic!("expected early-return constructor");
        };
        let ExpressionDesc::Pexp_ident(rhs) = &arena.get_expr(early_case.pc_rhs).pexp_desc else {
            panic!("expected early-return binder expression");
        };
        (ctor.txt, rhs.txt, continue_case.pc_rhs)
    }

    /// bs_builtin_ppx.ml:250-276, 363-372 and 556-571: the builtin mapper
    /// raises the `let?` errors where it meets the binding, whether LetUnwrap
    /// is enabled deciding which one.
    /// `Ast_helper` constructors take `?loc ?attrs` first, so OCaml evaluates
    /// a node's children before its attributes (ast_helper.ml:423-448,
    /// 469-566, 633-642): the child's error is the first one raised.
    #[test]
    fn builtin_mapper_maps_children_before_declaration_attributes() {
        let first_error_line = |source: &str| {
            let (mut arena, structure) = parse_structure(source);
            let error = rewrite_structure(&structure, &mut arena, false)
                .expect_err("both payloads are invalid");
            let loc = error.loc().expect("the error has a location");
            arena.loc_start(loc).line
        };
        let cases = [
            // module binding
            (
                "@foo(let a = %raw(1))\nmodule M = {\n  let b = %raw(2)\n}\n",
                3,
            ),
            // include
            (
                "@foo(let a = %raw(1))\ninclude {\n  let b = %raw(2)\n}\n",
                3,
            ),
            // module type declaration
            (
                "@foo(let a = %raw(1))\nmodule type S = module type of {\n  let b = %raw(2)\n}\n",
                3,
            ),
            // label declaration: the type before the attributes
            (
                "type t = {\n  @foo(let a = %raw(1)) x: @bar(let b = %raw(2)) int,\n}\n",
                2,
            ),
            // type extension: the constructors before the attributes
            (
                "type t = ..\n@foo(let a = %raw(1))\ntype t += @bar(let b = %raw(2)) B\n",
                3,
            ),
        ];
        for (source, line) in cases {
            assert_eq!(first_error_line(source), line, "{source}");
        }
        let column = |source: &str| {
            let (mut arena, structure) = parse_structure(source);
            let error = rewrite_structure(&structure, &mut arena, false).unwrap_err();
            let start = arena.loc_start(error.loc().unwrap());
            start.cnum - start.bol
        };
        // label declaration: `x: @bar(...)` is reported (OCaml prints 2:41,
        // a one-based column), not `@foo(...)`.
        assert_eq!(
            column("type t = {\n  @foo(let a = %raw(1)) x: @bar(let b = %raw(2)) int,\n}\n"),
            40
        );
    }

    /// bs_builtin_ppx.ml:883-903 and 770-777: a functor body is not in an
    /// async context, whatever the context around the functor, and the
    /// context around it comes back after it; `module M = await List` in a
    /// structure is checked against the context, before the items of that
    /// structure mapped after the rest of it.
    #[test]
    fn builtin_mapper_gives_a_functor_body_no_async_context() {
        let check = |source: &str| -> Option<(i32, i32)> {
            let (mut arena, structure) = parse_structure(source);
            match rewrite_structure(&structure, &mut arena, false) {
                Ok(_) => None,
                Err(error) => {
                    assert_eq!(
                        error.message_text(),
                        AWAIT_NOT_ASYNC_CONTEXT_ERROR,
                        "{source}"
                    );
                    let start = arena.loc_start(error.loc().expect("the error has a location"));
                    Some((start.line, start.cnum - start.bol))
                }
            }
        };
        let functor = "module type S = {\n  let p: promise<int>\n}\n";
        let accepted = [
            format!("{functor}module F = (X: S) => {{\n  let f = async () => await X.p\n}}\n"),
            format!(
                "{functor}module F = (X: S) => {{\n  let x = 1\n}}\nlet v = await Promise.resolve(1)\n"
            ),
            "module M = await List\n".to_string(),
            "let f = async () => {\n  module M = {\n    module L = await List\n  }\n  ()\n}\n"
                .to_string(),
        ];
        for source in &accepted {
            assert_eq!(check(source), None, "{source}");
        }
        let rejected = [
            (format!("{functor}module F = (X: S) => {{\n  let v = await X.p\n}}\n"), (5, 10)),
            (
                format!("{functor}let f = async p => {{\n  module F = (X: S) => {{\n    let v = await X.p\n  }}\n  1\n}}\n"),
                (6, 12),
            ),
            (format!("{functor}module F = (X: S) => {{\n  module L = await List\n}}\n"), (5, 13)),
            (
                "let f = values => {\n  module M = {\n    module L = await List\n  }\n  values\n}\n"
                    .to_string(),
                (3, 15),
            ),
        ];
        for (source, at) in &rejected {
            assert_eq!(check(source), Some(*at), "{source}");
        }
    }

    /// bs_builtin_ppx.ml:165-171: a `Pexp_fun` holds all parameters of one
    /// function, so a `Pexp_fun` in its body is another function, in an
    /// async context exactly when it is async itself. `await` in a plain
    /// function an async function returns is an error at the `await`, and so
    /// is one in that function's default argument; the async function's own
    /// parameters and body stay in its async context.
    #[test]
    fn builtin_mapper_gives_each_function_its_own_async_context() {
        let check = |source: &str| -> Result<(), (i32, i32)> {
            let (mut arena, structure) = parse_structure(source);
            match rewrite_structure(&structure, &mut arena, false) {
                Ok(_) => Ok(()),
                Err(error) => {
                    assert_eq!(error.message_text(), AWAIT_NOT_ASYNC_CONTEXT_ERROR, "{source}");
                    let loc = error.loc().expect("the error has a location");
                    let (start, end) = (arena.loc_start(loc), arena.loc_end(loc));
                    assert_eq!(start.line, end.line, "{source}");
                    Err((start.cnum - start.bol, end.cnum - end.bol))
                }
            }
        };
        let accepted = [
            "let f = async (x, y) => await y + x\n",
            "let f = async x => async y => await y + x\n",
            "let f = async x => y => async z => await z + y + x\n",
            "let f = async x => {\n  let y = await x\n  z => z + y\n}\n",
            "let f = async (~x=await Promise.resolve(1)) => x\n",
            "let f = async x => y => y + x\n",
        ];
        for source in accepted {
            assert_eq!(check(source), Ok(()), "{source}");
        }
        let rejected = [
            ("let f = async x => y => await y + x\n", (24, 31)),
            ("let f = async x => (y => await y)\n", (25, 32)),
            ("let f = x => async y => z => await z\n", (29, 36)),
            ("let f = async x => (~y=await x) => y\n", (23, 30)),
            ("let f = async x => y => z => await z\n", (29, 36)),
        ];
        for (source, columns) in rejected {
            assert_eq!(check(source), Err(columns), "{source}");
        }
    }

    #[test]
    fn let_unwrap_errors_come_from_the_builtin_mapper() {
        let rewrite_error = |source: &str, let_unwrap: bool| {
            let (mut arena, structure) = parse_structure(source);
            match rewrite_structure(&structure, &mut arena, let_unwrap) {
                Ok(_) => None,
                Err(error) => {
                    let loc = error.loc().expect("the error has a location");
                    let start = arena.loc_start(loc);
                    Some((error.message_text().to_string(), start.line, start.cnum - start.bol))
                }
            }
        };
        let nested = "let f = value => {\n  let? Ok(x) = value\n  Ok(x)\n}\n";
        assert_eq!(
            rewrite_error(nested, false),
            Some((LET_UNWRAP_NOT_ENABLED_ERROR.to_string(), 2, 7))
        );
        assert_eq!(rewrite_error(nested, true), None);
        let top_level = "let x = 1\nlet? Some(y) = None\n";
        assert_eq!(
            rewrite_error(top_level, false),
            Some((LET_UNWRAP_NOT_ENABLED_ERROR.to_string(), 2, 5))
        );
        assert_eq!(
            rewrite_error(top_level, true),
            Some((LET_UNWRAP_TOPLEVEL_ERROR.to_string(), 2, 5))
        );
        let unsupported = "let f = value => {\n  let? (a, b) = value\n  a + b\n}\n";
        assert_eq!(
            rewrite_error(unsupported, false),
            Some((LET_UNWRAP_NOT_ENABLED_ERROR.to_string(), 2, 7))
        );
        assert_eq!(
            rewrite_error(unsupported, true),
            Some((LET_UNWRAP_UNSUPPORTED_TYPE_ERROR.to_string(), 2, 7))
        );

        // A structure nested in a module is rewritten with the same setting.
        let nested_module = "module M = {\n  let f = value => {\n    let? Some(x) = value\n    Some(x)\n  }\n}\n";
        assert_eq!(
            rewrite_error(nested_module, false),
            Some((LET_UNWRAP_NOT_ENABLED_ERROR.to_string(), 3, 9))
        );
        assert_eq!(rewrite_error(nested_module, true), None);
        let nested_top_level = "module M = {\n  let? Some(x) = None\n}\n";
        assert_eq!(
            rewrite_error(nested_top_level, true),
            Some((LET_UNWRAP_TOPLEVEL_ERROR.to_string(), 2, 7))
        );
    }

    /// `Ast_derive.dispatch` (ast_derive.ml:48-64) resolves a deriver by
    /// name: accessors rejects any configuration at the configuration's
    /// location, a removed deriver points to its replacement and any other
    /// name is unsupported at the name's location, in structures and
    /// signatures alike.
    #[test]
    fn deriving_dispatch_errors_name_the_deriver() {
        let located = |arena: &ParseArena, error: PpxError| {
            let loc = error.loc().expect("the error has a location");
            let start = arena.loc_start(loc);
            let end = arena.loc_end(loc);
            (
                error.message_text().to_string(),
                start.line,
                start.cnum - start.bol,
                end.cnum - end.bol,
            )
        };
        let structure_error = |source: &str| {
            let (mut arena, structure) = parse_structure(source);
            let error = rewrite_structure(&structure, &mut arena, false)
                .expect_err("the deriver is rejected");
            located(&arena, error)
        };
        let signature_error = |source: &str| {
            let mut parser = Parser::new("test.resi", source);
            let signature = module::parse_signature(&mut parser);
            assert!(
                !parser.has_errors(),
                "parser errors: {:?}",
                parser.diagnostics()
            );
            let mut arena = parser.into_arena();
            let error = rewrite_signature(&signature, &mut arena, false)
                .expect_err("the deriver is rejected");
            located(&arena, error)
        };
        let unknown = "@deriving(lenses)\ntype t = {name: string}\n";
        let unknown_error = (
            "@deriving(lenses) is not supported. The only deriver is @deriving(accessors)."
                .to_string(),
            1,
            10,
            16,
        );
        assert_eq!(structure_error(unknown), unknown_error);
        assert_eq!(signature_error(unknown), unknown_error);
        let config = "@deriving({accessors: true})\ntype t = {name: string}\n";
        let config_error = (
            "@deriving(accessors) takes no configuration.".to_string(),
            1,
            22,
            26,
        );
        assert_eq!(structure_error(config), config_error);
        assert_eq!(signature_error(config), config_error);
        let (message, line, start, end) =
            structure_error("@deriving(abstract)\ntype t = {name: string}\n");
        assert!(
            message.starts_with("@deriving(abstract) has been removed. Use a record type instead."),
            "{message}"
        );
        assert_eq!((line, start, end), (1, 10, 18));
    }

    #[test]
    fn derived_value_groups_survive_frontend_rewriting() {
        let (mut arena, source) = parse_structure(
            "let before = 1\n@spice type a = {x: int}\n@spice type b = string\nlet after = 2\n",
        );
        assert!(source.iter().all(|item| !derive::is_derived_item(item, &arena)));
        let expanded: Vec<_> = source.iter().flat_map(|item|
            derive::expand_structure_item_with_mapper(item, &mut arena, true).unwrap()
        ).collect();
        assert_eq!(expanded.iter().map(|item| derive::is_derived_item(item, &arena))
            .collect::<Vec<_>>(), vec![false, false, true, false, true, false]);
        // Use the original tree: expanding twice would generate codecs twice.
        let rewritten = rewrite_structure_with_warnings(&source, &mut arena, false).0.unwrap();
        assert_eq!(rewritten.iter().map(|item| derive::is_derived_item(item, &arena))
            .collect::<Vec<_>>(), vec![false, false, true, false, true, false]);
    }

    #[test]
    fn rewrite_child_skips_only_certified_subtrees() {
        let source = "let x = ((a, [1, 2]), Some((b, c)), (a, @foo b), (1l, 2), (a, %raw(`1`)), (a, b->f))\n";
        let (mut arena, structure) = parse_structure(source);
        let StructureItemDesc::Pstr_value((_, bindings)) = &structure[0].pstr_desc else {
            panic!("expected binding");
        };
        let root = arena.vb_list(*bindings)[0].pvb_expr;
        let ExpressionDesc::Pexp_tuple(items) = arena.get_expr(root).pexp_desc else {
            panic!("expected tuple");
        };
        let items = arena.expr_list(items).to_vec();
        for &idx in &items[..2] {
            assert!(arena.expr_needs_no_rewrite(idx));
            assert!(matches!(rewrite_child(idx, &mut arena), Rewritten::Same(kept) if kept == idx));
        }
        for &idx in &items[2..] {
            assert!(!arena.expr_needs_no_rewrite(idx));
            assert!(matches!(rewrite_child(idx, &mut arena), Rewritten::New(_)));
        }
        assert!(!arena.expr_needs_no_rewrite(root));
    }

    #[test]
    fn mutating_a_child_invalidates_its_certified_parents() {
        let (mut arena, structure) = parse_structure("let x = ((a, b), c)\n");
        let StructureItemDesc::Pstr_value((_, bindings)) = &structure[0].pstr_desc else {
            panic!("expected binding");
        };
        let root = arena.vb_list(*bindings)[0].pvb_expr;
        let ExpressionDesc::Pexp_tuple(items) = arena.get_expr(root).pexp_desc else {
            panic!("expected tuple");
        };
        let child = arena.expr_list(items)[0];
        assert!(arena.expr_needs_no_rewrite(root));
        assert!(arena.expr_needs_no_rewrite(child));
        let replacement = arena.get_expr(child).clone();
        arena.get_expr_mut(child).pexp_attributes = replacement.pexp_attributes.clone();
        assert!(!arena.expr_needs_no_rewrite(child));
        assert!(!arena.expr_needs_no_rewrite(root));
        let reserved = arena.reserve_expr();
        arena.initialize_expr(reserved, replacement);
        assert!(!arena.expr_needs_no_rewrite(reserved));
    }

    #[test]
    fn rewrite_child_keeps_the_node_of_an_unchanged_leaf() {
        let source = "let x = (a, 1, \"s\", f(b), @foo c)\n";
        let (mut arena, structure) = parse_structure(source);
        let StructureItemDesc::Pstr_value(value) = &structure[0].pstr_desc else {
            panic!("expected value binding");
        };
        let (_, bindings) = value;
        let ExpressionDesc::Pexp_tuple(items) =
            &arena.get_expr(arena.vb_list(*bindings)[0].pvb_expr).pexp_desc
        else {
            panic!("expected tuple");
        };
        let items = arena.expr_list(*items).to_vec();
        let [ident, int, string, apply, attributed] = items[..] else {
            panic!("expected five tuple items");
        };
        for leaf in [ident, int, string] {
            let before = arena.get_expr(leaf).clone();
            let mapped = rewrite_expression(&before, &mut arena);
            assert_eq!(mapped, before, "the mapper leaves such a leaf as it is");
            assert!(matches!(
                rewrite_child(leaf, &mut arena),
                Rewritten::Same(idx) if idx == leaf
            ));
            assert!(arena.is_rewritten_expr_loc(before.pexp_loc));
        }
        assert!(matches!(rewrite_child(apply, &mut arena), Rewritten::Same(idx) if idx == apply));
        // An expression with attributes still goes through the full mapper.
        let rewritten = rewrite_child(attributed, &mut arena);
        assert!(matches!(rewritten, Rewritten::New(_)));
        assert_ne!(push_rewritten(&mut arena, rewritten), attributed);
    }

    #[test]
    fn let_unwrap_shares_static_constructors_but_not_fallback_binder_lidents() {
        let source = r#"
let f = value => {
  let? Ok(_) = value
  let? Ok(_) = value
  value
}
"#;
        let (mut arena, structure) = parse_structure(source);
        let rewritten =
            rewrite_structure(&structure, &mut arena, true).expect("rewrite should work");
        let StructureItemDesc::Pstr_value(value) = &rewritten[0].pstr_desc else {
            panic!("expected value binding");
        };
        let (_, bindings) = value;
        let ExpressionDesc::Pexp_fun(fun) = &arena
            .get_expr(arena.vb_list(*bindings)[0].pvb_expr)
            .pexp_desc
        else {
            panic!("expected function");
        };

        let (first_ctor, first_rhs, second_match) = let_unwrap_case_lidents(fun.rhs, &arena);
        let (second_ctor, second_rhs, _) = let_unwrap_case_lidents(second_match, &arena);

        // `Lident "Error"` is a static value in the OCaml rewrite branch, while
        // `Lident var_name` is allocated from the dynamic fallback variable at
        // each rewrite invocation.
        assert_eq!(first_ctor, second_ctor);
        assert_ne!(first_rhs, second_rhs);
        assert_eq!(
            arena.get_string(arena.get_longident(first_ctor).last_idx()),
            "Error"
        );
        assert_eq!(
            arena.get_string(arena.get_longident(first_rhs).last_idx()),
            "x"
        );
    }

    fn obj_optional_label_nested_flags(source: &str) -> Vec<(String, bool)> {
        let (mut arena, structure) = parse_structure(source);
        let StructureItemDesc::Pstr_primitive(vd) = &structure[0].pstr_desc else {
            panic!("expected external");
        };
        let encoded = encode_external(vd, &mut arena);
        let Some(PrimitiveRepr::PrimFfi { spec, .. }) = encoded.pval_prim else {
            panic!("expected encoded FFI primitive");
        };
        let ExternalFfi::FfiObjCreate(params) = *spec else {
            panic!("expected @obj creation");
        };
        params
            .into_iter()
            .filter_map(|param| match param.obj_arg_label {
                Label::ObjOptional {
                    name,
                    for_sure_no_nested_option,
                } => Some((name, for_sure_no_nested_option)),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn obj_optional_builtin_rank0_types_include_char_like_ocaml() {
        // OCaml `Ast_core_type.is_builtin_rank0_type` includes "char".
        let flags = obj_optional_label_nested_flags(
            "@obj external mk: (~c: char=?, ~i: int=?, ~o: option<int>=?, unit) => _ = \"\"",
        );
        assert_eq!(
            flags,
            [
                ("c".to_string(), true),
                ("i".to_string(), true),
                ("o".to_string(), false)
            ]
        );
    }

    #[test]
    fn test_first_char_special() {
        assert!(first_char_special("#foo"));
        assert!(first_char_special("?foo"));
        assert!(first_char_special("%foo"));
        assert!(!first_char_special("foo"));
        assert!(!first_char_special(""));
    }

    #[test]
    fn test_prim_to_be_encoded() {
        assert!(prim_to_be_encoded("console.log"));
        assert!(!prim_to_be_encoded("#foo"));
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

    #[test]
    fn spice_expands_nested_inline_record_variants_once() {
        let source = r#"
module Story = {
  @spice
  type event =
    | Rename({name: string})
    | Resize({width: int, height: int})
}

@spice
type envelope = Story(Story.event)
"#;
        let (mut arena, structure) = parse_structure(source);
        let rewritten =
            rewrite_structure(&structure, &mut arena, true).expect("rewrite should work");
        let StructureItemDesc::Pstr_module(module) = &rewritten[0].pstr_desc else {
            panic!("expected nested module");
        };
        let module_expr = arena.get_mod_expr(module.pmb_expr);
        let ModuleExprDesc::Pmod_structure(items) = &module_expr.pmod_desc else {
            panic!("expected nested module structure");
        };

        let codec_names = items
            .iter()
            .filter_map(|item| match &item.pstr_desc {
                StructureItemDesc::Pstr_value(value) => Some(arena.vb_list(value.1)),
                _ => None,
            })
            .flatten()
            .filter_map(|binding| match &arena.get_pat(binding.pvb_pat).ppat_desc {
                PatternDesc::Ppat_var(name) => Some(arena.get_string(name.txt)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            codec_names,
            ["event_encode", "event_encodeJson", "event_decode"]
        );
    }

    /// ppx_spice 0.10.1 (signature.ml `add_encoder_params`) gives a type
    /// parameter's encoder argument (`'a => JSON.t`) arity 1, like the
    /// decoder argument, so the signature a `.resi` gets matches the values
    /// its implementation gets.
    #[test]
    fn spice_signature_codec_arguments_have_arity_one() {
        let mut parser = Parser::new("test.resi", "@spice\ntype t<'a, 'b> = {a: 'a, b: 'b}\n");
        let signature = module::parse_signature(&mut parser);
        assert!(
            !parser.has_errors(),
            "parser errors: {:?}",
            parser.diagnostics()
        );
        let mut arena = parser.into_arena();
        let rewritten =
            rewrite_signature(&signature, &mut arena, true).expect("rewrite should work");
        let arrow = |ty: CoreTypeIdx| match &arena.get_core_type(ty).ptyp_desc {
            CoreTypeDesc::Ptyp_arrow(arrow) => {
                Some((arrow.0.typ, arrow.1, arena.get_arity(arrow.2)))
            }
            _ => None,
        };
        let mut codecs = Vec::new();
        for item in &rewritten {
            let SignatureItemDesc::Psig_value(value) = &item.psig_desc else {
                continue;
            };
            // The two codec arguments, each a one-argument function, then
            // the value or the JSON.
            let mut ty = value.pval_type;
            for _ in 0..2 {
                let (argument, result, arity) = arrow(ty).expect("a codec argument");
                assert_eq!(arity, Some(1));
                let (_, _, argument_arity) = arrow(argument).expect("a codec");
                assert_eq!(argument_arity, Some(1));
                ty = result;
            }
            assert_eq!(arrow(ty).map(|(_, _, arity)| arity), Some(Some(1)));
            codecs.push(arena.get_string(value.pval_name.txt).to_string());
        }
        assert_eq!(codecs, ["t_encode", "t_encodeJson", "t_decode"]);
    }

    #[test]
    fn validation_skips_preserve_diagnostics_and_order() {
        for source in [
            "let x = (2147483648, 4294967296, 1)",
            "let x = (f(a, b), @string c, d)",
            "let x = () => (f(a), %todo(\"first\"), await g(b))",
            "let seed = 0\nmodule M = { @get external bad: int = \"bad\" }",
            "let x = { module M = { @get external bad: int = \"bad\" }; f(a) }",
            "let x = (@unknown(%todo(\"payload\")) f(a), %todo(\"last\"))",
        ] {
            let run = |disable_skipping| {
                let (mut arena, items) = parse_structure(source);
                if disable_skipping {
                    // Mutable access to the earliest node invalidates every
                    // allocation-time proof, without changing the tree.
                    arena.get_expr_mut(ExprIdx(0));
                }
                let (result, warnings) = rewrite_structure_with_warnings(&items, &mut arena, true);
                match result {
                    Ok(items) => {
                        if disable_skipping {
                            arena.get_expr_mut(ExprIdx(0));
                        }
                        let (sweep, error) =
                            collect_unused_attribute_warnings_structure(&items, &arena);
                        format!("{warnings:?}; {sweep:?}; {error:?}")
                    }
                    Err(error) => format!("{warnings:?}; {error:?}"),
                }
            };
            assert_eq!(run(false), run(true), "{source}");
        }
    }

}
