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

use crate::intern::StrIdx;
use crate::parse_arena::{LidentIdx, Located, LocIdx, ParseArena};
use crate::parser::ast::{
    self as current, ArgLabel, Attribute, Case, Constant, ConstructorArguments,
    ConstructorDeclaration, CoreType, CoreTypeDesc, Expression, ExpressionDesc,
    IncludeDeclaration, JsxContainerElement, JsxElement, JsxFragment, JsxProp, JsxUnaryElement,
    LabelDeclaration, ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeDesc, ObjectField, Pattern,
    PatternDesc, PatternRecordField, Payload, RecFlag, RowField, SignatureItem, SignatureItemDesc,
    StructureItem, StructureItemDesc, TypeArg, TypeDeclaration, TypeKind, ValueBinding,
    ValueDescription,
};
use crate::parser::longident::Longident;

use super::ffi_types::{
    encode_ffi_type, Attr, Cst, Delim, ExternalModuleName, ExternalSpec, FfiType, Label, LabelNoname,
    LamConstant, ModuleBindName, ObjParam, Param, Params, PointerInfo, ReturnWrapper,
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

/// Check if the first char of a string is special (OCaml FFI marker)
fn first_char_special(s: &str) -> bool {
    matches!(s.chars().next(), Some('#' | '?' | '%'))
}

/// Check if a string starts with the OCaml marshal magic number
fn starts_with_marshal_magic(s: &str) -> bool {
    let bytes: Vec<u8> = s.bytes().collect();
    bytes.len() >= 4 && bytes[0] == 0x84 && bytes[1] == 0x95 && bytes[2] == 0xA6 && bytes[3] == 0xBE
}

/// Check if primitives need to be encoded as ReScript FFI
fn prims_to_be_encoded(pval_prim: &[String]) -> bool {
    match pval_prim.first() {
        None => false, // shouldn't happen for externals
        Some(first) if first_char_special(first) => false,
        Some(_) => {
            // Check if second string already has marshal magic
            match pval_prim.get(1) {
                Some(second) if starts_with_marshal_magic(second) => false,
                _ => true,
            }
        }
    }
}

/// Check if an external declaration has ReScript FFI attributes
fn has_external_attrs(attrs: &[Attribute], arena: &mut ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _payload)| {
        let name = arena.get_string(attr_name.txt);
        EXTERNAL_ATTRS.iter().any(|&ext_attr| name == ext_attr)
    })
}

/// Check if a value description represents a ReScript external
pub fn is_rs_external(attrs: &[Attribute], pval_prim: &[String], arena: &mut ParseArena) -> bool {
    if pval_prim.is_empty() {
        return false;
    }
    has_external_attrs(attrs, arena) || prims_to_be_encoded(pval_prim)
}

/// Check if attributes contain @obj
fn has_obj_attr(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _)| {
        let name = arena.get_string(attr_name.txt);
        name == "obj"
    })
}

/// Result of classifying a JavaScript expression.
/// This mirrors OCaml's `Js_raw_info.exp` type.
#[derive(Debug, Clone, PartialEq)]
pub enum JsExpClassification {
    /// A function expression (regular or arrow)
    JsFunction {
        arity: usize,
        arrow: bool,
    },
    /// A literal value (string, number, bool, null, undefined, object literal, array literal)
    JsLiteral,
    /// Unknown expression type
    JsExpUnknown,
}

/// Check if an OXC expression is an object literal (recursively).
/// This matches OCaml's `is_obj_literal` function.
fn is_obj_literal(expr: &oxc_ast::ast::Expression) -> bool {
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
        _ => false,
    }
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
                | Expression::RegExpLiteral(_) => JsExpClassification::JsLiteral,
                // undefined identifier
                Expression::Identifier(id) if id.name == "undefined" => {
                    JsExpClassification::JsLiteral
                }
                // Object/array literals (checked recursively)
                _ if is_obj_literal(&expr) => JsExpClassification::JsLiteral,
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

/// Detect if a JavaScript string contains a function expression.
/// This is a convenience wrapper around `classify_js_exp`.
fn is_js_function(s: &str) -> bool {
    matches!(classify_js_exp(s), JsExpClassification::JsFunction { .. })
}

/// Process args from list_of_arrow into FFI Param specs and compute arity.
/// This mirrors OCaml's fold_right in handle_attributes which builds
/// arg_type_specs and arg_type_specs_length.
///
/// Returns (params, arity, args_for_type_reconstruction) where:
/// - params: The Params encoding for the FFI blob
/// - arity: The number of non-ignored args (for determining JsVar vs JsCall)
/// - args_for_type_reconstruction: Args to use for type reconstruction (filtered)
fn build_arg_type_specs(typ: &CoreType, arena: &mut ParseArena) -> (Params, usize) {
    let (args, _result) = list_of_arrow(typ, arena);

    let mut param_specs: Vec<Param> = Vec::new();
    let mut arity = 0;
    let mut all_simple = true; // true if all args are {Nothing, Arg_empty}

    for arg in &args {
        let (label_noname, arg_type) = match &arg.lbl {
            ArgLabel::Optional(_) => {
                // Optional args: get_opt_arg_type
                // For now, simplified: mark as Arg_optional, Nothing
                all_simple = false;
                (LabelNoname::ArgOptional, Attr::Nothing)
            }
            ArgLabel::Labelled(_) => {
                // Labeled args
                let arg_type = refine_arg_type(false, &arg.typ, arena);
                all_simple = false;
                (LabelNoname::ArgLabel, arg_type)
            }
            ArgLabel::Nolabel => {
                let arg_type = refine_arg_type(true, &arg.typ, arena);
                if !matches!(arg_type, Attr::Nothing) || false {
                    // Non-trivial arg type
                }
                (LabelNoname::ArgEmpty, arg_type)
            }
        };

        let is_ignored = matches!(arg_type, Attr::Ignore);
        if !is_ignored {
            arity += 1;
        }

        if !matches!((&label_noname, &arg_type), (LabelNoname::ArgEmpty, Attr::Nothing)) {
            all_simple = false;
        }

        param_specs.push(Param {
            arg_type,
            arg_label: label_noname,
        });
    }

    // OCaml's ffi_bs_aux: if all args are {Nothing, Arg_empty}, use ParamNumber(n)
    // Otherwise use Params(list)
    let params = if all_simple {
        Params::ParamNumber(arity as i64)
    } else {
        Params::Params(param_specs)
    };

    (params, arity)
}

/// Determine the arg type for a non-labeled argument type.
/// Mirrors OCaml's refine_arg_type / spec_of_ptyp.
fn refine_arg_type(nolabel: bool, typ: &CoreType, arena: &mut ParseArena) -> Attr {
    // For Ptyp_any with @as attribute, handle constant args
    if matches!(&typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
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

/// Extract @as("string") from attributes.
/// Mirrors OCaml's iter_process_bs_string_as.
fn get_as_string_attr(attrs: &[Attribute], arena: &ParseArena) -> Option<String> {
    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        if name == "as" {
            // Try to get string payload
            if let Payload::PStr(items) = payload {
                if items.len() == 1 {
                    if let StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc {
                        if let ExpressionDesc::Pexp_constant(Constant::String(s, _)) = &expr.pexp_desc {
                            return Some(s.clone());
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
            if let Payload::PStr(items) = payload {
                if items.len() == 1 {
                    if let StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc {
                        if let ExpressionDesc::Pexp_constant(Constant::Integer(s, suffix)) = &expr.pexp_desc {
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
    None
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
                    None => tag.clone(),
                };

                result.push((tag.clone(), value));
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
fn map_row_fields_into_ints(
    row_fields: &[RowField],
    arena: &ParseArena,
) -> Vec<(String, i64)> {
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

                result.push((tag.clone(), value));
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
            if let CoreTypeDesc::Ptyp_variant(row_fields, current::ClosedFlag::Closed, None) = &typ.ptyp_desc {
                let (has_as, descr) = map_row_fields_into_strings(row_fields, arena);

                // Check if any tags are non-nullary (have payloads)
                let has_payload = row_fields.iter().any(|rf| {
                    matches!(rf, RowField::Rtag(_, _, false, types) if !types.is_empty())
                });

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
            if let CoreTypeDesc::Ptyp_variant(row_fields, current::ClosedFlag::Closed, None) = &typ.ptyp_desc {
                let int_list = map_row_fields_into_ints(row_fields, arena);
                return Attr::Int(int_list);
            }
            // Invalid @int usage
            Attr::Nothing
        }
        Some("ignore") => Attr::Ignore,
        Some("unwrap") => {
            // @unwrap: must be applied to a closed polyvariant where each tag has exactly one payload
            if let CoreTypeDesc::Ptyp_variant(row_fields, current::ClosedFlag::Closed, _) = &typ.ptyp_desc {
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
                CoreTypeDesc::Ptyp_constr(lid, args) if args.is_empty() => {
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
fn is_unit_type(typ: &CoreType, arena: &mut ParseArena) -> bool {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(lid, args) => {
            args.is_empty() && {
                let longident = arena.get_longident(lid.txt);
                matches!(longident, Longident::Lident(s) if arena.get_string(*s) == "unit")
            }
        }
        _ => false,
    }
}

/// Get the result type of an arrow type
fn get_result_type(typ: &CoreType) -> Option<&CoreType> {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow { ret, .. } => Some(ret.as_ref()),
        _ => None,
    }
}

/// Get the innermost result type (following all arrows)
fn get_final_result_type(typ: &CoreType) -> &CoreType {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow { ret, .. } => get_final_result_type(ret),
        _ => typ,
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
fn list_of_arrow<'a>(typ: &'a CoreType, arena: &ParseArena) -> (Vec<&'a TypeArg>, &'a CoreType) {
    let mut args = Vec::new();
    let mut current = typ;
    loop {
        match &current.ptyp_desc {
            CoreTypeDesc::Ptyp_arrow { arg, ret, arity } => {
                let arity_val = arena.get_arity(*arity);
                // OCaml: arity = None || acc = []
                if arity_val.is_none() || args.is_empty() {
                    args.push(arg.as_ref());
                    current = ret.as_ref();
                } else {
                    // Has arity (Some n) and not the first arg → stop
                    break;
                }
            }
            _ => break,
        }
    }
    (args, current)
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
        let arg_type = refine_arg_type(nolabel, &arg.typ, arena);
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
            ptyp_desc: CoreTypeDesc::Ptyp_constr(
                Located { txt: unit_lid, loc: loc },
                vec![],
            ),
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
        let arity = arena.push_arity(Some(1));
        let unit_arg = TypeArg {
            attrs: vec![],
            lbl: ArgLabel::Nolabel,
            typ: unit_type,
        };
        return CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow {
                arg: Box::new(unit_arg),
                ret: Box::new(result.clone()),
                arity,
            },
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }

    // Rebuild the arrow chain from right to left, like OCaml's Typ.arrows
    let arity_count = filtered_args.len();
    let outermost_arity = arena.push_arity(Some(arity_count as i32));

    // Build from the last arg backwards
    let mut current = result.clone();
    for (i, arg) in filtered_args.iter().enumerate().rev() {
        let arity = if i == 0 {
            outermost_arity
        } else {
            // Inner arrows get arity = None (fresh push like OCaml)
            arena.push_arity(None)
        };
        current = CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow {
                arg: Box::new((*arg).clone()),
                ret: Box::new(current),
                arity,
            },
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }
    current
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
    let result_is_any = matches!(&result.ptyp_desc, CoreTypeDesc::Ptyp_any);

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
                let field_name = get_as_string_attr(&arg.attrs, arena)
                    .unwrap_or_else(|| label_name.clone());

                let arg_type = refine_arg_type(false, &arg.typ, arena);

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
                            Located { txt: arena.push_string(field_name.clone()), loc: loc },
                            vec![],
                            arg.typ.clone(),
                        ));
                    }
                    Attr::Int(_) => {
                        // @int polyvariant: add to result_types with int type
                        filtered_args.push(arg);
                        let int_lid = arena.push_lident_static("int");
                        let int_type = CoreType {
                            ptyp_desc: CoreTypeDesc::Ptyp_constr(
                                Located { txt: int_lid, loc },
                                vec![],
                            ),
                            ptyp_loc: loc,
                            ptyp_attributes: vec![],
                        };
                        result_types.push(ObjectField::Otag(
                            Located { txt: arena.push_string(field_name.clone()), loc: loc },
                            vec![],
                            int_type,
                        ));
                    }
                    Attr::PolyVarString { .. } => {
                        // @string polyvariant: add to result_types with string type
                        filtered_args.push(arg);
                        let string_lid = arena.push_lident_static("string");
                        let string_type = CoreType {
                            ptyp_desc: CoreTypeDesc::Ptyp_constr(
                                Located { txt: string_lid, loc },
                                vec![],
                            ),
                            ptyp_loc: loc,
                            ptyp_attributes: vec![],
                        };
                        result_types.push(ObjectField::Otag(
                            Located { txt: arena.push_string(field_name.clone()), loc: loc },
                            vec![],
                            string_type,
                        ));
                    }
                    Attr::PolyVar { .. } | Attr::Unwrap | Attr::ExternUnit => {
                        // These are errors in OCaml but we'll just add the original type
                        filtered_args.push(arg);
                        result_types.push(ObjectField::Otag(
                            Located { txt: arena.push_string(field_name.clone()), loc: loc },
                            vec![],
                            arg.typ.clone(),
                        ));
                    }
                }
            }
            ArgLabel::Optional(label_loc) => {
                // Optional args: add to result_types with Js.undefined wrapper
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name = get_as_string_attr(&arg.attrs, arena)
                    .unwrap_or_else(|| label_name.clone());

                let arg_type = get_opt_arg_type(false, &arg.typ, arena);

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
                        let wrapped_type = to_undefined_type(&arg.typ, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located { txt: arena.push_string(field_name.clone()), loc: loc },
                            vec![],
                            wrapped_type,
                        ));
                    }
                    Attr::Int(_) => {
                        // @int optional: wrap int in Js.undefined
                        filtered_args.push(arg);
                        let int_lid = arena.push_lident_static("int");
                        let int_type = CoreType {
                            ptyp_desc: CoreTypeDesc::Ptyp_constr(
                                Located { txt: int_lid, loc },
                                vec![],
                            ),
                            ptyp_loc: loc,
                            ptyp_attributes: vec![],
                        };
                        let wrapped_type = to_undefined_type(&int_type, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located { txt: arena.push_string(field_name.clone()), loc: loc },
                            vec![],
                            wrapped_type,
                        ));
                    }
                    Attr::PolyVarString { .. } => {
                        // @string optional: wrap string in Js.undefined
                        filtered_args.push(arg);
                        let string_lid = arena.push_lident_static("string");
                        let string_type = CoreType {
                            ptyp_desc: CoreTypeDesc::Ptyp_constr(
                                Located { txt: string_lid, loc },
                                vec![],
                            ),
                            ptyp_loc: loc,
                            ptyp_attributes: vec![],
                        };
                        let wrapped_type = to_undefined_type(&string_type, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located { txt: arena.push_string(field_name.clone()), loc: loc },
                            vec![],
                            wrapped_type,
                        ));
                    }
                    _ => {
                        // Other types: add with undefined wrapper
                        filtered_args.push(arg);
                        let wrapped_type = to_undefined_type(&arg.typ, loc, arena);
                        result_types.push(ObjectField::Otag(
                            Located { txt: arena.push_string(field_name.clone()), loc: loc },
                            vec![],
                            wrapped_type,
                        ));
                    }
                }
            }
        }
    }

    // If result type is Ptyp_any, build Ptyp_object from result_types
    let final_result = if result_is_any && !result_types.is_empty() {
        CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_object(result_types, current::ClosedFlag::Closed),
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        }
    } else {
        result.clone()
    };

    // Rebuild the arrow chain
    if filtered_args.is_empty() {
        return final_result;
    }

    let arity_count = filtered_args.len();
    let outermost_arity = arena.push_arity(Some(arity_count as i32));

    let mut current = final_result;
    for (i, arg) in filtered_args.iter().enumerate().rev() {
        let arity = if i == 0 {
            outermost_arity
        } else {
            arena.push_arity(None)
        };
        current = CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow {
                arg: Box::new((*arg).clone()),
                ret: Box::new(current),
                arity,
            },
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }
    current
}

/// Get optional arg type (for Optional labels).
/// Mirrors OCaml's get_opt_arg_type.
fn get_opt_arg_type(_nolabel: bool, typ: &CoreType, arena: &ParseArena) -> Attr {
    // Check for special attributes
    let attr_type = check_type_ffi_attrs(typ, arena);
    match attr_type {
        Some("ignore") => Attr::Ignore,
        Some("int") => {
            if let CoreTypeDesc::Ptyp_variant(row_fields, current::ClosedFlag::Closed, None) = &typ.ptyp_desc {
                let int_list = map_row_fields_into_ints(row_fields, arena);
                return Attr::Int(int_list);
            }
            Attr::Nothing
        }
        Some("string") => {
            if let CoreTypeDesc::Ptyp_variant(row_fields, current::ClosedFlag::Closed, None) = &typ.ptyp_desc {
                let (has_as, descr) = map_row_fields_into_strings(row_fields, arena);
                if has_as {
                    return Attr::PolyVarString { descr };
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
        ptyp_desc: CoreTypeDesc::Ptyp_constr(
            Located { txt: longident, loc },
            vec![typ.clone()],
        ),
        ptyp_loc: loc,
        ptyp_attributes: vec![],
    }
}

/// Parse external attributes to determine FFI encoding details
#[derive(Debug)]
struct ExternalDesc {
    val_name: Option<String>,
    module_as_val: bool,           // @module with no payload
    external_module_name: Option<String>,  // @module("name") with string payload
    module_bind_name: Option<String>,      // @module("name", "bind") second string
    call_name: Option<String>,
    send_name: Option<String>,
    new_name: Option<String>,
    get_name: Option<String>,
    set_name: Option<String>,
    get_index: bool,
    set_index: bool,
    splice: bool,
    tagged_template: bool,
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
            call_name: None,
            send_name: None,
            new_name: None,
            get_name: None,
            set_name: None,
            get_index: false,
            set_index: false,
            splice: false,
            tagged_template: false,
            scopes: Vec::new(),
            return_wrapper: ReturnWrapper::ReturnUnset,
            mk_obj: false,
        }
    }
}

fn parse_external_attrs(attrs: &[Attribute], prim_name: &str, no_arguments: bool, arena: &mut ParseArena) -> ExternalDesc {
    let mut desc = ExternalDesc::default();

    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        match name {
            "val" => {
                let name = get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string());
                if no_arguments {
                    desc.val_name = Some(name);
                } else {
                    desc.call_name = Some(name);
                }
            }
            "module" => {
                let strings = get_payload_strings(payload, arena);
                match strings.len() {
                    0 => {
                        // @module with no payload - module_as_val, bundle = prim_name
                        desc.module_as_val = true;
                    }
                    1 => {
                        // @module("name") - sets external_module_name
                        desc.external_module_name = Some(strings[0].clone());
                    }
                    2 => {
                        // @module("bundle", "bind_name") - sets external_module_name with bind name
                        desc.external_module_name = Some(strings[0].clone());
                        desc.module_bind_name = Some(strings[1].clone());
                    }
                    _ => {}
                }
            }
            "send" => {
                desc.send_name = Some(get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()));
            }
            "new" => {
                desc.new_name = Some(get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()));
            }
            "get" => {
                desc.get_name = Some(get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()));
            }
            "set" => {
                desc.set_name = Some(get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()));
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
            "taggedTemplate" => {
                desc.splice = true;
                desc.tagged_template = true;
            }
            "scope" => {
                let scopes = get_payload_strings(payload, arena);
                if !scopes.is_empty() {
                    desc.scopes = scopes;
                }
            }
            "return" => {
                if let Some(wrapper_str) = get_payload_string(payload, arena) {
                    desc.return_wrapper = match wrapper_str.as_str() {
                        "null_to_opt" => ReturnWrapper::ReturnNullToOpt,
                        "nullable" | "null_undefined_to_opt" => ReturnWrapper::ReturnNullUndefinedToOpt,
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
fn get_payload_string(payload: &current::Payload, arena: &mut ParseArena) -> Option<String> {
    match payload {
        current::Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc {
                match &expr.pexp_desc {
                    ExpressionDesc::Pexp_constant(current::Constant::String(s, _)) => {
                        return Some(s.clone());
                    }
                    // Handle @attr(ident) where ident is a simple identifier like nullable
                    ExpressionDesc::Pexp_ident(lid) => {
                        let longident = arena.get_longident(lid.txt);
                        if let Longident::Lident(s) = longident {
                            return Some(arena.get_string(*s).to_string());
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

/// Extract integer from attribute payload (mirrors OCaml's Ast_payload.is_single_int)
fn get_payload_int(payload: &current::Payload, arena: &mut ParseArena) -> Option<i32> {
    match payload {
        current::Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc {
                if let ExpressionDesc::Pexp_constant(current::Constant::Integer(name, suffix)) = &expr.pexp_desc {
                    // OCaml's is_single_int rejects 'n' suffix (bigint)
                    if matches!(suffix, Some('n')) {
                        return None;
                    }
                    return name.parse::<i32>().ok();
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract string with delimiter from attribute payload.
/// Mirrors OCaml's string extraction in iter_process_bs_string_or_int_as,
/// including the parse_processed_delim logic that converts raw string delimiters
/// to FFI Delim values.
///
/// The OCaml PPX pipeline rewrites all plain string delimiters (None → Some "*j")
/// before external processing, so we need to apply the same transformation here.
fn get_payload_string_with_delim(payload: &current::Payload, arena: &mut ParseArena) -> Option<(String, Delim)> {
    match payload {
        current::Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc {
                if let ExpressionDesc::Pexp_constant(current::Constant::String(s, raw_delim)) = &expr.pexp_desc {
                    // Apply parse_processed_delim logic:
                    // In OCaml, strings get rewritten: None → "*j", then
                    // parse_processed_delim maps: None→DNone, "*j"→DStarJ, "json"→DNoQuotes, "bq"→DBackQuotes
                    // Rust parser uses "js" for plain strings (equivalent to OCaml's None → "*j" rewrite)
                    let delim = match raw_delim.as_deref() {
                        None => Delim::DStarJ,        // None → rewritten to "*j" → DStarJ
                        Some("js") => Delim::DStarJ,  // Rust parser's plain string delimiter
                        Some("*j") => Delim::DStarJ,  // Already rewritten (OCaml format)
                        Some("json") => Delim::DNoQuotes,
                        Some("bq") => Delim::DBackQuotes,
                        Some("j") => Delim::DStarJ,   // "j" delimiter → DStarJ
                        _ => return None,              // Unrecognized delimiter
                    };
                    return Some((s.clone(), delim));
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract multiple strings from attribute payload (mirrors OCaml's Ast_payload.assert_strings)
/// Handles: @attr("str"), @attr(("str1", "str2", ...)), @attr (empty → [])
fn get_payload_strings(payload: &current::Payload, arena: &mut ParseArena) -> Vec<String> {
    match payload {
        current::Payload::PStr(items) if items.is_empty() => vec![],
        current::Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc {
                match &expr.pexp_desc {
                    ExpressionDesc::Pexp_constant(current::Constant::String(s, _)) => {
                        return vec![s.clone()];
                    }
                    ExpressionDesc::Pexp_tuple(exprs) => {
                        let mut result = Vec::new();
                        for e in exprs {
                            if let ExpressionDesc::Pexp_constant(current::Constant::String(s, _)) = &e.pexp_desc {
                                result.push(s.clone());
                            }
                        }
                        if result.len() == exprs.len() {
                            return result;
                        }
                    }
                    ExpressionDesc::Pexp_ident(lid) => {
                        let longident = arena.get_longident(lid.txt);
                        if let Longident::Lident(s) = longident {
                            return vec![arena.get_string(*s).to_string()];
                        }
                    }
                    _ => {}
                }
            }
            vec![]
        }
        _ => vec![],
    }
}

/// Build FFI type from external description and type info
fn build_ffi_type(desc: &ExternalDesc, prim_name: &str, arity: usize, result_is_unit: bool, params: Params) -> FfiType {
    // Determine return wrapper
    let return_wrapper = if result_is_unit && matches!(desc.return_wrapper, ReturnWrapper::ReturnUnset) {
        ReturnWrapper::ReturnReplacedWithUnit
    } else {
        desc.return_wrapper.clone()
    };

    // Build ExternalModuleName from desc.external_module_name if present
    // (this is @module("name") or @module("name", "bind") with string payload)
    let external_module_name = desc.external_module_name.as_ref().map(|bundle| ExternalModuleName {
        bundle: bundle.clone(),
        module_bind_name: match &desc.module_bind_name {
            Some(name) => ModuleBindName::PhintName(name.clone()),
            None => ModuleBindName::PhintNothing,
        },
        import_attributes: None,
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
                tagged_template: desc.tagged_template,
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
                tagged_template: desc.tagged_template,
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
            tagged_template: desc.tagged_template,
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
        Some(name) => name.as_str(),
        None => return false,
    };
    if !is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return false;
    }
    let (params, arity) = build_arg_type_specs(&vd.pval_type, arena);
    let (args, _) = list_of_arrow(&vd.pval_type, arena);
    let no_arguments = args.is_empty();
    let desc = parse_external_attrs(&vd.pval_attributes, prim_name, no_arguments, arena);
    let result_is_unit = is_unit_type(get_final_result_type(&vd.pval_type), arena);
    let ffi = build_ffi_type(&desc, prim_name, arity, result_is_unit, params);
    check_ffi_relative(&ffi)
}

/// Check if a path string is a package-relative path (starts with "./" or "../").
fn is_package_relative_path(s: &str) -> bool {
    s.starts_with("./") || s.starts_with("../")
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
    pub pval_prim: Vec<String>,
    pub pval_attributes: Vec<Attribute>,
}

/// Filter out ReScript FFI attributes (they're consumed by encoding)
fn filter_ffi_attributes(attrs: &[Attribute], arena: &mut ParseArena) -> Vec<Attribute> {
    attrs
        .iter()
        .filter(|(attr_name, _payload)| {
            let name = arena.get_string(attr_name.txt);
            !EXTERNAL_ATTRS.iter().any(|&ext_attr| name == ext_attr)
        })
        .cloned()
        .collect()
}

/// Encode external value description with FFI metadata
pub fn encode_external(vd: &ValueDescription, arena: &mut ParseArena) -> EncodedExternal {
    // Get the primitive name
    let prim_name = match vd.pval_prim.first() {
        Some(name) => name.as_str(),
        None => return EncodedExternal {
            pval_prim: vd.pval_prim.clone(),
            pval_attributes: vd.pval_attributes.clone(),
        },
    };

    // Check if this is a ReScript external
    if !is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
        return EncodedExternal {
            pval_prim: vd.pval_prim.clone(),
            pval_attributes: vd.pval_attributes.clone(),
        };
    }

    // Build arg type specs (mirrors OCaml's fold_right in handle_attributes)
    // Must compute before parse_external_attrs because @val behavior depends on no_arguments
    let (params, arity) = build_arg_type_specs(&vd.pval_type, arena);
    // no_arguments = arg_types_ty = [] in OCaml: checks if there are ANY arrow args,
    // regardless of ignored. Use list_of_arrow directly.
    let (args, _) = list_of_arrow(&vd.pval_type, arena);
    let no_arguments = args.is_empty();

    // Parse attributes
    let desc = parse_external_attrs(&vd.pval_attributes, prim_name, no_arguments, arena);

    // Check if result is unit
    let result_is_unit = is_unit_type(get_final_result_type(&vd.pval_type), arena);

    // Build FFI type
    let ffi = if desc.mk_obj {
        // @obj external: build FfiObjCreate with field names
        build_obj_ffi_type(&vd.pval_type, arena)
    } else {
        build_ffi_type(&desc, prim_name, arity, result_is_unit, params)
    };

    // Encode FFI type
    let encoded = encode_ffi_type(&ffi);

    // Filter out consumed FFI attributes
    let filtered_attrs = filter_ffi_attributes(&vd.pval_attributes, arena);

    EncodedExternal {
        pval_prim: vec![prim_name.to_string(), encoded],
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
                // Nolabel in @obj: only unit allowed, mark as empty kind
                // Skip from obj_params (unit args don't contribute to object)
            }
            ArgLabel::Labelled(label_loc) => {
                let label_name = arena.get_string(label_loc.txt).to_string();
                let field_name = get_as_string_attr(&arg.attrs, arena)
                    .unwrap_or_else(|| label_name.clone());

                let arg_type = refine_arg_type(false, &arg.typ, arena);

                match arg_type {
                    Attr::Ignore => {
                        // @ignore: empty_kind, skip from result
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
                let field_name = get_as_string_attr(&arg.attrs, arena)
                    .unwrap_or_else(|| label_name.clone());

                let arg_type = get_opt_arg_type(false, &arg.typ, arena);

                match arg_type {
                    Attr::Ignore => {
                        // @ignore: empty_kind, skip from result
                    }
                    Attr::Nothing => {
                        // Check if for_sure_no_nested_option
                        let for_sure_not_nested = match &arg.typ.ptyp_desc {
                            CoreTypeDesc::Ptyp_constr(lid, args) if args.is_empty() => {
                                let longident = arena.get_longident(lid.txt);
                                if let Longident::Lident(s) = longident {
                                    let name = arena.get_string(*s);
                                    // is_builtin_rank0_type
                                    matches!(name, "int" | "float" | "string" | "bool" | "unit" | "exn")
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
pub fn inline_string_primitive(s: &str, delim: Option<&str>) -> Vec<String> {
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

    vec![String::new(), encoded]
}

/// Encode inline bool constant
pub fn inline_bool_primitive(b: bool) -> Vec<String> {
    let constant = if b {
        LamConstant::ConstJsTrue
    } else {
        LamConstant::ConstJsFalse
    };

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![String::new(), encoded]
}

/// Encode inline int constant
pub fn inline_int_primitive(i: i32) -> Vec<String> {
    let constant = LamConstant::ConstInt {
        i,
        comment: PointerInfo::None,
    };

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![String::new(), encoded]
}

/// Encode inline float constant
pub fn inline_float_primitive(f: &str) -> Vec<String> {
    let constant = LamConstant::ConstFloat(f.to_string());

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![String::new(), encoded]
}

/// Encode inline bigint constant
pub fn inline_bigint_primitive(s: &str) -> Vec<String> {
    // Parse bigint: handle optional - sign
    let (negative, digits) = if let Some(stripped) = s.strip_prefix('-') {
        (true, stripped.to_string())
    } else {
        (false, s.to_string())
    };

    let constant = LamConstant::ConstBigint(negative, digits);

    let ffi = FfiType::FfiInlineConst(constant);
    let encoded = encode_ffi_type(&ffi);

    vec![String::new(), encoded]
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
    attrs: &'a [Attribute],
    arena: &ParseArena,
) -> Option<&'a Expression> {
    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        if name == "inline" {
            // @inline(expr) has PStr with a single Pstr_eval
            if let Payload::PStr(items) = payload {
                if items.len() == 1 {
                    if let StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc {
                        return Some(expr);
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
    let expr = find_inline_payload_expr(&vd.pval_attributes, arena)?;

    match &expr.pexp_desc {
        // @inline("string") let x: t
        ExpressionDesc::Pexp_constant(Constant::String(s, delim)) => {
            let prim = inline_string_primitive(s, delim.as_deref());
            Some(ValueDescription {
                pval_name: vd.pval_name.clone(),
                pval_type: vd.pval_type.clone(),
                pval_prim: prim,
                pval_attributes: vec![], // Clear attributes
                pval_loc: vd.pval_loc,
            })
        }
        // @inline(42) let x: t
        ExpressionDesc::Pexp_constant(Constant::Integer(s, None)) => {
            let i = s.parse::<i32>().ok()?;
            let prim = inline_int_primitive(i);
            Some(ValueDescription {
                pval_name: vd.pval_name.clone(),
                pval_type: vd.pval_type.clone(),
                pval_prim: prim,
                pval_attributes: vec![], // Clear attributes
                pval_loc: vd.pval_loc,
            })
        }
        // @inline(42n) let x: t (bigint)
        ExpressionDesc::Pexp_constant(Constant::Integer(s, Some('n'))) => {
            let prim = inline_bigint_primitive(s);
            Some(ValueDescription {
                pval_name: vd.pval_name.clone(),
                pval_type: vd.pval_type.clone(),
                pval_prim: prim,
                pval_attributes: vec![], // Clear attributes
                pval_loc: vd.pval_loc,
            })
        }
        // @inline(3.14) let x: t
        ExpressionDesc::Pexp_constant(Constant::Float(s, None)) => {
            let prim = inline_float_primitive(s);
            Some(ValueDescription {
                pval_name: vd.pval_name.clone(),
                pval_type: vd.pval_type.clone(),
                pval_prim: prim,
                pval_attributes: vec![], // Clear attributes
                pval_loc: vd.pval_loc,
            })
        }
        // @inline(true) or @inline(false) let x: t
        ExpressionDesc::Pexp_construct(lid, None) => {
            let longident = arena.get_longident(lid.txt);
            if let Longident::Lident(name_idx) = longident {
                let name = arena.get_string(*name_idx);
                if name == "true" || name == "false" {
                    let prim = inline_bool_primitive(name == "true");
                    return Some(ValueDescription {
                        pval_name: vd.pval_name.clone(),
                        pval_type: vd.pval_type.clone(),
                        pval_prim: prim,
                        pval_attributes: vec![], // Clear attributes
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
    let lid_idx = arena.push_lident_static(type_name);
    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr(
            Located { txt: lid_idx, loc: none_loc },
            vec![],
        ),
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
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
    match &expr.pexp_desc {
        // @inline let x = "string"
        ExpressionDesc::Pexp_constant(Constant::String(s, delim)) => {
            let prim = inline_string_primitive(s, delim.as_deref());
            Some(StructureItem {
                pstr_desc: StructureItemDesc::Pstr_primitive(ValueDescription {
                    pval_name: Located {
                        txt: pval_name.txt,
                        loc: pval_name.loc,
                    },
                    pval_type: make_simple_type("string", arena),
                    pval_prim: prim,
                    pval_attributes: vec![],
                    pval_loc: pvb_loc,
                }),
                pstr_loc,
            })
        }
        // @inline let x = 42
        ExpressionDesc::Pexp_constant(Constant::Integer(s, None)) => {
            let i = s.parse::<i32>().ok()?;
            let prim = inline_int_primitive(i);
            Some(StructureItem {
                pstr_desc: StructureItemDesc::Pstr_primitive(ValueDescription {
                    pval_name: Located {
                        txt: pval_name.txt,
                        loc: pval_name.loc,
                    },
                    pval_type: make_simple_type("int", arena),
                    pval_prim: prim,
                    pval_attributes: vec![],
                    pval_loc: pvb_loc,
                }),
                pstr_loc,
            })
        }
        // @inline let x = 3.14
        ExpressionDesc::Pexp_constant(Constant::Float(s, None)) => {
            let prim = inline_float_primitive(s);
            Some(StructureItem {
                pstr_desc: StructureItemDesc::Pstr_primitive(ValueDescription {
                    pval_name: Located {
                        txt: pval_name.txt,
                        loc: pval_name.loc,
                    },
                    pval_type: make_simple_type("float", arena),
                    pval_prim: prim,
                    pval_attributes: vec![],
                    pval_loc: pvb_loc,
                }),
                pstr_loc,
            })
        }
        // @inline let x = true or @inline let x = false
        ExpressionDesc::Pexp_construct(lid, None) => {
            let longident = arena.get_longident(lid.txt);
            if let Longident::Lident(name_idx) = longident {
                let name = arena.get_string(*name_idx);
                if name == "true" || name == "false" {
                    let prim = inline_bool_primitive(name == "true");
                    return Some(StructureItem {
                        pstr_desc: StructureItemDesc::Pstr_primitive(ValueDescription {
                            pval_name: Located {
                                txt: pval_name.txt,
                                loc: pval_name.loc,
                            },
                            pval_type: make_simple_type("bool", arena),
                            pval_prim: prim,
                            pval_attributes: vec![],
                            pval_loc: pvb_loc,
                        }),
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
        "raw" => handle_raw(expr, payload, arena, "#raw_expr", ext_loc),
        "re" => handle_re(expr, payload, arena, ext_loc),
        "external" => handle_external_ext(expr, payload, arena, ext_loc),
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
fn handle_obj(
    expr: &Expression,
    payload: &Payload,
    arena: &mut ParseArena,
) -> Expression {
    // Extract the record expression from the payload: PStr [{ Pstr_eval(Pexp_record(...), _) }]
    let (record_expr, label_exprs) = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(e, _) = &items[0].pstr_desc {
                if let ExpressionDesc::Pexp_record(fields, None) = &e.pexp_desc {
                    (e, fields)
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
    let loc = record_expr.pexp_loc;
    let none_loc = arena.none_loc();

    // Extract labels and rewritten expressions from the record fields.
    // OCaml: Ext_list.fold_right label_exprs ([], [], 0) (fun {lid={txt;loc}; x=e} ...)
    // Only Lident fields are valid.
    let mut labels: Vec<(StrIdx, LocIdx)> = Vec::with_capacity(label_exprs.len());
    let mut args: Vec<(StrIdx, Expression)> = Vec::with_capacity(label_exprs.len());
    let arity = label_exprs.len();

    for field in label_exprs {
        let lid = arena.get_longident(field.lid.txt);
        match lid {
            Longident::Lident(s) => {
                let str_idx = *s;
                let field_loc = field.lid.loc;
                labels.push((str_idx, field_loc));
                // Recursively rewrite the field expression (OCaml: self.expr self e)
                let rewritten_expr = rewrite_expression(&field.expr, arena);
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
    let pval_prim = vec!["".to_string(), encoded];

    // === Build pval_type: (~a: 'a0, ~b: 'a1) => {"a": 'a0, "b": 'a1} ===
    // OCaml: from_labels ~loc arity labels

    // Create type variables 'a0, 'a1, ...
    let tyvars: Vec<CoreType> = (0..arity)
        .map(|i| CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_var(format!("a{}", i)),
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        })
        .collect();

    // Create object type: {"a": 'a0, "b": 'a1}
    let obj_fields: Vec<current::ObjectField> = labels
        .iter()
        .zip(tyvars.iter())
        .map(|((str_idx, label_loc), tyvar)| {
            current::ObjectField::Otag(
                Located { txt: *str_idx, loc: *label_loc },
                vec![],
                tyvar.clone(),
            )
        })
        .collect();

    let result_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_object(obj_fields, current::ClosedFlag::Closed),
        ptyp_loc: loc,
        ptyp_attributes: vec![],
    };

    // Create arrow type args: [~a: 'a0, ~b: 'a1]
    // OCaml: Ext_list.map2 labels tyvars (fun label tyvar -> {attrs=[]; lbl=Labelled label; typ=tyvar})
    let type_args: Vec<TypeArg> = labels
        .iter()
        .zip(tyvars.iter())
        .map(|((str_idx, label_loc), tyvar)| TypeArg {
            attrs: vec![],
            lbl: ArgLabel::Labelled(Located {
                txt: *str_idx,
                loc: *label_loc,
            }),
            typ: tyvar.clone(),
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
        pval_type,
        pval_prim,
        pval_attributes: vec![],
        pval_loc: loc,
    };

    let mod_structure = vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_primitive(vd),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(mod_structure),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    // === Create the function application: J.unsafe_expr(~a=e1, ~b=e2) ===
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    let func_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: j_unsafe_expr, loc }),
        pexp_loc: loc,
        pexp_attributes: vec![],
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
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(func_ident),
            args: apply_args,
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // The final result: {e with pexp_desc = Pexp_letmodule(...)}
    // where e is the record expression, so pexp_loc = record's loc and pexp_attributes = record's attrs
    Expression {
        pexp_desc: ExpressionDesc::Pexp_letmodule(
            Located {
                txt: module_name_idx,
                loc,
            },
            mod_expr,
            Box::new(apply_expr),
        ),
        pexp_loc: record_expr.pexp_loc,
        pexp_attributes: record_expr.pexp_attributes.clone(),
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

    let total_arity = args.len() as i32;

    // Build right-to-left: last arg wraps result first
    let mut current = result;
    for (i, arg) in args.into_iter().enumerate().collect::<Vec<_>>().into_iter().rev() {
        let arity = if i == 0 {
            // Outermost arrow gets Some(total_arity)
            arena.push_arity(Some(total_arity))
        } else {
            // Inner arrows get None
            arena.push_arity(None)
        };
        current = CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow {
                arg: Box::new(arg),
                ret: Box::new(current),
                arity,
            },
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }
    current
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
    if let Payload::PStr(items) = payload {
        if !items.is_empty() {
            return expr.clone(); // Error case - return unchanged
        }
    } else {
        return expr.clone();
    }

    // OCaml: loc comes from the extension identifier's location ({txt; loc} pattern)
    let loc = ext_loc;
    let none_loc = arena.none_loc();

    // Create the type: _ -> unit
    let any_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_any,
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
    };

    // Create "unit" type
    let unit_ident = arena.push_lident_static("unit");
    let unit_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr(
            Located { txt: unit_ident, loc: none_loc },
            vec![],
        ),
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
    };

    let pval_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow {
            arg: Box::new(TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type,
            }),
            ret: Box::new(unit_type),
            arity: arena.static_arity_1(),  // OCaml's CSE shares all literal Some(1) values
        },
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
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
        pval_type,
        pval_prim: vec!["%debugger".to_string()],
        pval_attributes: vec![],
        pval_loc: loc,
    };

    // Create the module structure
    let mod_structure = vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_primitive(vd),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(mod_structure),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    // Create the longident J.unsafe_expr
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    // Create the unit literal: ()
    let unit_construct = arena.push_lident_static("()");
    let unit_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_construct(
            Located { txt: unit_construct, loc },
            None,
        ),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create the function application: J.unsafe_expr(())
    let func_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: j_unsafe_expr, loc }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    let apply_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(func_ident),
            args: vec![(ArgLabel::Nolabel, unit_expr)],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create the final expression: let module J = struct ... end in J.unsafe_expr(())
    Expression {
        pexp_desc: ExpressionDesc::Pexp_letmodule(
            Located {
                txt: module_name_idx,
                loc,
            },
            mod_expr,
            Box::new(apply_expr),
        ),
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
fn handle_re(expr: &Expression, payload: &Payload, arena: &mut ParseArena, ext_loc: LocIdx) -> Expression {
    // OCaml: loc comes from the extension identifier's location ({txt; loc} pattern)
    let loc = ext_loc;

    // First, handle it like %raw to get the letmodule expression
    let raw_expr = handle_raw(expr, payload, arena, "#raw_expr", ext_loc);

    // Create the type: Stdlib_RegExp.t
    // This is Longident.Ldot(Lident "Stdlib_RegExp", "t")
    // OCaml uses `loc` for both ptyp_loc and the Located.loc:
    //   Typ.constr ~loc {txt = regexp_id; loc} []
    let stdlib_regexp_lident = arena.push_lident_static("Stdlib_RegExp");
    let regexp_t = arena.push_ldot_static(stdlib_regexp_lident, "t");

    let regexp_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr(
            Located {
                txt: regexp_t,
                loc,
            },
            vec![],
        ),
        ptyp_loc: loc,
        ptyp_attributes: vec![],
    };

    // Wrap the raw expression in a type constraint
    Expression {
        pexp_desc: ExpressionDesc::Pexp_constraint(Box::new(raw_expr), regexp_type),
        pexp_loc: loc,
        pexp_attributes: vec![],
    }
}

/// Handle %external extension (DEPRECATED).
///
/// OCaml transforms `%external(name)` into:
/// ```text
/// Js.undefinedToOption(
///   if (Js.typeof(raw_exp(name)) == "undefined") then
///     Js.Undefined.empty
///   else
///     raw_exp(name)
/// )
/// ```
///
/// This is deprecated - users should use %raw or regular FFI syntax instead.
fn handle_external_ext(
    expr: &Expression,
    payload: &Payload,
    arena: &mut ParseArena,
    ext_loc: LocIdx,
) -> Expression {
    use crate::parser::longident::Longident;

    // Extract the identifier from the payload
    // %external expects a single identifier like %external(__DEV__)
    let ident_str = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(e, _) = &items[0].pstr_desc {
                if let ExpressionDesc::Pexp_ident(Located { txt, .. }) = &e.pexp_desc {
                    // Get the Longident and check if it's an Lident
                    let lid = arena.get_longident(*txt);
                    if let Longident::Lident(str_idx) = lid {
                        Some(arena.get_string(*str_idx).to_string())
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

    let ident_str = match ident_str {
        Some(s) => s,
        None => return expr.clone(), // Return unchanged on error
    };

    // OCaml: loc comes from the extension identifier's location ({txt; loc} pattern)
    let loc = ext_loc;
    let none_loc = arena.none_loc();

    // Create the raw expression: handle_raw(ident_str)
    // First, create a string expression for the identifier
    let str_exp = Expression {
        pexp_desc: ExpressionDesc::Pexp_constant(Constant::String(
            ident_str.clone(),
            None,
        )),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create raw_exp as local_external_apply with "#raw_expr"
    let any_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_any,
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
    };

    let pval_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow {
            arg: Box::new(TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type.clone(),
            }),
            ret: Box::new(any_type.clone()),
            arity: arena.static_arity_1(),  // OCaml's CSE shares all literal Some(1) values
        },
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
    };

    // Module name and function names
    let module_name_idx = arena.intern_string("J");
    let func_name_idx = arena.intern_string("unsafe_expr");

    // Create the value description (external primitive)
    let vd = ValueDescription {
        pval_name: Located {
            txt: func_name_idx,
            loc,
        },
        pval_type: pval_type.clone(),
        pval_prim: vec!["#raw_expr".to_string()],
        pval_attributes: vec![],
        pval_loc: loc,
    };

    // Create the module structure
    let mod_structure = vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_primitive(vd),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(mod_structure),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    // Create J.unsafe_expr longident
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    // Create J.unsafe_expr(ident_str)
    let func_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: j_unsafe_expr, loc }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    let apply_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(func_ident.clone()),
            args: vec![(ArgLabel::Nolabel, str_exp.clone())],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create raw_exp = let module J = ... in J.unsafe_expr(str)
    // This is the full letmodule expression that will be used inside Js.typeof and the else branch
    let raw_exp = Expression {
        pexp_desc: ExpressionDesc::Pexp_letmodule(
            Located {
                txt: module_name_idx,
                loc,
            },
            mod_expr,
            Box::new(apply_expr),
        ),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create Js.typeof longident
    let js_lident = arena.push_lident_static("Js");
    let js_typeof = arena.push_ldot_static(js_lident, "typeof");

    // Create Js.typeof(raw_exp)
    let typeof_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: js_typeof, loc }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    let typeof_call = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(typeof_ident),
            args: vec![(ArgLabel::Nolabel, raw_exp.clone())],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create == operator longident
    let eq_lident = arena.push_lident_static("==");

    // Create "undefined" string constant
    let undefined_str = Expression {
        pexp_desc: ExpressionDesc::Pexp_constant(Constant::String(
            "undefined".to_string(),
            None,
        )),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create Js.typeof(raw_exp) == "undefined"
    let eq_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: eq_lident, loc }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    let condition = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(eq_ident),
            args: vec![
                (ArgLabel::Nolabel, typeof_call),
                (ArgLabel::Nolabel, undefined_str),
            ],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create Js.Undefined.empty
    let js_undefined = arena.push_ldot_static(js_lident, "Undefined");
    let js_undefined_empty = arena.push_ldot_static(js_undefined, "empty");

    let empty_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: js_undefined_empty,
            loc,
        }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create the if-then-else: if condition then empty else raw_exp
    let if_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_ifthenelse(
            Box::new(condition),
            Box::new(empty_expr),
            Some(Box::new(raw_exp)),
        ),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create Js.undefinedToOption
    let js_undef_to_opt = arena.push_ldot_static(js_lident, "undefinedToOption");

    let undef_to_opt_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: js_undef_to_opt,
            loc,
        }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create Js.undefinedToOption(if_expr)
    // This is the final result - no additional letmodule wrapping needed
    // because raw_exp already contains the letmodule
    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(undef_to_opt_ident),
            args: vec![(ArgLabel::Nolabel, if_expr)],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: expr.pexp_attributes.clone(),
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
    pval_prim: &str,
    ext_loc: LocIdx,
) -> Expression {
    // Extract the string expression from the payload
    // OCaml's raw_as_string_exp_exn returns {e with pexp_desc = Pexp_constant ...}
    // where e is the original expression from the payload.
    // The returned expression uses e.pexp_loc (the payload string's location).
    // Also detect if the JS string contains a function (for internal.expansive attribute).
    let (str_exp, payload_loc, is_function) = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(e, _) = &items[0].pstr_desc {
                if let ExpressionDesc::Pexp_constant(Constant::String(s, _)) = &e.pexp_desc {
                    // Check if the JS string contains a function
                    let is_func = is_js_function(s);

                    // Create a new string expression with delimiter stripped
                    // (OCaml strips the delimiter when transforming %raw)
                    let exp = Expression {
                        pexp_desc: ExpressionDesc::Pexp_constant(Constant::String(
                            s.clone(),
                            None, // Strip delimiter
                        )),
                        pexp_loc: e.pexp_loc,
                        pexp_attributes: e.pexp_attributes.clone(),
                    };
                    (exp, e.pexp_loc, is_func)
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
        ptyp_desc: CoreTypeDesc::Ptyp_any,
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
    };

    let pval_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow {
            arg: Box::new(TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type.clone(),
            }),
            ret: Box::new(any_type),
            arity: arena.static_arity_1(),  // OCaml's CSE shares all literal Some(1) values
        },
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
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
        pval_type,
        pval_prim: vec![pval_prim.to_string()],
        pval_attributes: vec![],
        pval_loc: loc,
    };

    // Create the module structure: struct external unsafe_expr: _ -> _ = "#raw_expr" end
    let mod_structure = vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_primitive(vd),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(mod_structure),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    // Create the longident J.unsafe_expr
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    // Save attributes before moving str_exp
    let payload_attributes = str_exp.pexp_attributes.clone();

    // Create the function application: J.unsafe_expr("code")
    let func_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: j_unsafe_expr, loc }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    let apply_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(func_ident),
            args: vec![(ArgLabel::Nolabel, str_exp)],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
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
            Payload::PStr(vec![]),
        );
        let mut attrs = vec![internal_expansive];
        attrs.extend(payload_attributes);
        attrs
    } else {
        payload_attributes
    };

    Expression {
        pexp_desc: ExpressionDesc::Pexp_letmodule(
            Located {
                txt: module_name_idx,
                loc,
            },
            mod_expr,
            Box::new(apply_expr),
        ),
        pexp_loc: payload_loc,
        pexp_attributes: final_attributes,
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
    let (str_exp, str_loc) = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(e, _) = &items[0].pstr_desc {
                if let ExpressionDesc::Pexp_constant(Constant::String(s, _)) = &e.pexp_desc {
                    // Create a new string expression with delimiter stripped
                    (
                        Expression {
                            pexp_desc: ExpressionDesc::Pexp_constant(Constant::String(
                                s.clone(),
                                None, // Strip delimiter
                            )),
                            pexp_loc: e.pexp_loc,
                            pexp_attributes: e.pexp_attributes.clone(),
                        },
                        e.pexp_loc,
                    )
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
        ptyp_desc: CoreTypeDesc::Ptyp_any,
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
    };

    let pval_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow {
            arg: Box::new(TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: any_type.clone(),
            }),
            ret: Box::new(any_type),
            arity: arena.static_arity_1(),  // OCaml's CSE shares all literal Some(1) values
        },
        ptyp_loc: none_loc,
        ptyp_attributes: vec![],
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
        pval_type,
        pval_prim: vec!["#raw_stmt".to_string()],
        pval_attributes: vec![],
        pval_loc: loc,
    };

    // Create the module structure
    let mod_structure = vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_primitive(vd),
        pstr_loc: loc,
    }];

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(mod_structure),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    // Create the longident J.unsafe_expr
    let j_lident = arena.push_lident_static("J");
    let j_unsafe_expr = arena.push_ldot_static(j_lident, "unsafe_expr");

    // Create the function application: J.unsafe_expr("code")
    // Save attributes before moving str_exp (for template attribute propagation)
    let payload_attributes = str_exp.pexp_attributes.clone();

    let func_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: j_unsafe_expr, loc }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    let apply_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(func_ident),
            args: vec![(ArgLabel::Nolabel, str_exp)],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    // Create the let module expression
    // Inherit the template attribute from the string expression (res.template)
    let letmodule_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_letmodule(
            Located {
                txt: module_name_idx,
                loc,
            },
            mod_expr,
            Box::new(apply_expr),
        ),
        pexp_loc: str_loc, // Use the string expression's location for outer expr
        pexp_attributes: payload_attributes,
    };

    // Wrap in Pstr_eval - OCaml's Ast_helper.Str.eval uses default_loc (= Location.none)
    // when no ~loc is passed, so we use none_loc here
    StructureItem {
        pstr_desc: StructureItemDesc::Pstr_eval(letmodule_expr, vec![]),
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
) -> Vec<StructureItem> {
    // Extract structure items from payload
    let items = match payload {
        Payload::PStr(items) if !items.is_empty() => items,
        _ => {
            // Invalid payload - just return empty (OCaml would error)
            return vec![];
        }
    };

    // Rewrite the items first (for string transformations etc.)
    let rewritten_items: Vec<StructureItem> = items
        .iter()
        .flat_map(|item| rewrite_structure_item(item, arena))
        .collect();

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
        Payload::PStr(vec![]),
    );

    // Create the module binding:
    // module local_N = { ... } with @internal.local attribute
    let module_binding = current::ModuleBinding {
        pmb_name: Located {
            txt: local_name_idx,
            loc: combined_loc,
        },
        pmb_expr: ModuleExpr {
            pmod_desc: ModuleExprDesc::Pmod_structure(rewritten_items),
            pmod_loc: combined_loc,
            pmod_attributes: vec![],
        },
        pmb_attributes: vec![internal_local_attr],
        pmb_loc: combined_loc,
    };

    let module_item = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_module(module_binding),
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
        popen_attributes: vec![],
    };

    let open_item = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_open(open_desc),
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
    let unsafe_await_lid = arena.push_ldot(promise_lident, "unsafe_await");

    let func_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: unsafe_await_lid, loc: ghost_loc }),
        pexp_loc: ghost_loc,
        pexp_attributes: vec![],
    };

    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(func_ident),
            args: vec![(ArgLabel::Nolabel, inner)],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: ghost_loc,
        pexp_attributes: vec![],
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
    let unsafe_async_lid = arena.push_ldot(promise_lident, "unsafe_async");

    // OCaml uses the same loc object for all three positions
    let func_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located { txt: unsafe_async_lid, loc }),
        pexp_loc: loc,
        pexp_attributes: vec![],
    };

    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(func_ident),
            args: vec![(ArgLabel::Nolabel, inner)],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
    }
}

/// Recursively find the innermost body of nested Pexp_fun and wrap it with unsafe_async.
/// OCaml: ast_async.ml add_promise_to_result
fn add_promise_to_fun_body(expr: &Expression, loc: LocIdx, arena: &mut ParseArena) -> Expression {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_fun {
            arg_label,
            default,
            lhs,
            rhs,
            arity,
            is_async,
        } => {
            // Recurse into rhs to find innermost body
            let new_rhs = add_promise_to_fun_body(rhs, loc, arena);
            Expression {
                pexp_desc: ExpressionDesc::Pexp_fun {
                    arg_label: arg_label.clone(),
                    default: default.clone(),
                    lhs: lhs.clone(),
                    rhs: Box::new(new_rhs),
                    arity: *arity,
                    is_async: *is_async,
                },
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
        pexp_desc: ExpressionDesc::Pexp_pack(cleaned_mod_expr),
        pexp_loc: pmod_loc,
        pexp_attributes: vec![],
    };

    // Create package type: (__ME__, [])
    // The module_type_lid has its own location from the original source
    let package_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_package((
            module_type_lid, // Use the Located<LidentIdx> directly with its location
            vec![], // No with constraints
        )),
        ptyp_loc: pmod_loc,
        ptyp_attributes: vec![],
    };

    // Create constrained expression: (module(ME): __ME__)
    let constrained_pack = Expression {
        pexp_desc: ExpressionDesc::Pexp_constraint(Box::new(pack_expr), package_type),
        pexp_loc: pmod_loc,
        pexp_attributes: vec![],
    };

    // Create Primitive_module.import(constrained_pack)
    let module_str = arena.intern_string("Primitive_module");
    let module_lident = arena.push_lident_from_idx(module_str);
    let import_lid = arena.push_ldot(module_lident, "import");

    let import_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: import_lid,
            loc: pmod_loc,
        }),
        pexp_loc: pmod_loc,
        pexp_attributes: vec![],
    };

    let import_apply = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(import_ident),
            args: vec![(ArgLabel::Nolabel, constrained_pack)],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: pmod_loc,
        pexp_attributes: vec![],
    };

    // Create Primitive_promise.unsafe_await(import_apply)
    let await_expr = transform_await(import_apply, mod_expr.pmod_loc, arena);

    // Create unpack(await_expr)
    // OCaml: {e with pmod_desc = Pmod_unpack ...} - keeps original pmod_attributes (with @res.await)
    current::ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_unpack(Box::new(await_expr)),
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
    match &expr.pexp_desc {
        // Main case: Pexp_letmodule with Pmod_ident and @res.await
        ExpressionDesc::Pexp_letmodule(_, mod_expr, body) => {
            let mut results = Vec::new();

            // Check for Pmod_ident with @res.await
            if let ModuleExprDesc::Pmod_ident(located_lid) = &mod_expr.pmod_desc {
                if has_await_attribute(&mod_expr.pmod_attributes, arena) {
                    let module_type_name = local_module_type_name(located_lid.txt, arena);

                    // Only create if not already in context
                    if !context.contains(&module_type_name) {
                        context.insert(module_type_name.clone());

                        // Create module type declaration:
                        // module type __ME__ = module type of ME
                        let module_type_name_idx = arena.intern_string(&module_type_name);
                        let lid_loc = located_lid.loc;

                        let module_type_decl = StructureItem {
                            pstr_desc: StructureItemDesc::Pstr_modtype(current::ModuleTypeDeclaration {
                                pmtd_name: Located {
                                    txt: module_type_name_idx,
                                    loc: lid_loc,
                                },
                                pmtd_type: Some(current::ModuleType {
                                    pmty_desc: ModuleTypeDesc::Pmty_typeof(Box::new(current::ModuleExpr {
                                        pmod_desc: ModuleExprDesc::Pmod_ident(Located {
                                            txt: located_lid.txt,
                                            loc: lid_loc,
                                        }),
                                        pmod_loc: lid_loc,
                                        // OCaml: Mty.typeof_ ~loc me - uses original `me` which has @res.await
                                        pmod_attributes: mod_expr.pmod_attributes.clone(),
                                    })),
                                    pmty_loc: lid_loc,
                                    pmty_attributes: vec![],
                                }),
                                pmtd_attributes: vec![],
                                pmtd_loc: lid_loc,
                            }),
                            pstr_loc: lid_loc,
                        };

                        results.push(module_type_decl);
                    }
                }
            }

            // Continue spelunking into body
            results.extend(spelunk_expression_for_await_module_types(body, context, arena));
            results
        }

        // Recursively traverse other expression forms (matching OCaml's aux function)
        ExpressionDesc::Pexp_let(_, bindings, body) => {
            let mut results = spelunk_expression_for_await_module_types(body, context, arena);
            for vb in bindings {
                results.extend(spelunk_expression_for_await_module_types(&vb.pvb_expr, context, arena));
            }
            results
        }

        ExpressionDesc::Pexp_ifthenelse(_, then_expr, else_expr) => {
            let mut results = spelunk_expression_for_await_module_types(then_expr, context, arena);
            if let Some(else_e) = else_expr {
                results.extend(spelunk_expression_for_await_module_types(else_e, context, arena));
            }
            results
        }

        ExpressionDesc::Pexp_construct(_, Some(e)) => {
            spelunk_expression_for_await_module_types(e, context, arena)
        }

        ExpressionDesc::Pexp_fun { rhs: body, .. } => {
            spelunk_expression_for_await_module_types(body, context, arena)
        }

        ExpressionDesc::Pexp_newtype(_, body) => {
            spelunk_expression_for_await_module_types(body, context, arena)
        }

        ExpressionDesc::Pexp_constraint(e, _) => {
            spelunk_expression_for_await_module_types(e, context, arena)
        }

        ExpressionDesc::Pexp_match(scrut, cases) => {
            let mut results = spelunk_expression_for_await_module_types(scrut, context, arena);
            for case in cases {
                results.extend(spelunk_expression_for_await_module_types(&case.pc_rhs, context, arena));
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
        results.extend(spelunk_expression_for_await_module_types(&vb.pvb_expr, context, arena));
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
    let mod_expr = &mb.pmb_expr;
    if !has_await_attribute(&mod_expr.pmod_attributes, arena) {
        return None;
    }

    // Get the module identifier and its location
    let (lid, lid_loc) = match &mod_expr.pmod_desc {
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
    let module_type_decl = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_modtype(current::ModuleTypeDeclaration {
            pmtd_name: Located {
                txt: module_type_name_idx,
                loc: lid_loc,
            },
            pmtd_type: Some(current::ModuleType {
                pmty_desc: current::ModuleTypeDesc::Pmty_typeof(Box::new(current::ModuleExpr {
                    pmod_desc: ModuleExprDesc::Pmod_ident(Located {
                        txt: lid,
                        loc: lid_loc,
                    }),
                    pmod_loc: lid_loc,
                    // OCaml: Mty.typeof_ ~loc me - uses original `me` which has @res.await
                    pmod_attributes: mod_expr.pmod_attributes.clone(),
                })),
                pmty_loc: lid_loc,
                pmty_attributes: vec![],
            }),
            pmtd_attributes: vec![],
            pmtd_loc: lid_loc,
        }),
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
        pmod_desc: ModuleExprDesc::Pmod_ident(Located {
            txt: lid,
            loc: lid_loc, // Preserve original Longident location
        }),
        pmod_loc: mod_expr.pmod_loc,
        // Keep attributes as-is to match OCaml's actual behavior (not its intended behavior)
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    };

    // OCaml uses e.pmod_loc for pack, constraint, and package type locations
    let pmod_loc = mod_expr.pmod_loc;

    let pack_expr = Expression {
        pexp_desc: ExpressionDesc::Pexp_pack(cleaned_mod_expr),
        pexp_loc: pmod_loc,
        pexp_attributes: vec![],
    };

    // Create package type: (Lident("__Belt_List__"), [])
    // module_type_lid location is mb.pmb_expr.pmod_loc in OCaml
    let package_type = CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_package((
            Located {
                txt: module_type_lid,
                loc: pmod_loc,
            },
            vec![], // No with constraints
        )),
        ptyp_loc: pmod_loc,
        ptyp_attributes: vec![],
    };

    // Create constrained expression: (module(Belt.List): __Belt_List__)
    let constrained_pack = Expression {
        pexp_desc: ExpressionDesc::Pexp_constraint(Box::new(pack_expr), package_type),
        pexp_loc: pmod_loc,
        pexp_attributes: vec![],
    };

    // Create Primitive_module.import(constrained_pack)
    let module_str = arena.intern_string("Primitive_module");
    let module_lident = arena.push_lident_from_idx(module_str);
    let import_lid = arena.push_ldot(module_lident, "import");

    let import_ident = Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located {
            txt: import_lid,
            loc: pmod_loc,
        }),
        pexp_loc: pmod_loc,
        pexp_attributes: vec![],
    };

    let import_apply = Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(import_ident),
            args: vec![(ArgLabel::Nolabel, constrained_pack)],
            partial: false,
            transformed_jsx: false,
        },
        pexp_loc: pmod_loc,
        pexp_attributes: vec![],
    };

    // Create Primitive_promise.unsafe_await(import_apply)
    let await_expr = transform_await(import_apply, mod_expr.pmod_loc, arena);

    // Create unpack(await_expr)
    // OCaml: {e with pmod_desc = Pmod_unpack ...} - keeps original pmod_attributes (with @res.await)
    let transformed_mod_expr = current::ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_unpack(Box::new(await_expr)),
        pmod_loc: mod_expr.pmod_loc,
        // OCaml's {e with pmod_desc = ...} keeps the original attributes including @res.await
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    };

    // Create the transformed module binding
    // OCaml: {item with pstr_desc = Pstr_module {mb with pmb_expr = ...}}
    // This preserves original_pstr_loc (from item), not mb.pmb_loc
    let transformed_mb = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_module(current::ModuleBinding {
            pmb_name: mb.pmb_name.clone(),
            pmb_expr: transformed_mod_expr,
            pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena),
            pmb_loc: mb.pmb_loc,
        }),
        pstr_loc: original_pstr_loc, // Use original structure item location
    };

    Some((module_type_decl, transformed_mb))
}

// ========== Expression Rewriting ==========

/// Check if an expression is a pipe operator application (a -> b)
fn is_pipe_application(expr: &Expression, arena: &mut ParseArena) -> bool {
    if let ExpressionDesc::Pexp_apply { funct, args, .. } = &expr.pexp_desc {
        if args.len() == 2
            && matches!(&args[0].0, ArgLabel::Nolabel)
            && matches!(&args[1].0, ArgLabel::Nolabel)
        {
            if let ExpressionDesc::Pexp_ident(lid) = &funct.pexp_desc {
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
fn transform_string_exp(expr: &Expression, s: &str, delim: &str, arena: &mut ParseArena) -> Expression {
    // Check if this is a template string (has @res.template or @res.taggedTemplate)
    let is_template = has_template_attr(expr, arena);

    if delim == "js" {
        if is_template {
            // Template string: just change delimiter to "bq" (back quotes)
            Expression {
                pexp_desc: ExpressionDesc::Pexp_constant(Constant::String(
                    s.to_string(),
                    Some("bq".to_string()),
                )),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: expr.pexp_attributes.clone(),
            }
        } else {
            // JS string: transform the string and change delimiter to "*j"
            let transformed = transform_js_string(s);
            Expression {
                pexp_desc: ExpressionDesc::Pexp_constant(Constant::String(
                    transformed,
                    Some("*j".to_string()),
                )),
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
            ppat_desc: PatternDesc::Ppat_constant(Constant::String(
                transformed,
                Some("*j".to_string()),
            )),
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
        Payload::PStr(items) => {
            Payload::PStr(items.iter().flat_map(|item| rewrite_structure_item(item, arena)).collect())
        }
        Payload::PSig(items) => {
            Payload::PSig(items.iter().map(|item| rewrite_signature_item(item, arena)).collect())
        }
        Payload::PTyp(typ) => Payload::PTyp(typ.clone()),
        Payload::PPat(pat, guard) => {
            Payload::PPat(
                Box::new(rewrite_pattern(pat, arena)),
                guard.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
            )
        }
    }
}

/// Rewrite a core type, recursing into nested types and extension payloads.
/// This matches OCaml's default_mapper.typ behavior, ensuring that expressions
/// inside Ptyp_extension payloads get the "js" -> "*j" delimiter transformation.
fn rewrite_core_type(typ: &CoreType, arena: &mut ParseArena) -> CoreType {
    let new_desc = match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_extension(ext) => {
            let (name, payload) = ext;
            CoreTypeDesc::Ptyp_extension((name.clone(), rewrite_payload(payload, arena)))
        }
        CoreTypeDesc::Ptyp_arrow { arg, ret, arity } => {
            // Note: OCaml's default_mapper.typ for Ptyp_arrow does NOT process arg.attrs
            // through self.attributes - it only maps arg.typ. So we clone arg.attrs as-is.
            CoreTypeDesc::Ptyp_arrow {
                arg: Box::new(TypeArg {
                    attrs: arg.attrs.clone(),
                    lbl: arg.lbl.clone(),
                    typ: rewrite_core_type(&arg.typ, arena),
                }),
                ret: Box::new(rewrite_core_type(ret, arena)),
                arity: *arity,
            }
        }
        CoreTypeDesc::Ptyp_tuple(types) => {
            CoreTypeDesc::Ptyp_tuple(types.iter().map(|t| rewrite_core_type(t, arena)).collect())
        }
        CoreTypeDesc::Ptyp_constr(lid, args) => {
            CoreTypeDesc::Ptyp_constr(
                lid.clone(),
                args.iter().map(|t| rewrite_core_type(t, arena)).collect(),
            )
        }
        CoreTypeDesc::Ptyp_alias(inner, name) => {
            CoreTypeDesc::Ptyp_alias(Box::new(rewrite_core_type(inner, arena)), name.clone())
        }
        CoreTypeDesc::Ptyp_poly(vars, inner) => {
            CoreTypeDesc::Ptyp_poly(vars.clone(), Box::new(rewrite_core_type(inner, arena)))
        }
        CoreTypeDesc::Ptyp_object(fields, closed) => {
            CoreTypeDesc::Ptyp_object(
                fields.iter().map(|f| match f {
                    ObjectField::Otag(name, attrs, typ) => {
                        ObjectField::Otag(name.clone(), rewrite_attributes(attrs, arena), rewrite_core_type(typ, arena))
                    }
                    ObjectField::Oinherit(typ) => {
                        ObjectField::Oinherit(rewrite_core_type(typ, arena))
                    }
                }).collect(),
                *closed,
            )
        }
        CoreTypeDesc::Ptyp_variant(rows, closed, labels) => {
            CoreTypeDesc::Ptyp_variant(
                rows.iter().map(|r| match r {
                    RowField::Rtag(label, attrs, empty, types) => {
                        RowField::Rtag(
                            label.clone(),
                            rewrite_attributes(attrs, arena),
                            *empty,
                            types.iter().map(|t| rewrite_core_type(t, arena)).collect(),
                        )
                    }
                    RowField::Rinherit(typ) => {
                        RowField::Rinherit(rewrite_core_type(typ, arena))
                    }
                }).collect(),
                *closed,
                labels.clone(),
            )
        }
        CoreTypeDesc::Ptyp_package((lid, constraints)) => {
            CoreTypeDesc::Ptyp_package((
                lid.clone(),
                constraints.iter().map(|(l, t)| (l.clone(), rewrite_core_type(t, arena))).collect(),
            ))
        }
        // Ptyp_any, Ptyp_var - no nested types to rewrite
        _ => return CoreType {
            ptyp_desc: typ.ptyp_desc.clone(),
            ptyp_loc: typ.ptyp_loc,
            ptyp_attributes: rewrite_attributes(&typ.ptyp_attributes, arena),
        },
    };
    CoreType {
        ptyp_desc: new_desc,
        ptyp_loc: typ.ptyp_loc,
        ptyp_attributes: rewrite_attributes(&typ.ptyp_attributes, arena),
    }
}

/// Rewrite a type declaration, transforming strings in all nested attributes and types
fn rewrite_type_declaration(tdcl: &TypeDeclaration, arena: &mut ParseArena) -> TypeDeclaration {
    TypeDeclaration {
        ptype_name: tdcl.ptype_name.clone(),
        ptype_params: tdcl.ptype_params.iter().map(|(t, v)| (rewrite_core_type(t, arena), *v)).collect(),
        ptype_cstrs: tdcl.ptype_cstrs.clone(),
        ptype_kind: rewrite_type_kind(&tdcl.ptype_kind, arena),
        ptype_private: tdcl.ptype_private,
        ptype_manifest: tdcl.ptype_manifest.as_ref().map(|t| rewrite_core_type(t, arena)),
        ptype_attributes: rewrite_attributes(&tdcl.ptype_attributes, arena),
        ptype_loc: tdcl.ptype_loc,
    }
}

/// Rewrite a type kind, transforming strings in constructor/label attributes
fn rewrite_type_kind(kind: &TypeKind, arena: &mut ParseArena) -> TypeKind {
    match kind {
        TypeKind::Ptype_abstract => TypeKind::Ptype_abstract,
        TypeKind::Ptype_open => TypeKind::Ptype_open,
        TypeKind::Ptype_variant(constructors) => {
            TypeKind::Ptype_variant(
                constructors
                    .iter()
                    .map(|ctor| rewrite_constructor_declaration(ctor, arena))
                    .collect(),
            )
        }
        TypeKind::Ptype_record(labels) => {
            TypeKind::Ptype_record(
                labels
                    .iter()
                    .map(|label| rewrite_label_declaration(label, arena))
                    .collect(),
            )
        }
    }
}

/// Rewrite a constructor declaration, transforming strings in attributes
fn rewrite_constructor_declaration(
    ctor: &ConstructorDeclaration,
    arena: &mut ParseArena,
) -> ConstructorDeclaration {
    ConstructorDeclaration {
        pcd_name: ctor.pcd_name.clone(),
        pcd_args: rewrite_constructor_arguments(&ctor.pcd_args, arena),
        pcd_res: ctor.pcd_res.as_ref().map(|t| rewrite_core_type(t, arena)),
        pcd_loc: ctor.pcd_loc,
        pcd_attributes: rewrite_attributes(&ctor.pcd_attributes, arena),
    }
}

/// Rewrite constructor arguments, transforming strings in nested record labels
fn rewrite_constructor_arguments(
    args: &ConstructorArguments,
    arena: &mut ParseArena,
) -> ConstructorArguments {
    match args {
        ConstructorArguments::Pcstr_tuple(types) => ConstructorArguments::Pcstr_tuple(types.iter().map(|t| rewrite_core_type(t, arena)).collect()),
        ConstructorArguments::Pcstr_record(labels) => {
            ConstructorArguments::Pcstr_record(
                labels
                    .iter()
                    .map(|label| rewrite_label_declaration(label, arena))
                    .collect(),
            )
        }
    }
}

/// Rewrite a label declaration (record field), transforming strings in attributes and types
fn rewrite_label_declaration(label: &LabelDeclaration, arena: &mut ParseArena) -> LabelDeclaration {
    LabelDeclaration {
        pld_name: label.pld_name.clone(),
        pld_mutable: label.pld_mutable,
        pld_type: rewrite_core_type(&label.pld_type, arena),
        pld_loc: label.pld_loc,
        pld_attributes: rewrite_attributes(&label.pld_attributes, arena),
        pld_optional: label.pld_optional,
    }
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
fn is_simple_pattern(p: &Pattern) -> bool {
    match &p.ppat_desc {
        PatternDesc::Ppat_any => true,
        PatternDesc::Ppat_var(_) => true,
        PatternDesc::Ppat_constraint(inner, _) => is_simple_pattern(inner),
        _ => false,
    }
}

/// Destructure an expression through Pexp_open chains to find a tuple.
/// Returns (open_contexts, tuple_elements) if the expression is a
/// (possibly open-wrapped) tuple.
///
/// The open contexts are accumulated in reverse order (innermost first),
/// matching the OCaml implementation.
fn destruct_open_tuple(e: &Expression) -> Option<(Vec<OpenCtx>, &Vec<Expression>)> {
    destruct_open_tuple_inner(e, Vec::new())
}

fn destruct_open_tuple_inner<'a>(
    e: &'a Expression,
    mut acc: Vec<OpenCtx>,
) -> Option<(Vec<OpenCtx>, &'a Vec<Expression>)> {
    match &e.pexp_desc {
        ExpressionDesc::Pexp_open(flag, lid, cont) => {
            acc.push(OpenCtx {
                flag: *flag,
                lid: *lid,
                loc: e.pexp_loc,
                attrs: e.pexp_attributes.clone(),
            });
            destruct_open_tuple_inner(cont, acc)
        }
        ExpressionDesc::Pexp_tuple(es) => Some((acc, es)),
        _ => None,
    }
}

/// Restore open expression wrappers around an expression.
/// The opens list is in reverse order (innermost first), so we fold left
/// to rebuild the nesting correctly.
fn restore_exp(expr: Expression, opens: &[OpenCtx]) -> Expression {
    opens.iter().fold(expr, |inner, open| Expression {
        pexp_desc: ExpressionDesc::Pexp_open(open.flag, open.lid, Box::new(inner)),
        pexp_loc: open.loc,
        pexp_attributes: open.attrs.clone(),
    })
}

/// Flatten a single value binding into one or more bindings.
/// If the binding is a tuple pattern matched against a tuple expression
/// (possibly wrapped in open expressions), desugar into individual bindings.
fn flatten_value_binding(vb: &ValueBinding, arena: &mut ParseArena) -> Vec<ValueBinding> {
    let pvb_pat = rewrite_pattern(&vb.pvb_pat, arena);
    let pvb_expr = rewrite_expression(&vb.pvb_expr, arena);
    let pvb_attributes = rewrite_attributes(&vb.pvb_attributes, arena);

    if let PatternDesc::Ppat_tuple(ref pats) = pvb_pat.ppat_desc {
        if pats.iter().all(is_simple_pattern) {
            if let Some((opens, exprs)) = destruct_open_tuple(&pvb_expr) {
                if exprs.len() == pats.len() {
                    return pats
                        .iter()
                        .zip(exprs.iter())
                        .map(|(pat, expr)| ValueBinding {
                            pvb_pat: pat.clone(),
                            pvb_expr: restore_exp(expr.clone(), &opens),
                            pvb_attributes: pvb_attributes.clone(),
                            pvb_loc: vb.pvb_loc,
                        })
                        .collect();
                }
            }
        }
    }

    vec![ValueBinding {
        pvb_pat,
        pvb_expr,
        pvb_attributes,
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
        // String constant with delimiter: transform js -> *j
        PatternDesc::Ppat_constant(Constant::String(s, Some(delim))) => {
            let base = transform_string_pat(pat, s, delim);
            return Pattern {
                ppat_attributes: attrs,
                ..base
            };
        }
        // Strip 'l' suffix from integer literals
        PatternDesc::Ppat_constant(Constant::Integer(s, Some('l'))) => {
            PatternDesc::Ppat_constant(Constant::Integer(s.clone(), None))
        }
        // Other constants: no transformation needed
        PatternDesc::Ppat_constant(c) => PatternDesc::Ppat_constant(c.clone()),

        // Alias pattern: recurse into the aliased pattern
        PatternDesc::Ppat_alias(inner, name) => {
            PatternDesc::Ppat_alias(Box::new(rewrite_pattern(inner, arena)), name.clone())
        }

        // Tuple pattern: recurse into all elements
        PatternDesc::Ppat_tuple(pats) => {
            PatternDesc::Ppat_tuple(pats.iter().map(|p| rewrite_pattern(p, arena)).collect())
        }

        // Constructor pattern: recurse into optional payload
        PatternDesc::Ppat_construct(lid, opt_p) => {
            PatternDesc::Ppat_construct(
                lid.clone(),
                opt_p.as_ref().map(|p| Box::new(rewrite_pattern(p, arena))),
            )
        }

        // Variant pattern: recurse into optional payload
        PatternDesc::Ppat_variant(label, opt_p) => {
            PatternDesc::Ppat_variant(
                label.clone(),
                opt_p.as_ref().map(|p| Box::new(rewrite_pattern(p, arena))),
            )
        }

        // Record pattern: recurse into all field patterns
        PatternDesc::Ppat_record(fields, flag) => {
            PatternDesc::Ppat_record(
                fields
                    .iter()
                    .map(|f| PatternRecordField {
                        lid: f.lid.clone(),
                        pat: rewrite_pattern(&f.pat, arena),
                        opt: f.opt,
                    })
                    .collect(),
                *flag,
            )
        }

        // Array pattern: recurse into all elements
        PatternDesc::Ppat_array(pats) => {
            PatternDesc::Ppat_array(pats.iter().map(|p| rewrite_pattern(p, arena)).collect())
        }

        // Or pattern: recurse into both alternatives
        PatternDesc::Ppat_or(p1, p2) => {
            PatternDesc::Ppat_or(
                Box::new(rewrite_pattern(p1, arena)),
                Box::new(rewrite_pattern(p2, arena)),
            )
        }

        // Constraint pattern: recurse into pattern and type
        PatternDesc::Ppat_constraint(inner_pat, core_type) => {
            PatternDesc::Ppat_constraint(
                Box::new(rewrite_pattern(inner_pat, arena)),
                rewrite_core_type(core_type, arena),
            )
        }

        // Exception pattern: recurse into inner pattern
        PatternDesc::Ppat_exception(inner) => {
            PatternDesc::Ppat_exception(Box::new(rewrite_pattern(inner, arena)))
        }

        // Open pattern: recurse into inner pattern
        PatternDesc::Ppat_open(lid, inner) => {
            PatternDesc::Ppat_open(lid.clone(), Box::new(rewrite_pattern(inner, arena)))
        }

        // Patterns without nested patterns: clone as-is
        PatternDesc::Ppat_any => PatternDesc::Ppat_any,
        PatternDesc::Ppat_var(name) => PatternDesc::Ppat_var(name.clone()),
        PatternDesc::Ppat_interval(c1, c2) => PatternDesc::Ppat_interval(c1.clone(), c2.clone()),
        PatternDesc::Ppat_type(lid) => PatternDesc::Ppat_type(lid.clone()),
        PatternDesc::Ppat_unpack(name) => PatternDesc::Ppat_unpack(name.clone()),
        PatternDesc::Ppat_extension((name, payload)) => {
            PatternDesc::Ppat_extension((name.clone(), rewrite_payload(payload, arena)))
        }
    };

    Pattern {
        ppat_desc: desc,
        ppat_loc: pat.ppat_loc,
        ppat_attributes: attrs,
    }
}

/// Rewrite an expression, desugaring pipe operators
fn rewrite_expression(expr: &Expression, arena: &mut ParseArena) -> Expression {
    // Handle string constant transformations first
    if let ExpressionDesc::Pexp_constant(Constant::String(s, Some(delim))) = &expr.pexp_desc {
        return transform_string_exp(expr, s, delim, arena);
    }

    // Handle integer literal suffix stripping ('l' suffix)
    // OCaml: {e with pexp_desc = Pexp_constant (Pconst_integer (s, None))}
    // This is an early-return case that preserves attributes without remapping.
    if let ExpressionDesc::Pexp_constant(Constant::Integer(s, Some('l'))) = &expr.pexp_desc {
        return Expression {
            pexp_desc: ExpressionDesc::Pexp_constant(Constant::Integer(s.clone(), None)),
            pexp_loc: expr.pexp_loc,
            pexp_attributes: expr.pexp_attributes.clone(),
        };
    }

    // First check if this is a pipe or #= application
    if let ExpressionDesc::Pexp_apply {
        funct,
        args,
        partial: _,
        transformed_jsx: _,
    } = &expr.pexp_desc
    {
        // Check if this is a binary op: -> or #= with two args
        if args.len() == 2
            && matches!(&args[0].0, ArgLabel::Nolabel)
            && matches!(&args[1].0, ArgLabel::Nolabel)
        {
            if let ExpressionDesc::Pexp_ident(lid) = &funct.pexp_desc {
                if let Longident::Lident(op_idx) = arena.get_longident(lid.txt) {
                    let op = arena.get_string(*op_idx);
                    if op == "->" {
                        // This is a pipe: a -> f
                        // First recursively rewrite both arguments
                        let a = rewrite_expression(&args[0].1, arena);
                        let f = rewrite_expression(&args[1].1, arena);

                        // Now desugar based on what f is
                        return desugar_pipe(expr, a, f, arena);
                    }
                    if op == "#=" {
                        // This is a setter: obj["prop"] = value
                        // OCaml transforms: Pexp_apply("#=", [Pexp_send(obj, name), value])
                        // Into: Pexp_constraint(Pexp_apply(Pexp_send(obj, name^"#="), [value]), unit)
                        return desugar_hash_set(expr, &args[0].1, &args[1].1, arena);
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
/// - `Pexp_send(obj, {txt=name})`: becomes
///   `Pexp_constraint(Pexp_apply(Pexp_send(obj, name^"#="), [value]), unit)`
///
/// This matches OCaml's `ast_exp_apply.ml` gen_assignment.
fn desugar_hash_set(
    expr: &Expression,
    obj_expr: &Expression,
    value_expr: &Expression,
    arena: &mut ParseArena,
) -> Expression {
    let loc = expr.pexp_loc;

    match &obj_expr.pexp_desc {
        ExpressionDesc::Pexp_send(obj, method_loc) => {
            let obj = rewrite_expression(obj, arena);
            let value = rewrite_expression(value_expr, arena);

            // Concatenate name with "#=" suffix
            let setter_name = format!("{}#=", method_loc.txt);

            // Create Pexp_send(obj, "name#=") with the outer loc
            let send_expr = Expression {
                pexp_desc: ExpressionDesc::Pexp_send(
                    Box::new(obj),
                    Located::new(setter_name, loc),
                ),
                pexp_loc: loc,
                pexp_attributes: vec![],
            };

            // Create Pexp_apply(send_expr, [(Nolabel, value)]) with the outer loc
            let apply_expr = Expression {
                pexp_desc: ExpressionDesc::Pexp_apply {
                    funct: Box::new(send_expr),
                    args: vec![(ArgLabel::Nolabel, value)],
                    partial: false,
                    transformed_jsx: false,
                },
                pexp_loc: loc,
                pexp_attributes: vec![],
            };

            // Create type "unit" = Ptyp_constr(Lident "unit", [])
            let unit_lid = Longident::Lident(arena.intern_string("unit"));
            let unit_lid_idx = arena.push_longident(unit_lid);
            let unit_type = CoreType {
                ptyp_desc: CoreTypeDesc::Ptyp_constr(Located::new(unit_lid_idx, loc), vec![]),
                ptyp_loc: loc,
                ptyp_attributes: vec![],
            };

            // Wrap in Pexp_constraint
            Expression {
                pexp_desc: ExpressionDesc::Pexp_constraint(Box::new(apply_expr), unit_type),
                pexp_loc: loc,
                pexp_attributes: vec![],
            }
        }
        _ => {
            // Fallback: just rewrite sub-expressions generically
            rewrite_expression_generic(expr, arena)
        }
    }
}

/// Desugar pipe expression: a -> f
/// Transforms based on what f is:
/// - f is Pexp_variant(label, None): becomes Pexp_variant(label, Some(a))
/// - f is Pexp_construct(ctor, None): becomes Pexp_construct(ctor, Some(a))
/// - f is Pexp_apply(fn1, args): becomes Pexp_apply(fn1, (Nolabel, a) :: args)
/// - f is Pexp_tuple(xs): binds a and maps each element
/// - otherwise: becomes f(a) = Pexp_apply(f, [(Nolabel, a)])
fn desugar_pipe(
    original: &Expression,
    a: Expression,
    f: Expression,
    _arena: &mut ParseArena,
) -> Expression {
    match &f.pexp_desc {
        // a -> `Variant becomes `Variant(a)
        ExpressionDesc::Pexp_variant(label, None) => Expression {
            pexp_desc: ExpressionDesc::Pexp_variant(label.clone(), Some(Box::new(a))),
            pexp_loc: original.pexp_loc,
            pexp_attributes: original.pexp_attributes.clone(),
        },

        // a -> Constructor becomes Constructor(a)
        ExpressionDesc::Pexp_construct(ctor, None) => Expression {
            pexp_desc: ExpressionDesc::Pexp_construct(ctor.clone(), Some(Box::new(a))),
            pexp_loc: original.pexp_loc,
            pexp_attributes: original.pexp_attributes.clone(),
        },

        // a -> f(b, c) becomes f(a, b, c)
        ExpressionDesc::Pexp_apply {
            funct: fn1,
            args,
            partial,
            transformed_jsx,
        } => {
            let mut new_args = Vec::with_capacity(args.len() + 1);
            new_args.push((ArgLabel::Nolabel, a));
            new_args.extend(args.iter().cloned());

            Expression {
                pexp_desc: ExpressionDesc::Pexp_apply {
                    funct: fn1.clone(),
                    args: new_args,
                    partial: *partial,
                    transformed_jsx: *transformed_jsx,
                },
                pexp_loc: original.pexp_loc,
                // Combine attributes from original and f
                pexp_attributes: {
                    let mut attrs = original.pexp_attributes.clone();
                    attrs.extend(f.pexp_attributes.iter().cloned());
                    attrs
                },
            }
        }

        // a -> (x, y) with tuple - for now, just create f(a)
        // TODO: Handle the bound case properly like OCaml does
        ExpressionDesc::Pexp_tuple(_) => {
            // For simplicity, just make it f(a)
            Expression {
                pexp_desc: ExpressionDesc::Pexp_apply {
                    funct: Box::new(f),
                    args: vec![(ArgLabel::Nolabel, a)],
                    partial: false,
                    transformed_jsx: false,
                },
                pexp_loc: original.pexp_loc,
                pexp_attributes: original.pexp_attributes.clone(),
            }
        }

        // Default: a -> f becomes f(a)
        _ => Expression {
            pexp_desc: ExpressionDesc::Pexp_apply {
                funct: Box::new(f),
                args: vec![(ArgLabel::Nolabel, a)],
                partial: false,
                transformed_jsx: false,
            },
            pexp_loc: original.pexp_loc,
            pexp_attributes: original.pexp_attributes.clone(),
        },
    }
}

/// Generic expression rewriting - recurses into sub-expressions
fn rewrite_expression_generic(expr: &Expression, arena: &mut ParseArena) -> Expression {
    let new_desc = match &expr.pexp_desc {
        ExpressionDesc::Pexp_ident(_) | ExpressionDesc::Pexp_constant(_) => {
            // Even for simple expressions, we need to rewrite attributes
            // to transform strings (e.g., "js" -> "*j" in @warning("-3"))
            // This matches OCaml's default_mapper which always maps attrs.
            return Expression {
                pexp_desc: expr.pexp_desc.clone(),
                pexp_loc: expr.pexp_loc,
                pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena),
            };
        }

        ExpressionDesc::Pexp_let(rec_flag, bindings, body) => {
            // Check for record pattern destructuring: convert to match expression
            // OCaml's bs_builtin_ppx.ml (lines 295-319) converts:
            //   let {field1, field2} = expr in body
            // to:
            //   match expr with {field1, field2} -> body
            if *rec_flag == RecFlag::Nonrecursive && bindings.len() == 1 {
                let vb = &bindings[0];
                let is_record_pat = match &vb.pvb_pat.ppat_desc {
                    PatternDesc::Ppat_record(..) => true,
                    PatternDesc::Ppat_alias(inner, _) => {
                        matches!(&inner.ppat_desc, PatternDesc::Ppat_record(..))
                    }
                    _ => false,
                };
                // Don't convert if the expression is Pexp_pack (module unpacking)
                let is_pack = matches!(&vb.pvb_expr.pexp_desc, ExpressionDesc::Pexp_pack(_));
                if is_record_pat && !is_pack {
                    let rewritten_expr = rewrite_expression(&vb.pvb_expr, arena);
                    let rewritten_pat = rewrite_pattern(&vb.pvb_pat, arena);
                    let rewritten_body = rewrite_expression(body, arena);
                    // Merge attributes: expression attrs + binding attrs
                    let mut attrs = expr.pexp_attributes.clone();
                    attrs.extend(vb.pvb_attributes.iter().cloned());
                    let attrs = rewrite_attributes(&attrs, arena);
                    return Expression {
                        pexp_desc: ExpressionDesc::Pexp_match(
                            Box::new(rewritten_expr),
                            vec![Case {
                                pc_bar: None,
                                pc_lhs: rewritten_pat,
                                pc_guard: None,
                                pc_rhs: rewritten_body,
                            }],
                        ),
                        pexp_loc: expr.pexp_loc,
                        pexp_attributes: attrs,
                    };
                }
            }

            let new_bindings = flatten_value_bindings(bindings, arena);
            ExpressionDesc::Pexp_let(
                *rec_flag,
                new_bindings,
                Box::new(rewrite_expression(body, arena)),
            )
        }

        ExpressionDesc::Pexp_fun {
            arg_label,
            default,
            lhs,
            rhs,
            arity,
            is_async,
        } => {
            // First, recursively rewrite the function components
            let rewritten_default = default.as_ref().map(|e| Box::new(rewrite_expression(e, arena)));
            let rewritten_lhs = rewrite_pattern(lhs, arena);
            let rewritten_rhs = Box::new(rewrite_expression(rhs, arena));

            // Create the rewritten fun expression
            let mut rewritten_fun = Expression {
                pexp_desc: ExpressionDesc::Pexp_fun {
                    arg_label: arg_label.clone(),
                    default: rewritten_default,
                    lhs: rewritten_lhs,
                    rhs: rewritten_rhs,
                    arity: *arity,
                    is_async: *is_async,
                },
                pexp_loc: expr.pexp_loc,
                pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena),
            };

            // If this is an async function, wrap the innermost body with unsafe_async
            // OCaml: Ast_async.make_function_async
            if *is_async {
                // Get location from the pattern for the ghost location
                let pattern_loc = lhs.ppat_loc;
                rewritten_fun = add_promise_to_fun_body(&rewritten_fun, pattern_loc, arena);
            }

            return rewritten_fun;
        }

        ExpressionDesc::Pexp_apply {
            funct,
            args,
            partial,
            transformed_jsx,
        } => ExpressionDesc::Pexp_apply {
            funct: Box::new(rewrite_expression(funct, arena)),
            args: args
                .iter()
                .map(|(lbl, e)| (lbl.clone(), rewrite_expression(e, arena)))
                .collect(),
            partial: *partial,
            transformed_jsx: *transformed_jsx,
        },

        ExpressionDesc::Pexp_match(scrutinee, cases) => {
            // Boolean match → if-then-else conversion
            // OCaml's bs_builtin_ppx.ml (lines 138-167) converts:
            //   switch b { | true => t | false => f }
            // to:
            //   if b { t } else { f }
            if cases.len() == 2
                && cases[0].pc_guard.is_none()
                && cases[1].pc_guard.is_none()
            {
                let is_true = |pat: &Pattern| -> bool {
                    if let PatternDesc::Ppat_construct(lid, None) = &pat.ppat_desc {
                        matches!(arena.get_longident(lid.txt), Longident::Lident(s) if arena.get_string(*s) == "true")
                    } else {
                        false
                    }
                };
                let is_false = |pat: &Pattern| -> bool {
                    if let PatternDesc::Ppat_construct(lid, None) = &pat.ppat_desc {
                        matches!(arena.get_longident(lid.txt), Longident::Lident(s) if arena.get_string(*s) == "false")
                    } else {
                        false
                    }
                };
                let (t_exp, f_exp) = if is_true(&cases[0].pc_lhs) && is_false(&cases[1].pc_lhs) {
                    (Some(&cases[0].pc_rhs), Some(&cases[1].pc_rhs))
                } else if is_false(&cases[0].pc_lhs) && is_true(&cases[1].pc_lhs) {
                    (Some(&cases[1].pc_rhs), Some(&cases[0].pc_rhs))
                } else {
                    (None, None)
                };
                if let (Some(t_exp), Some(f_exp)) = (t_exp, f_exp) {
                    return Expression {
                        pexp_desc: ExpressionDesc::Pexp_ifthenelse(
                            Box::new(rewrite_expression(scrutinee, arena)),
                            Box::new(rewrite_expression(t_exp, arena)),
                            Some(Box::new(rewrite_expression(f_exp, arena))),
                        ),
                        pexp_loc: expr.pexp_loc,
                        pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena),
                    };
                }
            }

            ExpressionDesc::Pexp_match(
                Box::new(rewrite_expression(scrutinee, arena)),
                rewrite_cases(cases, arena),
            )
        }

        ExpressionDesc::Pexp_try(body, cases) => ExpressionDesc::Pexp_try(
            Box::new(rewrite_expression(body, arena)),
            rewrite_cases(cases, arena),
        ),

        ExpressionDesc::Pexp_tuple(exprs) => ExpressionDesc::Pexp_tuple(
            exprs.iter().map(|e| rewrite_expression(e, arena)).collect(),
        ),

        ExpressionDesc::Pexp_construct(ctor, arg) => ExpressionDesc::Pexp_construct(
            ctor.clone(),
            arg.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
        ),

        ExpressionDesc::Pexp_variant(label, arg) => ExpressionDesc::Pexp_variant(
            label.clone(),
            arg.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
        ),

        ExpressionDesc::Pexp_record(fields, spread) => {
            let new_fields = fields
                .iter()
                .map(|f| current::ExpressionRecordField {
                    lid: f.lid.clone(),
                    expr: rewrite_expression(&f.expr, arena),
                    opt: f.opt,
                })
                .collect();
            ExpressionDesc::Pexp_record(
                new_fields,
                spread.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
            )
        }

        ExpressionDesc::Pexp_field(e, lid) => {
            ExpressionDesc::Pexp_field(Box::new(rewrite_expression(e, arena)), lid.clone())
        }

        ExpressionDesc::Pexp_setfield(e1, lid, e2) => ExpressionDesc::Pexp_setfield(
            Box::new(rewrite_expression(e1, arena)),
            lid.clone(),
            Box::new(rewrite_expression(e2, arena)),
        ),

        ExpressionDesc::Pexp_array(exprs) => ExpressionDesc::Pexp_array(
            exprs.iter().map(|e| rewrite_expression(e, arena)).collect(),
        ),

        ExpressionDesc::Pexp_ifthenelse(cond, then_branch, else_branch) => {
            ExpressionDesc::Pexp_ifthenelse(
                Box::new(rewrite_expression(cond, arena)),
                Box::new(rewrite_expression(then_branch, arena)),
                else_branch
                    .as_ref()
                    .map(|e| Box::new(rewrite_expression(e, arena))),
            )
        }

        ExpressionDesc::Pexp_sequence(e1, e2) => ExpressionDesc::Pexp_sequence(
            Box::new(rewrite_expression(e1, arena)),
            Box::new(rewrite_expression(e2, arena)),
        ),

        ExpressionDesc::Pexp_while(cond, body) => ExpressionDesc::Pexp_while(
            Box::new(rewrite_expression(cond, arena)),
            Box::new(rewrite_expression(body, arena)),
        ),

        ExpressionDesc::Pexp_for(pat, e1, e2, dir, body) => ExpressionDesc::Pexp_for(
            rewrite_pattern(pat, arena),
            Box::new(rewrite_expression(e1, arena)),
            Box::new(rewrite_expression(e2, arena)),
            *dir,
            Box::new(rewrite_expression(body, arena)),
        ),

        ExpressionDesc::Pexp_constraint(e, ty) => {
            ExpressionDesc::Pexp_constraint(
                Box::new(rewrite_expression(e, arena)),
                rewrite_core_type(ty, arena),
            )
        }

        ExpressionDesc::Pexp_coerce(e, ty1, ty2) => ExpressionDesc::Pexp_coerce(
            Box::new(rewrite_expression(e, arena)),
            ty1.as_ref().map(|t| rewrite_core_type(t, arena)),
            rewrite_core_type(ty2, arena),
        ),

        ExpressionDesc::Pexp_send(e, method) => {
            ExpressionDesc::Pexp_send(Box::new(rewrite_expression(e, arena)), method.clone())
        }

        ExpressionDesc::Pexp_assert(e) => {
            ExpressionDesc::Pexp_assert(Box::new(rewrite_expression(e, arena)))
        }

        ExpressionDesc::Pexp_await(e) => {
            // Transform: await expr -> Primitive_promise.unsafe_await(expr)
            // OCaml's create_await_expression uses the inner expression's pexp_loc
            // (not the Pexp_await node's loc) for the ghost location
            // OCaml creates a NEW expression with empty attributes, discarding any
            // attributes on the Pexp_await node (like @res.braces)
            let rewritten_inner = rewrite_expression(e, arena);
            return transform_await(rewritten_inner, e.pexp_loc, arena);
        }

        ExpressionDesc::Pexp_pack(mod_expr) => {
            // Module expressions - don't recurse for now
            ExpressionDesc::Pexp_pack(mod_expr.clone())
        }

        ExpressionDesc::Pexp_letmodule(name, mod_expr, body) => {
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
            if let ModuleExprDesc::Pmod_ident(located_lid) = &mod_expr.pmod_desc {
                if has_await_attribute(&mod_expr.pmod_attributes, arena) {
                    // Generate module type name: __Belt_List__
                    let module_type_name = local_module_type_name(located_lid.txt, arena);
                    let module_type_name_idx = arena.intern_string(&module_type_name);
                    let module_type_lid_idx = arena.push_lident_from_idx(module_type_name_idx);
                    // Use the original module ident's location for the generated type
                    let module_type_lid = Located {
                        txt: module_type_lid_idx,
                        loc: located_lid.loc,
                    };

                    let transformed_mod_expr = create_await_module_expression(mod_expr, module_type_lid, arena);

                    // OCaml: {e with pexp_desc = Pexp_letmodule(lid, transformed, self.expr self expr)}
                    return Expression {
                        pexp_desc: ExpressionDesc::Pexp_letmodule(
                            name.clone(),
                            transformed_mod_expr,
                            Box::new(rewrite_expression(body, arena)),
                        ),
                        pexp_loc: expr.pexp_loc,
                        pexp_attributes: expr.pexp_attributes.clone(),
                    };
                }
            }

            // Check Case 2: Pmod_constraint(Pmod_ident, Pmty_ident mtyp_lid) with await
            if let ModuleExprDesc::Pmod_constraint(inner_mod, mty) = &mod_expr.pmod_desc {
                if let ModuleExprDesc::Pmod_ident(_) = &inner_mod.pmod_desc {
                    if let ModuleTypeDesc::Pmty_ident(mtyp_lid) = &mty.pmty_desc {
                        // Check for @res.await on either the inner module or the constraint
                        if has_await_attribute(&inner_mod.pmod_attributes, arena)
                            || has_await_attribute(&mod_expr.pmod_attributes, arena)
                        {
                            // Use the existing module type identifier with its location
                            let transformed_mod_expr = create_await_module_expression(mod_expr, mtyp_lid.clone(), arena);

                            return Expression {
                                pexp_desc: ExpressionDesc::Pexp_letmodule(
                                    name.clone(),
                                    transformed_mod_expr,
                                    Box::new(rewrite_expression(body, arena)),
                                ),
                                pexp_loc: expr.pexp_loc,
                                pexp_attributes: expr.pexp_attributes.clone(),
                            };
                        }
                    }
                }
            }

            // Default: no await transformation needed, but DO recurse into module structure
            // to handle externals inside the module
            ExpressionDesc::Pexp_letmodule(
                name.clone(),
                rewrite_module_expr(mod_expr, arena),
                Box::new(rewrite_expression(body, arena)),
            )
        }

        ExpressionDesc::Pexp_letexception(exn, body) => ExpressionDesc::Pexp_letexception(
            exn.clone(),
            Box::new(rewrite_expression(body, arena)),
        ),

        ExpressionDesc::Pexp_open(override_flag, mod_name, body) => ExpressionDesc::Pexp_open(
            *override_flag,
            mod_name.clone(),
            Box::new(rewrite_expression(body, arena)),
        ),

        // Pexp_newtype is an early-return case in OCaml's expr_mapper:
        // {e with pexp_desc = Pexp_newtype (s, self.expr self body)}
        // It preserves the original expression's attributes without remapping.
        ExpressionDesc::Pexp_newtype(name, body) => {
            return Expression {
                pexp_desc: ExpressionDesc::Pexp_newtype(
                    name.clone(),
                    Box::new(rewrite_expression(body, arena)),
                ),
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
            ExpressionDesc::Pexp_jsx_element(rewrite_jsx_element(jsx, arena))
        }
    };

    Expression {
        pexp_desc: new_desc,
        pexp_loc: expr.pexp_loc,
        pexp_attributes: rewrite_attributes(&expr.pexp_attributes, arena),
    }
}

/// Rewrite cases for match/try expressions
fn rewrite_cases(cases: &[Case], arena: &mut ParseArena) -> Vec<Case> {
    cases
        .iter()
        .map(|c| Case {
            pc_bar: c.pc_bar,
            pc_lhs: rewrite_pattern(&c.pc_lhs, arena),
            pc_guard: c.pc_guard.as_ref().map(|e| rewrite_expression(e, arena)),
            pc_rhs: rewrite_expression(&c.pc_rhs, arena),
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
fn rewrite_jsx_children(children: &[Expression], arena: &mut ParseArena) -> Vec<Expression> {
    children
        .iter()
        .map(|e| rewrite_expression(e, arena))
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
                value: rewrite_expression(value, arena),
            },
            JsxProp::Spreading { loc, expr } => JsxProp::Spreading {
                loc: *loc,
                expr: rewrite_expression(expr, arena),
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

/// Parse @deriving attribute to extract derive actions
fn parse_deriving_actions(attrs: &[Attribute], arena: &mut ParseArena) -> (Vec<DeriveAction>, Vec<Attribute>) {
    let mut actions = vec![];
    let mut remaining_attrs = vec![];

    for attr in attrs {
        let (name_loc, payload) = attr;
        let name = arena.get_string(name_loc.txt);

        if name == "deriving" {
            // Parse the payload to extract actions
            if let Payload::PStr(items) = payload {
                // @deriving(accessors) or @deriving({jsConverter: newType})
                for item in items {
                    if let StructureItemDesc::Pstr_eval(expr, _) = &item.pstr_desc {
                        parse_deriving_expr(&expr.pexp_desc, &mut actions, arena);
                    }
                }
            }
        } else {
            remaining_attrs.push(attr.clone());
        }
    }

    (actions, remaining_attrs)
}

/// Parse a deriving expression to extract actions
fn parse_deriving_expr(expr_desc: &ExpressionDesc, actions: &mut Vec<DeriveAction>, arena: &mut ParseArena) {
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
            for expr in exprs {
                parse_deriving_expr(&expr.pexp_desc, actions, arena);
            }
        }
        // Record: @deriving({jsConverter: newType})
        ExpressionDesc::Pexp_record(fields, None) => {
            for field in fields {
                let lid = arena.get_longident(field.lid.txt);
                if let Longident::Lident(s) = lid {
                    let field_name = arena.get_string(*s);
                    match field_name {
                        "jsConverter" => {
                            // Check if value is `newType` or `{newType: true/false}`
                            let new_type = check_new_type_config(&field.expr, arena);
                            actions.push(DeriveAction::JsConverter { new_type });
                        }
                        "abstract" => {
                            actions.push(DeriveAction::Abstract { light: false });
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
        ExpressionDesc::Pexp_apply { funct, args, .. } => {
            // Check if it's a simple ident being applied
            if let ExpressionDesc::Pexp_ident(lid_loc) = &funct.pexp_desc {
                let lid = arena.get_longident(lid_loc.txt);
                if let Longident::Lident(s) = lid {
                    let name = arena.get_string(*s);
                    if name == "jsConverter" && !args.is_empty() {
                        // @deriving(jsConverter({newType: true}))
                        let (_, arg_expr) = &args[0];
                        let new_type = check_new_type_config(arg_expr, arena);
                        actions.push(DeriveAction::JsConverter { new_type });
                    }
                }
            }
        }
        _ => {}
    }
}

/// Check if an expression configures newType to true
fn check_new_type_config(expr: &Expression, arena: &mut ParseArena) -> bool {
    match &expr.pexp_desc {
        // {newType: true} or just `newType`
        ExpressionDesc::Pexp_ident(lid_loc) => {
            let lid = arena.get_longident(lid_loc.txt);
            if let Longident::Lident(s) = lid {
                let name = arena.get_string(*s);
                return name == "newType";
            }
            false
        }
        ExpressionDesc::Pexp_record(fields, _) => {
            for field in fields {
                let lid = arena.get_longident(field.lid.txt);
                if let Longident::Lident(s) = lid {
                    let field_name = arena.get_string(*s);
                    if field_name == "newType" {
                        // Check if value is `true`
                        if let ExpressionDesc::Pexp_construct(ctor_lid, None) = &field.expr.pexp_desc {
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

/// Generate accessor functions for @deriving(accessors)
fn generate_accessors(
    tdcl: &TypeDeclaration,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    match &tdcl.ptype_kind {
        TypeKind::Ptype_record(labels) => {
            // Generate accessor function for each field
            labels.iter().map(|label| {
                let core_type = core_type_of_type_declaration(tdcl, arena);

                // Create: let fieldName = param => param.fieldName
                let param_str = arena.intern_string("param");
                let param_pat = Pattern {
                    ppat_desc: PatternDesc::Ppat_constraint(
                        Box::new(Pattern {
                            ppat_desc: PatternDesc::Ppat_var(Located { txt: param_str, loc }),
                            ppat_loc: loc,
                            ppat_attributes: vec![],
                        }),
                        core_type.clone(),
                    ),
                    ppat_loc: loc,
                    ppat_attributes: vec![],
                };

                // param.fieldName
                let field_access = Expression {
                    pexp_desc: ExpressionDesc::Pexp_field(
                        Box::new(Expression {
                            pexp_desc: ExpressionDesc::Pexp_ident(Located {
                                txt: arena.push_longident(Longident::Lident(param_str)),
                                loc,
                            }),
                            pexp_loc: loc,
                            pexp_attributes: vec![],
                        }),
                        Located {
                            txt: arena.push_longident(Longident::Lident(label.pld_name.txt)),
                            loc,
                        },
                    ),
                    pexp_loc: loc,
                    pexp_attributes: vec![],
                };

                let fun_expr = Expression {
                    pexp_desc: ExpressionDesc::Pexp_fun {
                        arg_label: ArgLabel::Nolabel,
                        default: None,
                        lhs: param_pat,
                        rhs: Box::new(field_access),
                        is_async: false,
                        arity: arena.static_arity_1(),
                    },
                    pexp_loc: loc,
                    pexp_attributes: vec![],
                };

                let binding = ValueBinding {
                    pvb_pat: Pattern {
                        ppat_desc: PatternDesc::Ppat_var(Located {
                            txt: label.pld_name.txt,
                            loc: label.pld_name.loc,
                        }),
                        ppat_loc: loc,
                        ppat_attributes: vec![],
                    },
                    pvb_expr: fun_expr,
                    pvb_attributes: vec![],
                    pvb_loc: loc,
                };

                StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_value(RecFlag::Nonrecursive, vec![binding]),
                    pstr_loc: loc,
                }
            }).collect()
        }
        TypeKind::Ptype_variant(constructors) => {
            // Generate accessor function for each constructor
            constructors.iter().map(|ctor| {
                let ctor_name = arena.get_string(ctor.pcd_name.txt);
                let fn_name = uncapitalize_first(ctor_name);
                let fn_name_idx = arena.intern_string(&fn_name);
                let core_type = core_type_of_type_declaration(tdcl, arena);

                let arity = match &ctor.pcd_args {
                    ConstructorArguments::Pcstr_tuple(args) => args.len(),
                    ConstructorArguments::Pcstr_record(_) => {
                        // Record constructors not supported, skip
                        let unit_str = arena.intern_string("()");
                        let unit_lid = arena.push_longident(Longident::Lident(unit_str));
                        return StructureItem {
                            pstr_desc: StructureItemDesc::Pstr_eval(
                                Expression {
                                    pexp_desc: ExpressionDesc::Pexp_construct(
                                        Located { txt: unit_lid, loc },
                                        None,
                                    ),
                                    pexp_loc: loc,
                                    pexp_attributes: vec![],
                                },
                                vec![],
                            ),
                            pstr_loc: loc,
                        };
                    }
                };

                if arity == 0 {
                    // No args: let ctorName = CtorName
                    let ctor_expr = Expression {
                        pexp_desc: ExpressionDesc::Pexp_constraint(
                            Box::new(Expression {
                                pexp_desc: ExpressionDesc::Pexp_construct(
                                    Located {
                                        txt: arena.push_longident(Longident::Lident(ctor.pcd_name.txt)),
                                        loc,
                                    },
                                    None,
                                ),
                                pexp_loc: loc,
                                pexp_attributes: vec![],
                            }),
                            core_type,
                        ),
                        pexp_loc: loc,
                        pexp_attributes: vec![],
                    };

                    let binding = ValueBinding {
                        pvb_pat: Pattern {
                            ppat_desc: PatternDesc::Ppat_var(Located { txt: fn_name_idx, loc }),
                            ppat_loc: loc,
                            ppat_attributes: vec![],
                        },
                        pvb_expr: ctor_expr,
                        pvb_attributes: vec![],
                        pvb_loc: loc,
                    };

                    StructureItem {
                        pstr_desc: StructureItemDesc::Pstr_value(RecFlag::Nonrecursive, vec![binding]),
                        pstr_loc: loc,
                    }
                } else {
                    // Has args: let ctorName = (p0, p1, ...) => CtorName(p0, p1, ...)
                    let params: Vec<StrIdx> = (0..arity)
                        .map(|i| arena.intern_string(&format!("param_{}", i)))
                        .collect();

                    // Build the constructor argument tuple
                    let ctor_arg = if arity == 1 {
                        Expression {
                            pexp_desc: ExpressionDesc::Pexp_ident(Located {
                                txt: arena.push_longident(Longident::Lident(params[0])),
                                loc,
                            }),
                            pexp_loc: loc,
                            pexp_attributes: vec![],
                        }
                    } else {
                        Expression {
                            pexp_desc: ExpressionDesc::Pexp_tuple(
                                params.iter().map(|&p| Expression {
                                    pexp_desc: ExpressionDesc::Pexp_ident(Located {
                                        txt: arena.push_longident(Longident::Lident(p)),
                                        loc,
                                    }),
                                    pexp_loc: loc,
                                    pexp_attributes: vec![],
                                }).collect()
                            ),
                            pexp_loc: loc,
                            pexp_attributes: vec![],
                        }
                    };

                    let ctor_expr = Expression {
                        pexp_desc: ExpressionDesc::Pexp_constraint(
                            Box::new(Expression {
                                pexp_desc: ExpressionDesc::Pexp_construct(
                                    Located {
                                        txt: arena.push_longident(Longident::Lident(ctor.pcd_name.txt)),
                                        loc,
                                    },
                                    Some(Box::new(ctor_arg)),
                                ),
                                pexp_loc: loc,
                                pexp_attributes: vec![],
                            }),
                            core_type,
                        ),
                        pexp_loc: loc,
                        pexp_attributes: vec![],
                    };

                    // Wrap with function parameters (fold right)
                    let body = params.iter().rev().fold(ctor_expr, |acc, &param| {
                        Expression {
                            pexp_desc: ExpressionDesc::Pexp_fun {
                                arg_label: ArgLabel::Nolabel,
                                default: None,
                                lhs: Pattern {
                                    ppat_desc: PatternDesc::Ppat_var(Located { txt: param, loc }),
                                    ppat_loc: loc,
                                    ppat_attributes: vec![],
                                },
                                rhs: Box::new(acc),
                                is_async: false,
                                arity: arena.push_arity(None), // Inner functions have no arity annotation
                            },
                            pexp_loc: loc,
                            pexp_attributes: vec![],
                        }
                    });

                    // The outermost function should have the arity
                    let final_expr = set_outermost_arity(body, arity as i32, arena);

                    let binding = ValueBinding {
                        pvb_pat: Pattern {
                            ppat_desc: PatternDesc::Ppat_var(Located { txt: fn_name_idx, loc }),
                            ppat_loc: loc,
                            ppat_attributes: vec![],
                        },
                        pvb_expr: final_expr,
                        pvb_attributes: vec![],
                        pvb_loc: loc,
                    };

                    StructureItem {
                        pstr_desc: StructureItemDesc::Pstr_value(RecFlag::Nonrecursive, vec![binding]),
                        pstr_loc: loc,
                    }
                }
            }).collect()
        }
        _ => vec![], // Abstract or open types not supported
    }
}

/// Set the arity of the outermost Pexp_fun
fn set_outermost_arity(expr: Expression, arity: i32, arena: &mut ParseArena) -> Expression {
    if let ExpressionDesc::Pexp_fun { arg_label, default, lhs, rhs, is_async, arity: _ } = expr.pexp_desc {
        Expression {
            pexp_desc: ExpressionDesc::Pexp_fun {
                arg_label,
                default,
                lhs,
                rhs,
                is_async,
                arity: arena.push_arity(Some(arity)),
            },
            pexp_loc: expr.pexp_loc,
            pexp_attributes: expr.pexp_attributes,
        }
    } else {
        expr
    }
}

/// Generate a core type representing the type declaration
fn core_type_of_type_declaration(tdcl: &TypeDeclaration, arena: &mut ParseArena) -> CoreType {
    let loc = tdcl.ptype_loc;
    let name_lid = arena.push_longident(Longident::Lident(tdcl.ptype_name.txt));

    if tdcl.ptype_params.is_empty() {
        CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_constr(
                Located { txt: name_lid, loc },
                vec![],
            ),
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        }
    } else {
        // Type has parameters: 'a t -> t<'a>
        let type_args: Vec<CoreType> = tdcl.ptype_params.iter().map(|(core_type, _)| {
            core_type.clone()
        }).collect();
        CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_constr(
                Located { txt: name_lid, loc },
                type_args,
            ),
            ptyp_loc: loc,
            ptyp_attributes: vec![],
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

/// Handle @deriving for type declarations
///
/// OCaml transforms `@deriving(accessors) type t = { x: int }` into:
/// ```
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
            pstr_desc: StructureItemDesc::Pstr_type(rec_flag, rewritten_tdcls),
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
                rewritten.ptype_attributes = rewrite_attributes(&new_attrs, arena);
            }
            rewritten
        })
        .collect();

    let type_str_item = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_type(rec_flag, new_tdcls),
        pstr_loc: loc,
    };

    // Step 2: Generate accessor includes for each action
    let mut include_items: Vec<StructureItem> = vec![];

    for action in &actions {
        match action {
            DeriveAction::Accessors => {
                for tdcl in tdcls {
                    // Generate `include (struct <accessors> end : sig <sigs> end)`
                    if let Some(include_item) = generate_accessor_include(tdcl, loc, arena) {
                        include_items.push(include_item);
                    }
                }
            }
            DeriveAction::JsConverter { new_type: _ } => {
                // TODO: Implement jsConverter generation
            }
            DeriveAction::Abstract { light: _ } => {
                // TODO: Implement abstract generation
            }
        }
    }

    // Step 3: Wrap everything in `include (struct <type_decl> <includes> end)`
    let mut inner_structure = vec![type_str_item];
    inner_structure.extend(include_items);

    let mod_expr = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(inner_structure),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    let include_decl = current::IncludeDeclaration {
        pincl_mod: mod_expr,
        pincl_loc: loc,
        pincl_attributes: vec![],
    };

    vec![StructureItem {
        pstr_desc: StructureItemDesc::Pstr_include(include_decl),
        pstr_loc: loc,
    }]
}

/// Generate `include (struct <accessor_bindings> end : sig <accessor_sigs> end)`
fn generate_accessor_include(
    tdcl: &TypeDeclaration,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> Option<StructureItem> {
    // Get core type with @deriving attributes (OCaml preserves these in the generated code)
    let core_type_with_attrs = core_type_of_type_declaration_with_attrs(tdcl, arena);

    let (structure_items, signature_items) = match &tdcl.ptype_kind {
        TypeKind::Ptype_record(labels) => {
            generate_record_accessors_and_sigs(labels, &core_type_with_attrs, loc, arena)
        }
        TypeKind::Ptype_variant(constructors) => {
            generate_variant_accessors_and_sigs(constructors, tdcl, &core_type_with_attrs, loc, arena)
        }
        _ => return None, // Abstract or open types not supported
    };

    if structure_items.is_empty() {
        return None;
    }

    // Create: include (struct <structure_items> end : sig <signature_items> end)
    let inner_mod = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_structure(structure_items),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    let sig_mod_type = current::ModuleType {
        pmty_desc: current::ModuleTypeDesc::Pmty_signature(signature_items),
        pmty_loc: loc,
        pmty_attributes: vec![],
    };

    let constrained_mod = ModuleExpr {
        pmod_desc: ModuleExprDesc::Pmod_constraint(Box::new(inner_mod), Box::new(sig_mod_type)),
        pmod_loc: loc,
        pmod_attributes: vec![],
    };

    let include_decl = current::IncludeDeclaration {
        pincl_mod: constrained_mod,
        pincl_loc: loc,
        pincl_attributes: vec![],
    };

    Some(StructureItem {
        pstr_desc: StructureItemDesc::Pstr_include(include_decl),
        pstr_loc: loc,
    })
}

/// Generate accessor structure items and signature items for record fields
fn generate_record_accessors_and_sigs(
    labels: &[current::LabelDeclaration],
    core_type: &CoreType,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> (Vec<StructureItem>, Vec<SignatureItem>) {
    let mut structure_items = Vec::new();
    let mut signature_items = Vec::new();

    for label in labels {
        // Structure item: let fieldName = (param: t) => param.fieldName
        let param_str = arena.intern_string("param");
        let param_pat = Pattern {
            ppat_desc: PatternDesc::Ppat_constraint(
                Box::new(Pattern {
                    ppat_desc: PatternDesc::Ppat_var(Located { txt: param_str, loc }),
                    ppat_loc: loc,
                    ppat_attributes: vec![],
                }),
                core_type.clone(),
            ),
            ppat_loc: loc,
            ppat_attributes: vec![],
        };

        let field_access = Expression {
            pexp_desc: ExpressionDesc::Pexp_field(
                Box::new(Expression {
                    pexp_desc: ExpressionDesc::Pexp_ident(Located {
                        txt: arena.push_longident(Longident::Lident(param_str)),
                        loc,
                    }),
                    pexp_loc: loc,
                    pexp_attributes: vec![],
                }),
                Located {
                    txt: arena.push_longident(Longident::Lident(label.pld_name.txt)),
                    loc,
                },
            ),
            pexp_loc: loc,
            pexp_attributes: vec![],
        };

        let fun_expr = Expression {
            pexp_desc: ExpressionDesc::Pexp_fun {
                arg_label: ArgLabel::Nolabel,
                default: None,
                lhs: param_pat,
                rhs: Box::new(field_access),
                is_async: false,
                arity: arena.static_arity_1(),
            },
            pexp_loc: loc,
            pexp_attributes: vec![],
        };

        let binding = ValueBinding {
            pvb_pat: Pattern {
                ppat_desc: PatternDesc::Ppat_var(Located {
                    txt: label.pld_name.txt,
                    loc: label.pld_name.loc,
                }),
                ppat_loc: loc,
                ppat_attributes: vec![],
            },
            pvb_expr: fun_expr,
            pvb_attributes: vec![],
            pvb_loc: loc,
        };

        structure_items.push(StructureItem {
            pstr_desc: StructureItemDesc::Pstr_value(RecFlag::Nonrecursive, vec![binding]),
            pstr_loc: loc,
        });

        // Signature item: val fieldName: t -> fieldType
        let arrow_type = CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow {
                arg: Box::new(TypeArg {
                    attrs: vec![],
                    lbl: ArgLabel::Nolabel,
                    typ: core_type.clone(),
                }),
                ret: Box::new(label.pld_type.clone()),
                arity: arena.static_arity_1(),
            },
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };

        let val_desc = ValueDescription {
            pval_name: Located {
                txt: label.pld_name.txt,
                loc: label.pld_name.loc,
            },
            pval_type: arrow_type,
            pval_prim: vec![],
            pval_attributes: vec![],
            pval_loc: loc,
        };

        signature_items.push(SignatureItem {
            psig_desc: SignatureItemDesc::Psig_value(val_desc),
            psig_loc: loc,
        });
    }

    (structure_items, signature_items)
}

/// Generate accessor structure items and signature items for variant constructors
fn generate_variant_accessors_and_sigs(
    constructors: &[current::ConstructorDeclaration],
    _tdcl: &TypeDeclaration,
    core_type: &CoreType,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> (Vec<StructureItem>, Vec<SignatureItem>) {
    let mut structure_items = Vec::new();
    let mut signature_items = Vec::new();

    for ctor in constructors {
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

        let annotate_type = match &ctor.pcd_res {
            Some(t) => t.clone(),
            None => core_type.clone(),
        };

        if arity == 0 {
            // No args: let ctorName = CtorName : t
            let ctor_expr = Expression {
                pexp_desc: ExpressionDesc::Pexp_constraint(
                    Box::new(Expression {
                        pexp_desc: ExpressionDesc::Pexp_construct(
                            Located {
                                txt: arena.push_longident(Longident::Lident(ctor.pcd_name.txt)),
                                loc,
                            },
                            None,
                        ),
                        pexp_loc: loc,
                        pexp_attributes: vec![],
                    }),
                    annotate_type.clone(),
                ),
                pexp_loc: loc,
                pexp_attributes: vec![],
            };

            let binding = ValueBinding {
                pvb_pat: Pattern {
                    ppat_desc: PatternDesc::Ppat_var(Located { txt: fn_name_idx, loc }),
                    ppat_loc: loc,
                    ppat_attributes: vec![],
                },
                pvb_expr: ctor_expr,
                pvb_attributes: vec![],
                pvb_loc: loc,
            };

            structure_items.push(StructureItem {
                pstr_desc: StructureItemDesc::Pstr_value(RecFlag::Nonrecursive, vec![binding]),
                pstr_loc: loc,
            });

            // val ctorName: t
            let val_desc = ValueDescription {
                pval_name: Located { txt: fn_name_idx, loc },
                pval_type: annotate_type,
                pval_prim: vec![],
                pval_attributes: vec![],
                pval_loc: loc,
            };

            signature_items.push(SignatureItem {
                psig_desc: SignatureItemDesc::Psig_value(val_desc),
                psig_loc: loc,
            });
        } else {
            // Has args: let ctorName = (p0, p1, ...) => CtorName(p0, p1, ...)
            let params: Vec<StrIdx> = (0..arity)
                .map(|i| arena.intern_string(&format!("param_{}", i)))
                .collect();

            // Build constructor argument (single or tuple)
            let ctor_arg = if arity == 1 {
                Expression {
                    pexp_desc: ExpressionDesc::Pexp_ident(Located {
                        txt: arena.push_longident(Longident::Lident(params[0])),
                        loc,
                    }),
                    pexp_loc: loc,
                    pexp_attributes: vec![],
                }
            } else {
                Expression {
                    pexp_desc: ExpressionDesc::Pexp_tuple(
                        params.iter().map(|&p| Expression {
                            pexp_desc: ExpressionDesc::Pexp_ident(Located {
                                txt: arena.push_longident(Longident::Lident(p)),
                                loc,
                            }),
                            pexp_loc: loc,
                            pexp_attributes: vec![],
                        }).collect()
                    ),
                    pexp_loc: loc,
                    pexp_attributes: vec![],
                }
            };

            let ctor_expr = Expression {
                pexp_desc: ExpressionDesc::Pexp_constraint(
                    Box::new(Expression {
                        pexp_desc: ExpressionDesc::Pexp_construct(
                            Located {
                                txt: arena.push_longident(Longident::Lident(ctor.pcd_name.txt)),
                                loc,
                            },
                            Some(Box::new(ctor_arg)),
                        ),
                        pexp_loc: loc,
                        pexp_attributes: vec![],
                    }),
                    annotate_type.clone(),
                ),
                pexp_loc: loc,
                pexp_attributes: vec![],
            };

            // Wrap with function parameters (fold right)
            let body = params.iter().rev().fold(ctor_expr, |acc, &param| {
                Expression {
                    pexp_desc: ExpressionDesc::Pexp_fun {
                        arg_label: ArgLabel::Nolabel,
                        default: None,
                        lhs: Pattern {
                            ppat_desc: PatternDesc::Ppat_var(Located { txt: param, loc }),
                            ppat_loc: loc,
                            ppat_attributes: vec![],
                        },
                        rhs: Box::new(acc),
                        is_async: false,
                        arity: arena.push_arity(None),
                    },
                    pexp_loc: loc,
                    pexp_attributes: vec![],
                }
            });

            // Set outermost arity
            let final_expr = set_outermost_arity(body, arity as i32, arena);

            let binding = ValueBinding {
                pvb_pat: Pattern {
                    ppat_desc: PatternDesc::Ppat_var(Located { txt: fn_name_idx, loc }),
                    ppat_loc: loc,
                    ppat_attributes: vec![],
                },
                pvb_expr: final_expr,
                pvb_attributes: vec![],
                pvb_loc: loc,
            };

            structure_items.push(StructureItem {
                pstr_desc: StructureItemDesc::Pstr_value(RecFlag::Nonrecursive, vec![binding]),
                pstr_loc: loc,
            });

            // Signature: val ctorName: arg0 -> arg1 -> ... -> t
            let pcd_args = match &ctor.pcd_args {
                ConstructorArguments::Pcstr_tuple(args) => args.clone(),
                _ => vec![],
            };
            let args: Vec<TypeArg> = pcd_args.iter().map(|arg_type| TypeArg {
                attrs: vec![],
                lbl: ArgLabel::Nolabel,
                typ: arg_type.clone(),
            }).collect();
            let arrow_type = make_arrows(args, annotate_type, loc, arena);

            let val_desc = ValueDescription {
                pval_name: Located { txt: fn_name_idx, loc },
                pval_type: arrow_type,
                pval_prim: vec![],
                pval_attributes: vec![],
                pval_loc: loc,
            };

            signature_items.push(SignatureItem {
                psig_desc: SignatureItemDesc::Psig_value(val_desc),
                psig_loc: loc,
            });
        }
    }

    (structure_items, signature_items)
}

/// Create an arrow type from a list of arguments and return type
fn make_arrows(args: Vec<TypeArg>, ret: CoreType, loc: LocIdx, arena: &mut ParseArena) -> CoreType {
    if args.is_empty() {
        return ret;
    }

    // OCaml's Typ.arrows creates arity = Some(list_length)
    let arity = arena.push_arity(Some(args.len() as i32));

    // Build right-to-left (fold_right pattern)
    let mut result = ret;
    for arg in args.into_iter().rev() {
        result = CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_arrow {
                arg: Box::new(arg),
                ret: Box::new(result),
                arity,
            },
            ptyp_loc: loc,
            ptyp_attributes: vec![],
        };
    }
    result
}

/// Generate a core type with attributes (including @deriving)
/// This matches OCaml's Ast_derive_util.core_type_of_type_declaration
fn core_type_of_type_declaration_with_attrs(tdcl: &TypeDeclaration, arena: &mut ParseArena) -> CoreType {
    let loc = tdcl.ptype_loc;
    let name_lid = arena.push_longident(Longident::Lident(tdcl.ptype_name.txt));

    let type_args: Vec<CoreType> = tdcl.ptype_params.iter().map(|(core_type, _)| {
        core_type.clone()
    }).collect();

    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr(
            Located { txt: name_lid, loc },
            type_args,
        ),
        ptyp_loc: loc,
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
pub fn rewrite_structure(structure: &[StructureItem], arena: &mut ParseArena) -> Vec<StructureItem> {
    // Context for tracking already-created module type names (per-structure scope)
    let mut await_context = std::collections::HashSet::new();
    let mut result = Vec::new();

    for item in structure {
        match &item.pstr_desc {
            StructureItemDesc::Pstr_value(_rec_flag, bindings) => {
                // Spelunk through the ORIGINAL bindings to find await module types
                // (before expression rewriting transforms them)
                let module_type_decls =
                    spelunk_value_bindings_for_await_module_types(bindings, &mut await_context, arena);

                // Add hoisted module type declarations first
                result.extend(module_type_decls);

                // Then process the structure item normally
                result.extend(rewrite_structure_item(item, arena));
            }
            _ => {
                // Non-Pstr_value items: just process normally
                result.extend(rewrite_structure_item(item, arena));
            }
        }
    }

    result
}

/// Apply built-in PPX transformations to a signature
pub fn rewrite_signature(signature: &[SignatureItem], arena: &mut ParseArena) -> Vec<SignatureItem> {
    signature
        .iter()
        .map(|item| rewrite_signature_item(item, arena))
        .collect()
}

/// Rewrite a structure item, potentially returning multiple items for @deriving.
fn rewrite_structure_item(item: &StructureItem, arena: &mut ParseArena) -> Vec<StructureItem> {
    match &item.pstr_desc {
        StructureItemDesc::Pstr_primitive(vd) => {
            if is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
                // OCaml rewrites attributes (e.g. "js" -> "*j" in strings) before
                // encoding the external (ast_external.ml line 59).
                let rewritten_attrs = rewrite_attributes(&vd.pval_attributes, arena);
                // Rewrite the type to transform string delimiters in @as attributes
                let rewritten_type = rewrite_core_type(&vd.pval_type, arena);
                let rewritten_vd = ValueDescription {
                    pval_name: vd.pval_name.clone(),
                    pval_type: rewritten_type.clone(),
                    pval_prim: vd.pval_prim.clone(),
                    pval_attributes: rewritten_attrs,
                    pval_loc: vd.pval_loc,
                };

                // Check if FFI has relative paths before encoding
                // (need to build FFI type to check, same as encode_external does)
                let no_inline = check_external_relative(&rewritten_vd, arena);

                let encoded = encode_external(&rewritten_vd, arena);
                // OCaml's FFI processing (ast_external_process.ml handle_attributes)
                // reconstructs the arrow type with ptyp_loc = pval_loc.
                // For @obj externals, also reconstructs Ptyp_any -> Ptyp_object.
                let pval_type = process_obj_type(&rewritten_type, vd.pval_loc, &vd.pval_attributes, arena);
                let external_result = StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_primitive(ValueDescription {
                        pval_prim: encoded.pval_prim,
                        pval_attributes: encoded.pval_attributes.clone(),
                        pval_name: vd.pval_name.clone(),
                        pval_type: pval_type.clone(),
                        pval_loc: vd.pval_loc,
                    }),
                    pstr_loc: item.pstr_loc,
                };

                if no_inline {
                    // Wrap in Pstr_include to prevent cross-module inlining
                    // of relative path externals (ast_external.ml lines 78-98)
                    let loc = vd.pval_loc;
                    vec![StructureItem {
                        pstr_desc: StructureItemDesc::Pstr_include(IncludeDeclaration {
                            pincl_mod: ModuleExpr {
                                pmod_desc: ModuleExprDesc::Pmod_constraint(
                                    Box::new(ModuleExpr {
                                        pmod_desc: ModuleExprDesc::Pmod_structure(vec![
                                            external_result,
                                        ]),
                                        pmod_loc: loc,
                                        pmod_attributes: vec![],
                                    }),
                                    Box::new(ModuleType {
                                        pmty_desc: ModuleTypeDesc::Pmty_signature(vec![
                                            SignatureItem {
                                                psig_desc: SignatureItemDesc::Psig_value(
                                                    ValueDescription {
                                                        pval_name: vd.pval_name.clone(),
                                                        pval_type,
                                                        pval_prim: vec![],
                                                        pval_attributes: encoded.pval_attributes,
                                                        pval_loc: vd.pval_loc,
                                                    },
                                                ),
                                                psig_loc: loc,
                                            },
                                        ]),
                                        pmty_loc: loc,
                                        pmty_attributes: vec![],
                                    }),
                                ),
                                pmod_loc: loc,
                                pmod_attributes: vec![],
                            },
                            pincl_loc: loc,
                            pincl_attributes: vec![],
                        }),
                        pstr_loc: item.pstr_loc,
                    }]
                } else {
                    vec![external_result]
                }
            } else {
                // Non-ReScript externals still need attribute and type rewriting
                // (e.g. "js" -> "*j" in @ocaml.doc string delimiters and @as attributes in types)
                vec![StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_primitive(ValueDescription {
                        pval_name: vd.pval_name.clone(),
                        pval_type: rewrite_core_type(&vd.pval_type, arena),
                        pval_prim: vd.pval_prim.clone(),
                        pval_attributes: rewrite_attributes(&vd.pval_attributes, arena),
                        pval_loc: vd.pval_loc,
                    }),
                    pstr_loc: item.pstr_loc,
                }]
            }
        }
        // Handle value bindings - need to rewrite expressions and patterns
        // Also handle @inline transformation
        StructureItemDesc::Pstr_value(rec_flag, bindings) => {
            // Check for @inline on a single non-recursive let binding
            if *rec_flag == RecFlag::Nonrecursive && bindings.len() == 1 {
                let vb = &bindings[0];
                // Check if pattern is a simple variable
                if let PatternDesc::Ppat_var(pval_name) = &vb.pvb_pat.ppat_desc {
                    // Rewrite expression first to get string transformation
                    let pvb_expr = rewrite_expression(&vb.pvb_expr, arena);

                    // Check for @inline attribute
                    if has_inline_attr(&vb.pvb_attributes, arena) {
                        // Transform based on the expression type
                        if let Some(prim_item) = transform_inline_binding(
                            pval_name,
                            &pvb_expr,
                            vb.pvb_loc,
                            item.pstr_loc,
                            arena,
                        ) {
                            return vec![prim_item];
                        }
                    }

                    // No @inline or couldn't transform - return rewritten binding
                    return vec![StructureItem {
                        pstr_desc: StructureItemDesc::Pstr_value(
                            *rec_flag,
                            vec![ValueBinding {
                                pvb_expr,
                                pvb_pat: rewrite_pattern(&vb.pvb_pat, arena),
                                pvb_attributes: rewrite_attributes(&vb.pvb_attributes, arena),
                                pvb_loc: vb.pvb_loc,
                            }],
                        ),
                        pstr_loc: item.pstr_loc,
                    }];
                }
            }

            // Default case: rewrite all bindings (with tuple flattening)
            let new_bindings = flatten_value_bindings(bindings, arena);
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_value(*rec_flag, new_bindings),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Handle eval expressions
        StructureItemDesc::Pstr_eval(expr, attrs) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_eval(
                rewrite_expression(expr, arena),
                rewrite_attributes(attrs, arena),
            ),
            pstr_loc: item.pstr_loc,
        }],
        // Module - check for @res.await transformation first, then recurse
        StructureItemDesc::Pstr_module(mb) => {
            // Check for module-level await: module M = @res.await ME
            if let Some((module_type_decl, transformed_mb)) = transform_module_await(mb, item.pstr_loc, arena) {
                vec![module_type_decl, transformed_mb]
            } else {
                // Normal case - just recurse into module structure
                vec![StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_module(current::ModuleBinding {
                        pmb_name: mb.pmb_name.clone(),
                        pmb_expr: rewrite_module_expr(&mb.pmb_expr, arena),
                        pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena),
                        pmb_loc: mb.pmb_loc,
                    }),
                    pstr_loc: item.pstr_loc,
                }]
            }
        }
        // Recursive modules
        StructureItemDesc::Pstr_recmodule(mbs) => {
            let new_mbs = mbs
                .iter()
                .map(|mb| current::ModuleBinding {
                    pmb_name: mb.pmb_name.clone(),
                    pmb_expr: rewrite_module_expr(&mb.pmb_expr, arena),
                    pmb_attributes: rewrite_attributes(&mb.pmb_attributes, arena),
                    pmb_loc: mb.pmb_loc,
                })
                .collect();
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_recmodule(new_mbs),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Include - recurse into module expression
        StructureItemDesc::Pstr_include(incl) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_include(current::IncludeDeclaration {
                pincl_mod: rewrite_module_expr(&incl.pincl_mod, arena),
                pincl_loc: incl.pincl_loc,
                pincl_attributes: rewrite_attributes(&incl.pincl_attributes, arena),
            }),
            pstr_loc: item.pstr_loc,
        }],
        // Handle structure-level extensions (%%raw, %%private)
        StructureItemDesc::Pstr_extension(ext, attrs) => {
            let (ext_name, payload) = ext;
            let name = arena.get_string(ext_name.txt);
            if name == "raw" {
                // %%raw("...") -> Pstr_eval with local_external_apply using #raw_stmt
                // OCaml: loc comes from {txt = "raw"; loc} - extension identifier location
                vec![handle_raw_structure(item, payload, arena, ext_name.loc)]
            } else if name == "private" {
                // %%private(let x = ...) -> module local_N = { let x = ... } ; open! local_N
                handle_private_extension(payload, item.pstr_loc, arena)
            } else {
                // Rewrite payload for string transformation
                vec![StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_extension(
                        (ext_name.clone(), rewrite_payload(payload, arena)),
                        rewrite_attributes(attrs, arena),
                    ),
                    pstr_loc: item.pstr_loc,
                }]
            }
        }
        // Handle floating attributes (@@attr) - need to transform strings in payload
        StructureItemDesc::Pstr_attribute(attr) => {
            vec![StructureItem {
                pstr_desc: StructureItemDesc::Pstr_attribute(rewrite_attribute(attr, arena)),
                pstr_loc: item.pstr_loc,
            }]
        }
        // Handle type declarations with @deriving
        StructureItemDesc::Pstr_type(rec_flag, tdcls) => {
            handle_deriving_type(item, *rec_flag, tdcls, arena)
        }
        // Handle open - rewrite attributes
        StructureItemDesc::Pstr_open(od) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_open(current::OpenDescription {
                popen_lid: od.popen_lid.clone(),
                popen_override: od.popen_override,
                popen_loc: od.popen_loc,
                popen_attributes: rewrite_attributes(&od.popen_attributes, arena),
            }),
            pstr_loc: item.pstr_loc,
        }],
        // Handle modtype - rewrite attributes
        StructureItemDesc::Pstr_modtype(mtd) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_modtype(current::ModuleTypeDeclaration {
                pmtd_name: mtd.pmtd_name.clone(),
                pmtd_type: mtd.pmtd_type.as_ref().map(|mt| rewrite_module_type(mt, arena)),
                pmtd_attributes: rewrite_attributes(&mtd.pmtd_attributes, arena),
                pmtd_loc: mtd.pmtd_loc,
            }),
            pstr_loc: item.pstr_loc,
        }],
        // Handle exception - rewrite attributes
        StructureItemDesc::Pstr_exception(ec) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_exception(current::ExtensionConstructor {
                pext_name: ec.pext_name.clone(),
                pext_kind: ec.pext_kind.clone(),
                pext_loc: ec.pext_loc,
                pext_attributes: rewrite_attributes(&ec.pext_attributes, arena),
            }),
            pstr_loc: item.pstr_loc,
        }],
        // Handle type extension - rewrite attributes
        StructureItemDesc::Pstr_typext(te) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_typext(current::TypeExtension {
                ptyext_path: te.ptyext_path.clone(),
                ptyext_params: te.ptyext_params.clone(),
                ptyext_constructors: te
                    .ptyext_constructors
                    .iter()
                    .map(|ec| current::ExtensionConstructor {
                        pext_name: ec.pext_name.clone(),
                        pext_kind: ec.pext_kind.clone(),
                        pext_loc: ec.pext_loc,
                        pext_attributes: rewrite_attributes(&ec.pext_attributes, arena),
                    })
                    .collect(),
                ptyext_private: te.ptyext_private,
                ptyext_attributes: rewrite_attributes(&te.ptyext_attributes, arena),
            }),
            pstr_loc: item.pstr_loc,
        }],
    }
}

/// Rewrite a module expression, recursing into structure
fn rewrite_module_expr(
    mod_expr: &current::ModuleExpr,
    arena: &mut ParseArena,
) -> current::ModuleExpr {
    let new_desc = match &mod_expr.pmod_desc {
        current::ModuleExprDesc::Pmod_structure(items) => {
            current::ModuleExprDesc::Pmod_structure(
                items
                    .iter()
                    .flat_map(|item| rewrite_structure_item(item, arena))
                    .collect(),
            )
        }
        current::ModuleExprDesc::Pmod_functor(param, mod_type, body) => {
            current::ModuleExprDesc::Pmod_functor(
                param.clone(),
                mod_type.as_ref().map(|mt| Box::new(rewrite_module_type(mt, arena))),
                Box::new(rewrite_module_expr(body, arena)),
            )
        }
        current::ModuleExprDesc::Pmod_apply(m1, m2) => current::ModuleExprDesc::Pmod_apply(
            Box::new(rewrite_module_expr(m1, arena)),
            Box::new(rewrite_module_expr(m2, arena)),
        ),
        current::ModuleExprDesc::Pmod_constraint(m, mt) => {
            current::ModuleExprDesc::Pmod_constraint(
                Box::new(rewrite_module_expr(m, arena)),
                Box::new(rewrite_module_type(mt, arena)),
            )
        }
        // Handle module extension - rewrite payload
        current::ModuleExprDesc::Pmod_extension(ext) => {
            let (ext_name, payload) = ext;
            current::ModuleExprDesc::Pmod_extension((
                ext_name.clone(),
                rewrite_payload(payload, arena),
            ))
        }
        // Ident, unpack - just clone
        _ => return mod_expr.clone(),
    };

    current::ModuleExpr {
        pmod_desc: new_desc,
        pmod_loc: mod_expr.pmod_loc,
        pmod_attributes: rewrite_attributes(&mod_expr.pmod_attributes, arena),
    }
}

/// Rewrite a module type, recursing into signature and nested module types
fn rewrite_module_type(
    mod_type: &current::ModuleType,
    arena: &mut ParseArena,
) -> current::ModuleType {
    let new_desc = match &mod_type.pmty_desc {
        current::ModuleTypeDesc::Pmty_signature(items) => {
            current::ModuleTypeDesc::Pmty_signature(
                items.iter().map(|item| rewrite_signature_item(item, arena)).collect(),
            )
        }
        current::ModuleTypeDesc::Pmty_functor(name, param_type, result_type) => {
            current::ModuleTypeDesc::Pmty_functor(
                name.clone(),
                param_type.as_ref().map(|pt| Box::new(rewrite_module_type(pt, arena))),
                Box::new(rewrite_module_type(result_type, arena)),
            )
        }
        current::ModuleTypeDesc::Pmty_with(mt, constraints) => {
            current::ModuleTypeDesc::Pmty_with(
                Box::new(rewrite_module_type(mt, arena)),
                constraints.clone(),
            )
        }
        current::ModuleTypeDesc::Pmty_typeof(me) => {
            current::ModuleTypeDesc::Pmty_typeof(Box::new(rewrite_module_expr(me, arena)))
        }
        current::ModuleTypeDesc::Pmty_extension(ext) => {
            let (ext_name, payload) = ext;
            current::ModuleTypeDesc::Pmty_extension((
                ext_name.clone(),
                rewrite_payload(payload, arena),
            ))
        }
        // Ident, Alias - just return as-is (will be wrapped with rewritten attributes)
        _ => return current::ModuleType {
            pmty_desc: mod_type.pmty_desc.clone(),
            pmty_loc: mod_type.pmty_loc,
            pmty_attributes: rewrite_attributes(&mod_type.pmty_attributes, arena),
        },
    };

    current::ModuleType {
        pmty_desc: new_desc,
        pmty_loc: mod_type.pmty_loc,
        pmty_attributes: rewrite_attributes(&mod_type.pmty_attributes, arena),
    }
}

fn rewrite_signature_item(item: &SignatureItem, arena: &mut ParseArena) -> SignatureItem {
    match &item.psig_desc {
        SignatureItemDesc::Psig_value(vd) => {
            // OCaml rewrites attributes (e.g. "js" -> "*j" in strings) before
            // encoding the external (ast_external.ml handle_external_in_sig,
            // bs_builtin_ppx.ml line 409).
            let rewritten_attrs = rewrite_attributes(&vd.pval_attributes, arena);
            if is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
                let rewritten_vd = ValueDescription {
                    pval_name: vd.pval_name.clone(),
                    pval_type: vd.pval_type.clone(),
                    pval_prim: vd.pval_prim.clone(),
                    pval_attributes: rewritten_attrs,
                    pval_loc: vd.pval_loc,
                };
                let encoded = encode_external(&rewritten_vd, arena);
                // OCaml's FFI processing reconstructs the arrow type with ptyp_loc = pval_loc
                // For @obj externals, also reconstructs Ptyp_any -> Ptyp_object.
                let pval_type = process_obj_type(&vd.pval_type, vd.pval_loc, &vd.pval_attributes, arena);
                SignatureItem {
                    psig_desc: SignatureItemDesc::Psig_value(ValueDescription {
                        pval_prim: encoded.pval_prim,
                        pval_attributes: encoded.pval_attributes,
                        pval_name: vd.pval_name.clone(),
                        pval_type,
                        pval_loc: vd.pval_loc,
                    }),
                    psig_loc: item.psig_loc,
                }
            } else if let Some(inline_vd) = transform_inline_sig_value(vd, arena) {
                // Handle @inline("value") let x: t in signature
                // (bs_builtin_ppx.ml line 413-478)
                SignatureItem {
                    psig_desc: SignatureItemDesc::Psig_value(inline_vd),
                    psig_loc: item.psig_loc,
                }
            } else {
                SignatureItem {
                    psig_desc: SignatureItemDesc::Psig_value(ValueDescription {
                        pval_name: vd.pval_name.clone(),
                        pval_type: vd.pval_type.clone(),
                        pval_prim: vd.pval_prim.clone(),
                        pval_attributes: rewritten_attrs,
                        pval_loc: vd.pval_loc,
                    }),
                    psig_loc: item.psig_loc,
                }
            }
        }
        // Handle floating attributes (@@attr) - need to transform strings in payload
        SignatureItemDesc::Psig_attribute(attr) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_attribute(rewrite_attribute(attr, arena)),
            psig_loc: item.psig_loc,
        },
        // Handle extensions - need to transform strings in payload
        SignatureItemDesc::Psig_extension(ext, attrs) => {
            let (ext_name, payload) = ext;
            SignatureItem {
                psig_desc: SignatureItemDesc::Psig_extension(
                    (ext_name.clone(), rewrite_payload(payload, arena)),
                    rewrite_attributes(attrs, arena),
                ),
                psig_loc: item.psig_loc,
            }
        }
        // Handle open - rewrite attributes
        SignatureItemDesc::Psig_open(od) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_open(current::OpenDescription {
                popen_lid: od.popen_lid.clone(),
                popen_override: od.popen_override,
                popen_loc: od.popen_loc,
                popen_attributes: rewrite_attributes(&od.popen_attributes, arena),
            }),
            psig_loc: item.psig_loc,
        },
        // Handle modtype - rewrite attributes and module type
        SignatureItemDesc::Psig_modtype(mtd) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_modtype(current::ModuleTypeDeclaration {
                pmtd_name: mtd.pmtd_name.clone(),
                pmtd_type: mtd.pmtd_type.as_ref().map(|mt| rewrite_module_type(mt, arena)),
                pmtd_attributes: rewrite_attributes(&mtd.pmtd_attributes, arena),
                pmtd_loc: mtd.pmtd_loc,
            }),
            psig_loc: item.psig_loc,
        },
        // Handle exception - rewrite attributes
        SignatureItemDesc::Psig_exception(ec) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_exception(current::ExtensionConstructor {
                pext_name: ec.pext_name.clone(),
                pext_kind: ec.pext_kind.clone(),
                pext_loc: ec.pext_loc,
                pext_attributes: rewrite_attributes(&ec.pext_attributes, arena),
            }),
            psig_loc: item.psig_loc,
        },
        // Handle type extension - rewrite attributes
        SignatureItemDesc::Psig_typext(te) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_typext(current::TypeExtension {
                ptyext_path: te.ptyext_path.clone(),
                ptyext_params: te.ptyext_params.clone(),
                ptyext_constructors: te
                    .ptyext_constructors
                    .iter()
                    .map(|ec| current::ExtensionConstructor {
                        pext_name: ec.pext_name.clone(),
                        pext_kind: ec.pext_kind.clone(),
                        pext_loc: ec.pext_loc,
                        pext_attributes: rewrite_attributes(&ec.pext_attributes, arena),
                    })
                    .collect(),
                ptyext_private: te.ptyext_private,
                ptyext_attributes: rewrite_attributes(&te.ptyext_attributes, arena),
            }),
            psig_loc: item.psig_loc,
        },
        // Handle type declarations - rewrite attributes (including constructor/label attributes)
        SignatureItemDesc::Psig_type(rec_flag, tdcls) => {
            let rewritten_tdcls: Vec<TypeDeclaration> = tdcls
                .iter()
                .map(|tdcl| rewrite_type_declaration(tdcl, arena))
                .collect();
            SignatureItem {
                psig_desc: SignatureItemDesc::Psig_type(*rec_flag, rewritten_tdcls),
                psig_loc: item.psig_loc,
            }
        }
        // Handle include - recurse into module type
        SignatureItemDesc::Psig_include(incl) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_include(current::IncludeDescription {
                pincl_mod: rewrite_module_type(&incl.pincl_mod, arena),
                pincl_loc: incl.pincl_loc,
                pincl_attributes: rewrite_attributes(&incl.pincl_attributes, arena),
            }),
            psig_loc: item.psig_loc,
        },
        // Handle module - recurse into module type
        SignatureItemDesc::Psig_module(md) => SignatureItem {
            psig_desc: SignatureItemDesc::Psig_module(current::ModuleDeclaration {
                pmd_name: md.pmd_name.clone(),
                pmd_type: rewrite_module_type(&md.pmd_type, arena),
                pmd_attributes: rewrite_attributes(&md.pmd_attributes, arena),
                pmd_loc: md.pmd_loc,
            }),
            psig_loc: item.psig_loc,
        },
        // Handle recursive modules - recurse into module types
        SignatureItemDesc::Psig_recmodule(mds) => {
            let new_mds = mds
                .iter()
                .map(|md| current::ModuleDeclaration {
                    pmd_name: md.pmd_name.clone(),
                    pmd_type: rewrite_module_type(&md.pmd_type, arena),
                    pmd_attributes: rewrite_attributes(&md.pmd_attributes, arena),
                    pmd_loc: md.pmd_loc,
                })
                .collect();
            SignatureItem {
                psig_desc: SignatureItemDesc::Psig_recmodule(new_mds),
                psig_loc: item.psig_loc,
            }
        }
        // Any remaining cases - just clone (no string constants to transform)
        _ => item.clone(),
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
        assert!(prims_to_be_encoded(&["console.log".to_string()]));
        assert!(!prims_to_be_encoded(&["#foo".to_string()]));
        assert!(!prims_to_be_encoded(&[]));
    }
}
