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
use crate::location::Location;
use crate::parse_arena::{LidentIdx, Located, LocIdx, ParseArena};
use crate::parser::ast::{
    self as current, ArgLabel, Arity, Attribute, Case, Constant, CoreType, CoreTypeDesc,
    Expression, ExpressionDesc, Label, ModuleExpr, ModuleExprDesc, Pattern, PatternDesc, Payload,
    RecFlag, SignatureItem, SignatureItemDesc, StructureItem, StructureItemDesc,
    TypeArg, ValueBinding, ValueDescription,
};
use crate::parser::longident::Longident;

use super::ffi_types::{
    encode_ffi_type, Delim, ExternalSpec, FfiType, LamConstant, Params,
    PointerInfo, ReturnWrapper,
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

/// Count the arity of a function type
fn count_type_arity(typ: &CoreType, arena: &mut ParseArena) -> usize {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow { arg, ret, arity: _ } => {
            // Count this argument plus any more in the return type
            let is_unit = is_unit_type(&arg.typ, arena);
            let base = if is_unit { 0 } else { 1 };
            base + count_type_arity(ret, arena)
        }
        _ => 0,
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

/// Parse external attributes to determine FFI encoding details
#[derive(Debug)]
struct ExternalDesc {
    val_name: Option<String>,
    module_name: Option<String>,
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
            module_name: None,
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

fn parse_external_attrs(attrs: &[Attribute], prim_name: &str, arena: &mut ParseArena) -> ExternalDesc {
    let mut desc = ExternalDesc::default();

    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        match name {
            "val" => {
                desc.val_name = Some(get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()));
            }
            "module" => {
                desc.module_name = get_payload_string(payload, arena);
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
                if let Some(scope_str) = get_payload_string(payload, arena) {
                    desc.scopes.push(scope_str);
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
        && desc.send_name.is_none()
        && desc.new_name.is_none()
        && desc.get_name.is_none()
        && desc.set_name.is_none()
        && !desc.get_index
        && !desc.set_index
        && desc.module_name.is_none()
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
                if let ExpressionDesc::Pexp_constant(current::Constant::String(s, _)) = &expr.pexp_desc {
                    return Some(s.clone());
                }
            }
            None
        }
        _ => None,
    }
}

/// Build FFI type from external description and type info
fn build_ffi_type(desc: &ExternalDesc, prim_name: &str, arity: usize, result_is_unit: bool) -> FfiType {
    // Determine return wrapper
    let return_wrapper = if result_is_unit && matches!(desc.return_wrapper, ReturnWrapper::ReturnUnset) {
        ReturnWrapper::ReturnReplacedWithUnit
    } else {
        desc.return_wrapper.clone()
    };

    // Build params - simple case: just use ParamNumber for arity
    let params = Params::ParamNumber(arity as i64);

    // Determine external spec based on attributes
    let external_spec = if desc.get_index {
        ExternalSpec::JsGetIndex {
            js_get_index_scopes: desc.scopes.clone(),
        }
    } else if desc.set_index {
        ExternalSpec::JsSetIndex {
            js_set_index_scopes: desc.scopes.clone(),
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
            external_module_name: None, // TODO: handle module
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
    } else if arity == 0 {
        // No args = Js_var
        ExternalSpec::JsVar {
            name: desc.val_name.as_ref().unwrap_or(&prim_name.to_string()).clone(),
            external_module_name: None, // TODO: handle module
            scopes: desc.scopes.clone(),
        }
    } else {
        // Default: Js_call
        let name = desc.call_name.as_ref()
            .or(desc.val_name.as_ref())
            .cloned()
            .unwrap_or_else(|| prim_name.to_string());
        ExternalSpec::JsCall {
            name,
            external_module_name: None, // TODO: handle module
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

    // Parse attributes
    let desc = parse_external_attrs(&vd.pval_attributes, prim_name, arena);

    // Calculate arity from type
    let arity = count_type_arity(&vd.pval_type, arena);

    // Check if result is unit
    let result_is_unit = is_unit_type(get_final_result_type(&vd.pval_type), arena);

    // Build FFI type
    let ffi = build_ffi_type(&desc, prim_name, arity, result_is_unit);

    // Encode FFI type
    let encoded = encode_ffi_type(&ffi);

    // Filter out consumed FFI attributes
    let filtered_attrs = filter_ffi_attributes(&vd.pval_attributes, arena);

    EncodedExternal {
        pval_prim: vec![prim_name.to_string(), encoded],
        pval_attributes: filtered_attrs,
    }
}

/// Encode inline string constant
pub fn inline_string_primitive(s: &str, delim: Option<&str>) -> Vec<String> {
    let delim = delim.map(|d| match d {
        "j" => Delim::DStarJ,
        "" => Delim::DNone,
        _ => Delim::DNone, // TODO: handle other delimiters
    });

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

    match name {
        "raw" => handle_raw(expr, payload, arena, "#raw_expr"),
        _ => expr.clone(),
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
) -> Expression {
    // Extract the string expression from the payload
    let str_exp = match payload {
        Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(e, _) = &items[0].pstr_desc {
                if let ExpressionDesc::Pexp_constant(Constant::String(s, _)) = &e.pexp_desc {
                    // Create a new string expression with delimiter stripped
                    // (OCaml strips the delimiter when transforming %raw)
                    Expression {
                        pexp_desc: ExpressionDesc::Pexp_constant(Constant::String(
                            s.clone(),
                            None, // Strip delimiter
                        )),
                        pexp_loc: e.pexp_loc,
                        pexp_attributes: e.pexp_attributes.clone(),
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

    let loc = expr.pexp_loc;

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
            arity: Arity::default(),
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

    let loc = item.pstr_loc;
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
            arity: Arity::default(),
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
        pexp_attributes: vec![],
    };

    // Wrap in Pstr_eval
    StructureItem {
        pstr_desc: StructureItemDesc::Pstr_eval(letmodule_expr, vec![]),
        pstr_loc: item.pstr_loc,
    }
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
                // UTF-8 multi-byte character - copy all bytes
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
                for j in start..std::cmp::min(start + width, bytes.len()) {
                    buf.push(bytes[j] as char);
                }
                i = std::cmp::min(start + width, bytes.len());
            }
        }
    }

    buf
}

/// Transform string constant expression with delimiter.
/// Implements OCaml's Ast_utf8_string_interp.transform_exp.
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
        // Unrecognized delimiter - return unchanged
        expr.clone()
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

/// Rewrite a pattern, transforming string constants
fn rewrite_pattern(pat: &Pattern) -> Pattern {
    match &pat.ppat_desc {
        PatternDesc::Ppat_constant(Constant::String(s, Some(delim))) => {
            transform_string_pat(pat, s, delim)
        }
        // For other patterns, just clone (no recursive rewriting needed for now)
        _ => pat.clone(),
    }
}

/// Rewrite an expression, desugaring pipe operators
fn rewrite_expression(expr: &Expression, arena: &mut ParseArena) -> Expression {
    // Handle string constant transformations first
    if let ExpressionDesc::Pexp_constant(Constant::String(s, Some(delim))) = &expr.pexp_desc {
        return transform_string_exp(expr, s, delim, arena);
    }

    // First check if this is a pipe application
    if let ExpressionDesc::Pexp_apply {
        funct,
        args,
        partial: _,
        transformed_jsx: _,
    } = &expr.pexp_desc
    {
        // Check if this is a pipe: -> with two args
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
                }
            }
        }
    }

    // Not a pipe - recursively rewrite sub-expressions
    rewrite_expression_generic(expr, arena)
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
            return expr.clone();
        }

        ExpressionDesc::Pexp_let(rec_flag, bindings, body) => {
            let new_bindings: Vec<ValueBinding> = bindings
                .iter()
                .map(|vb| ValueBinding {
                    pvb_expr: rewrite_expression(&vb.pvb_expr, arena),
                    pvb_pat: rewrite_pattern(&vb.pvb_pat),
                    pvb_attributes: vb.pvb_attributes.clone(),
                    pvb_loc: vb.pvb_loc,
                })
                .collect();
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
        } => ExpressionDesc::Pexp_fun {
            arg_label: arg_label.clone(),
            default: default.as_ref().map(|e| Box::new(rewrite_expression(e, arena))),
            lhs: rewrite_pattern(lhs),
            rhs: Box::new(rewrite_expression(rhs, arena)),
            arity: *arity,
            is_async: *is_async,
        },

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

        ExpressionDesc::Pexp_match(scrutinee, cases) => ExpressionDesc::Pexp_match(
            Box::new(rewrite_expression(scrutinee, arena)),
            rewrite_cases(cases, arena),
        ),

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
            pat.clone(),
            Box::new(rewrite_expression(e1, arena)),
            Box::new(rewrite_expression(e2, arena)),
            *dir,
            Box::new(rewrite_expression(body, arena)),
        ),

        ExpressionDesc::Pexp_constraint(e, ty) => {
            ExpressionDesc::Pexp_constraint(Box::new(rewrite_expression(e, arena)), ty.clone())
        }

        ExpressionDesc::Pexp_coerce(e, ty1, ty2) => ExpressionDesc::Pexp_coerce(
            Box::new(rewrite_expression(e, arena)),
            ty1.clone(),
            ty2.clone(),
        ),

        ExpressionDesc::Pexp_send(e, method) => {
            ExpressionDesc::Pexp_send(Box::new(rewrite_expression(e, arena)), method.clone())
        }

        ExpressionDesc::Pexp_assert(e) => {
            ExpressionDesc::Pexp_assert(Box::new(rewrite_expression(e, arena)))
        }

        ExpressionDesc::Pexp_await(e) => {
            ExpressionDesc::Pexp_await(Box::new(rewrite_expression(e, arena)))
        }

        ExpressionDesc::Pexp_pack(mod_expr) => {
            // Module expressions - don't recurse for now
            ExpressionDesc::Pexp_pack(mod_expr.clone())
        }

        ExpressionDesc::Pexp_letmodule(name, mod_expr, body) => ExpressionDesc::Pexp_letmodule(
            name.clone(),
            mod_expr.clone(), // Don't recurse into module expressions
            Box::new(rewrite_expression(body, arena)),
        ),

        ExpressionDesc::Pexp_letexception(exn, body) => ExpressionDesc::Pexp_letexception(
            exn.clone(),
            Box::new(rewrite_expression(body, arena)),
        ),

        ExpressionDesc::Pexp_open(override_flag, mod_name, body) => ExpressionDesc::Pexp_open(
            *override_flag,
            mod_name.clone(),
            Box::new(rewrite_expression(body, arena)),
        ),

        ExpressionDesc::Pexp_newtype(name, body) => ExpressionDesc::Pexp_newtype(
            name.clone(),
            Box::new(rewrite_expression(body, arena)),
        ),

        // Extensions - handle %raw, others just clone
        ExpressionDesc::Pexp_extension(ext) => {
            return handle_extension(expr, ext, arena);
        }

        // JSX - just clone
        ExpressionDesc::Pexp_jsx_element(_) => {
            return expr.clone();
        }
    };

    Expression {
        pexp_desc: new_desc,
        pexp_loc: expr.pexp_loc,
        pexp_attributes: expr.pexp_attributes.clone(),
    }
}

/// Rewrite cases for match/try expressions
fn rewrite_cases(cases: &[Case], arena: &mut ParseArena) -> Vec<Case> {
    cases
        .iter()
        .map(|c| Case {
            pc_bar: c.pc_bar,
            pc_lhs: rewrite_pattern(&c.pc_lhs),
            pc_guard: c.pc_guard.as_ref().map(|e| rewrite_expression(e, arena)),
            pc_rhs: rewrite_expression(&c.pc_rhs, arena),
        })
        .collect()
}

// ========== PPX Application ==========

/// Apply built-in PPX transformations to a structure
pub fn rewrite_structure(structure: &[StructureItem], arena: &mut ParseArena) -> Vec<StructureItem> {
    structure
        .iter()
        .map(|item| rewrite_structure_item(item, arena))
        .collect()
}

/// Apply built-in PPX transformations to a signature
pub fn rewrite_signature(signature: &[SignatureItem], arena: &mut ParseArena) -> Vec<SignatureItem> {
    signature
        .iter()
        .map(|item| rewrite_signature_item(item, arena))
        .collect()
}

fn rewrite_structure_item(item: &StructureItem, arena: &mut ParseArena) -> StructureItem {
    match &item.pstr_desc {
        StructureItemDesc::Pstr_primitive(vd) => {
            if is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
                let encoded = encode_external(vd, arena);
                StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_primitive(ValueDescription {
                        pval_prim: encoded.pval_prim,
                        pval_attributes: encoded.pval_attributes,
                        pval_name: vd.pval_name.clone(),
                        pval_type: vd.pval_type.clone(),
                        pval_loc: vd.pval_loc,
                    }),
                    pstr_loc: item.pstr_loc,
                }
            } else {
                item.clone()
            }
        }
        // Handle value bindings - need to rewrite expressions and patterns
        StructureItemDesc::Pstr_value(rec_flag, bindings) => {
            let new_bindings: Vec<ValueBinding> = bindings
                .iter()
                .map(|vb| ValueBinding {
                    pvb_expr: rewrite_expression(&vb.pvb_expr, arena),
                    pvb_pat: rewrite_pattern(&vb.pvb_pat),
                    pvb_attributes: vb.pvb_attributes.clone(),
                    pvb_loc: vb.pvb_loc,
                })
                .collect();
            StructureItem {
                pstr_desc: StructureItemDesc::Pstr_value(*rec_flag, new_bindings),
                pstr_loc: item.pstr_loc,
            }
        }
        // Handle eval expressions
        StructureItemDesc::Pstr_eval(expr, attrs) => StructureItem {
            pstr_desc: StructureItemDesc::Pstr_eval(
                rewrite_expression(expr, arena),
                attrs.clone(),
            ),
            pstr_loc: item.pstr_loc,
        },
        // Module - recurse into module structure
        StructureItemDesc::Pstr_module(mb) => StructureItem {
            pstr_desc: StructureItemDesc::Pstr_module(current::ModuleBinding {
                pmb_name: mb.pmb_name.clone(),
                pmb_expr: rewrite_module_expr(&mb.pmb_expr, arena),
                pmb_attributes: mb.pmb_attributes.clone(),
                pmb_loc: mb.pmb_loc,
            }),
            pstr_loc: item.pstr_loc,
        },
        // Recursive modules
        StructureItemDesc::Pstr_recmodule(mbs) => {
            let new_mbs = mbs
                .iter()
                .map(|mb| current::ModuleBinding {
                    pmb_name: mb.pmb_name.clone(),
                    pmb_expr: rewrite_module_expr(&mb.pmb_expr, arena),
                    pmb_attributes: mb.pmb_attributes.clone(),
                    pmb_loc: mb.pmb_loc,
                })
                .collect();
            StructureItem {
                pstr_desc: StructureItemDesc::Pstr_recmodule(new_mbs),
                pstr_loc: item.pstr_loc,
            }
        }
        // Include - recurse into module expression
        StructureItemDesc::Pstr_include(incl) => StructureItem {
            pstr_desc: StructureItemDesc::Pstr_include(current::IncludeDeclaration {
                pincl_mod: rewrite_module_expr(&incl.pincl_mod, arena),
                pincl_loc: incl.pincl_loc,
                pincl_attributes: incl.pincl_attributes.clone(),
            }),
            pstr_loc: item.pstr_loc,
        },
        // Handle structure-level extensions (%%raw)
        StructureItemDesc::Pstr_extension(ext, _attrs) => {
            let (ext_name, payload) = ext;
            let name = arena.get_string(ext_name.txt);
            if name == "raw" {
                // %%raw("...") -> Pstr_eval with local_external_apply using #raw_stmt
                handle_raw_structure(item, payload, arena)
            } else {
                item.clone()
            }
        }
        // Other structure items don't contain expressions that need rewriting
        _ => item.clone(),
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
                    .map(|item| rewrite_structure_item(item, arena))
                    .collect(),
            )
        }
        current::ModuleExprDesc::Pmod_functor(param, mod_type, body) => {
            current::ModuleExprDesc::Pmod_functor(
                param.clone(),
                mod_type.clone(),
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
                mt.clone(),
            )
        }
        // Ident, extension, unpack - just clone
        _ => return mod_expr.clone(),
    };

    current::ModuleExpr {
        pmod_desc: new_desc,
        pmod_loc: mod_expr.pmod_loc,
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    }
}

fn rewrite_signature_item(item: &SignatureItem, arena: &mut ParseArena) -> SignatureItem {
    match &item.psig_desc {
        SignatureItemDesc::Psig_value(vd) => {
            if is_rs_external(&vd.pval_attributes, &vd.pval_prim, arena) {
                let encoded = encode_external(vd, arena);
                SignatureItem {
                    psig_desc: SignatureItemDesc::Psig_value(ValueDescription {
                        pval_prim: encoded.pval_prim,
                        pval_attributes: encoded.pval_attributes,
                        pval_name: vd.pval_name.clone(),
                        pval_type: vd.pval_type.clone(),
                        pval_loc: vd.pval_loc,
                    }),
                    psig_loc: item.psig_loc,
                }
            } else {
                item.clone()
            }
        }
        // TODO: Handle @inline values
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
