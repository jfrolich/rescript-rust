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
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena};
use crate::parser::ast::{
    self as current, Attribute, CoreType, CoreTypeDesc, Expression, ExpressionDesc, SignatureItem,
    SignatureItemDesc, StructureItem, StructureItemDesc, ValueDescription,
};
use crate::parser::longident::Longident;

use super::ffi_types::{
    encode_ffi_type, Delim, ExternalSpec, FfiType, LamConstant, Params, PointerInfo, ReturnWrapper,
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
fn has_external_attrs(attrs: &[Attribute], arena: &ParseArena) -> bool {
    attrs.iter().any(|(attr_name, _payload)| {
        let name = arena.get_string(attr_name.txt);
        EXTERNAL_ATTRS.iter().any(|&ext_attr| name == ext_attr)
    })
}

/// Check if a value description represents a ReScript external
pub fn is_rs_external(attrs: &[Attribute], pval_prim: &[String], arena: &ParseArena) -> bool {
    if pval_prim.is_empty() {
        return false;
    }
    has_external_attrs(attrs, arena) || prims_to_be_encoded(pval_prim)
}

/// Count the arity of a function type
fn count_type_arity(typ: &CoreType, arena: &ParseArena) -> usize {
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
fn is_unit_type(typ: &CoreType, arena: &ParseArena) -> bool {
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

fn parse_external_attrs(attrs: &[Attribute], prim_name: &str, arena: &ParseArena) -> ExternalDesc {
    let mut desc = ExternalDesc::default();

    for (attr_name, payload) in attrs {
        let name = arena.get_string(attr_name.txt);
        match name {
            "val" => {
                desc.val_name = Some(
                    get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()),
                );
            }
            "module" => {
                desc.module_name = get_payload_string(payload, arena);
            }
            "send" => {
                desc.send_name = Some(
                    get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()),
                );
            }
            "new" => {
                desc.new_name = Some(
                    get_payload_string(payload, arena).unwrap_or_else(|| prim_name.to_string()),
                );
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
fn get_payload_string(payload: &current::Payload, arena: &ParseArena) -> Option<String> {
    match payload {
        current::Payload::PStr(items) if items.len() == 1 => {
            if let StructureItemDesc::Pstr_eval(expr, _) = &items[0].pstr_desc {
                if let ExpressionDesc::Pexp_constant(current::Constant::String(s, _)) =
                    &expr.pexp_desc
                {
                    return Some(s.clone());
                }
            }
            None
        }
        _ => None,
    }
}

/// Build FFI type from external description and type info
fn build_ffi_type(
    desc: &ExternalDesc,
    prim_name: &str,
    arity: usize,
    result_is_unit: bool,
) -> FfiType {
    // Determine return wrapper
    let return_wrapper =
        if result_is_unit && matches!(desc.return_wrapper, ReturnWrapper::ReturnUnset) {
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
            name: desc
                .val_name
                .as_ref()
                .unwrap_or(&prim_name.to_string())
                .clone(),
            external_module_name: None, // TODO: handle module
            scopes: desc.scopes.clone(),
        }
    } else {
        // Default: Js_call
        let name = desc
            .call_name
            .as_ref()
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
fn filter_ffi_attributes(attrs: &[Attribute], arena: &ParseArena) -> Vec<Attribute> {
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
pub fn encode_external(vd: &ValueDescription, arena: &ParseArena) -> EncodedExternal {
    // Get the primitive name
    let prim_name = match vd.pval_prim.first() {
        Some(name) => name.as_str(),
        None => {
            return EncodedExternal {
                pval_prim: vd.pval_prim.clone(),
                pval_attributes: vd.pval_attributes.clone(),
            }
        }
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

// ========== PPX Application ==========

/// Apply built-in PPX transformations to a structure
pub fn rewrite_structure(structure: &[StructureItem], arena: &ParseArena) -> Vec<StructureItem> {
    structure
        .iter()
        .map(|item| rewrite_structure_item(item, arena))
        .collect()
}

/// Apply built-in PPX transformations to a signature
pub fn rewrite_signature(signature: &[SignatureItem], arena: &ParseArena) -> Vec<SignatureItem> {
    signature
        .iter()
        .map(|item| rewrite_signature_item(item, arena))
        .collect()
}

fn rewrite_structure_item(item: &StructureItem, arena: &ParseArena) -> StructureItem {
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
        // TODO: Handle @inline let bindings
        _ => item.clone(),
    }
}

fn rewrite_signature_item(item: &SignatureItem, arena: &ParseArena) -> SignatureItem {
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
