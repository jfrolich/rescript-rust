//! FFI type definitions for external declarations.
//!
//! This module defines the types used to encode FFI metadata for ReScript externals.
//! The encoded FFI information is marshaled and stored as the second string in
//! `pval_prim` of value descriptions.
//!
//! These types mirror those in `compiler/frontend/external_ffi_types.ml` and
//! `compiler/frontend/external_arg_spec.ml`.

use super::marshal::MarshalWriter;
use super::serialize::Marshal;

// ========== External arg spec types ==========

/// String delimiter type for constant arguments
#[derive(Clone, Debug, PartialEq)]
pub enum Delim {
    DNone,
    DStarJ,
    DNoQuotes,
    DBackQuotes,
}

impl Marshal for Delim {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            Delim::DNone => w.write_int(0),
            Delim::DStarJ => w.write_int(1),
            Delim::DNoQuotes => w.write_int(2),
            Delim::DBackQuotes => w.write_int(3),
        }
    }
}

/// Constant argument value
#[derive(Clone, Debug, PartialEq)]
pub enum Cst {
    ArgIntLit(i64),
    ArgStringLit(String, Delim),
}

impl Marshal for Cst {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            Cst::ArgIntLit(i) => {
                w.write_block_header(0, 1);
                w.write_int(*i);
            }
            Cst::ArgStringLit(s, delim) => {
                w.write_block_header(1, 2);
                w.write_str(s);
                delim.marshal(w);
            }
        }
    }
}

/// Label type for argument labels (without name)
#[derive(Clone, Debug, PartialEq)]
pub enum LabelNoname {
    ArgLabel,
    ArgEmpty,
    ArgOptional,
}

impl Marshal for LabelNoname {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            LabelNoname::ArgLabel => w.write_int(0),
            LabelNoname::ArgEmpty => w.write_int(1),
            LabelNoname::ArgOptional => w.write_int(2),
        }
    }
}

/// Label type for object arguments
#[derive(Clone, Debug, PartialEq)]
pub enum Label {
    ObjEmpty,
    ObjLabel {
        name: String,
    },
    ObjOptional {
        name: String,
        for_sure_no_nested_option: bool,
    },
}

impl Marshal for Label {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            Label::ObjEmpty => w.write_int(0),
            Label::ObjLabel { name } => {
                w.write_block_header(0, 1);
                w.write_string(name.as_bytes());
            }
            Label::ObjOptional {
                name,
                for_sure_no_nested_option,
            } => {
                w.write_block_header(1, 2);
                w.write_string(name.as_bytes());
                w.write_int(if *for_sure_no_nested_option { 1 } else { 0 });
            }
        }
    }
}

/// Attribute type for arguments
#[derive(Clone, Debug, PartialEq)]
pub enum Attr {
    PolyVarString {
        descr: Vec<(String, String)>,
    },
    PolyVar {
        descr: Option<Vec<(String, String)>>,
    },
    Int(Vec<(String, i64)>),
    ArgCst(Cst),
    ExternUnit,
    Nothing,
    Ignore,
    Unwrap,
}

impl Marshal for Attr {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            Attr::PolyVarString { descr } => {
                w.write_block_header(0, 1);
                marshal_string_pair_list(w, descr);
            }
            Attr::PolyVar { descr } => {
                w.write_block_header(1, 1);
                match descr {
                    None => w.write_int(0),
                    Some(list) => {
                        w.write_block_header(0, 1);
                        marshal_string_pair_list(w, list);
                    }
                }
            }
            Attr::Int(list) => {
                w.write_block_header(2, 1);
                marshal_list(w, list, |w, (s, i)| {
                    w.write_block_header(0, 2);
                    w.write_string(s.as_bytes());
                    w.write_int(*i);
                });
            }
            Attr::ArgCst(cst) => {
                w.write_block_header(3, 1);
                cst.marshal(w);
            }
            // OCaml constant constructors are numbered separately from block constructors.
            // Extern_unit is constant #0, Nothing is #1, Ignore is #2, Unwrap is #3.
            Attr::ExternUnit => w.write_int(0),
            Attr::Nothing => w.write_int(1),
            Attr::Ignore => w.write_int(2),
            Attr::Unwrap => w.write_int(3),
        }
    }
}

/// Parameter specification
#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub arg_type: Attr,
    pub arg_label: LabelNoname,
}

impl Marshal for Param {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 2);
        self.arg_type.marshal(w);
        self.arg_label.marshal(w);
    }
}

/// Object parameter specification
#[derive(Clone, Debug, PartialEq)]
pub struct ObjParam {
    pub obj_arg_type: Attr,
    pub obj_arg_label: Label,
}

impl Marshal for ObjParam {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 2);
        self.obj_arg_type.marshal(w);
        self.obj_arg_label.marshal(w);
    }
}

// ========== External FFI types ==========

/// Module bind name for imports
#[derive(Clone, Debug, PartialEq)]
pub enum ModuleBindName {
    PhintName(String),
    PhintNothing,
}

impl Marshal for ModuleBindName {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            ModuleBindName::PhintName(s) => {
                w.write_block_header(0, 1);
                w.write_string(s.as_bytes());
            }
            ModuleBindName::PhintNothing => w.write_int(0),
        }
    }
}

/// Import attributes (key-value pairs)
pub type ImportAttributes = Vec<(String, String)>;

/// External module name specification
#[derive(Clone, Debug, PartialEq)]
pub struct ExternalModuleName {
    pub bundle: String,
    pub module_bind_name: ModuleBindName,
    pub import_attributes: Option<ImportAttributes>,
}

impl Marshal for ExternalModuleName {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 3);
        w.write_string(self.bundle.as_bytes());
        self.module_bind_name.marshal(w);
        match &self.import_attributes {
            None => w.write_int(0),
            Some(attrs) => {
                // Import attributes are stored as a hashtable in OCaml
                // For marshal format, we need to match OCaml's Hashtbl serialization
                w.write_block_header(0, 1);
                marshal_hashtbl(w, attrs);
            }
        }
    }
}

/// External specification (the FFI binding type)
#[derive(Clone, Debug, PartialEq)]
pub enum ExternalSpec {
    JsVar {
        name: String,
        external_module_name: Option<ExternalModuleName>,
        scopes: Vec<String>,
    },
    JsModuleAsVar(ExternalModuleName),
    JsModuleAsFn {
        external_module_name: ExternalModuleName,
        splice: bool,
    },
    JsModuleAsClass(ExternalModuleName),
    JsCall {
        name: String,
        external_module_name: Option<ExternalModuleName>,
        splice: bool,
        scopes: Vec<String>,
    },
    JsSend {
        name: String,
        splice: bool,
        js_send_scopes: Vec<String>,
    },
    JsNew {
        name: String,
        external_module_name: Option<ExternalModuleName>,
        splice: bool,
        scopes: Vec<String>,
    },
    JsSet {
        js_set_name: String,
        js_set_scopes: Vec<String>,
    },
    JsGet {
        js_get_name: String,
        js_get_scopes: Vec<String>,
    },
    JsGetIndex {
        js_get_index_scopes: Vec<String>,
    },
    JsSetIndex {
        js_set_index_scopes: Vec<String>,
    },
}

impl Marshal for ExternalSpec {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            ExternalSpec::JsVar {
                name,
                external_module_name,
                scopes,
            } => {
                w.write_block_header(0, 3);
                w.write_string(name.as_bytes());
                marshal_option(w, external_module_name, |w, m| m.marshal(w));
                marshal_string_list(w, scopes);
            }
            ExternalSpec::JsModuleAsVar(m) => {
                w.write_block_header(1, 1);
                m.marshal(w);
            }
            ExternalSpec::JsModuleAsFn {
                external_module_name,
                splice,
            } => {
                w.write_block_header(2, 2);
                external_module_name.marshal(w);
                w.write_int(if *splice { 1 } else { 0 });
            }
            ExternalSpec::JsModuleAsClass(m) => {
                w.write_block_header(3, 1);
                m.marshal(w);
            }
            ExternalSpec::JsCall {
                name,
                external_module_name,
                splice,
                scopes,
            } => {
                w.write_block_header(4, 4);
                w.write_string(name.as_bytes());
                marshal_option(w, external_module_name, |w, m| m.marshal(w));
                w.write_int(if *splice { 1 } else { 0 });
                marshal_string_list(w, scopes);
            }
            ExternalSpec::JsSend {
                name,
                splice,
                js_send_scopes,
            } => {
                w.write_block_header(5, 3);
                w.write_string(name.as_bytes());
                w.write_int(if *splice { 1 } else { 0 });
                marshal_string_list(w, js_send_scopes);
            }
            ExternalSpec::JsNew {
                name,
                external_module_name,
                splice,
                scopes,
            } => {
                w.write_block_header(6, 4);
                w.write_string(name.as_bytes());
                marshal_option(w, external_module_name, |w, m| m.marshal(w));
                w.write_int(if *splice { 1 } else { 0 });
                marshal_string_list(w, scopes);
            }
            ExternalSpec::JsSet {
                js_set_name,
                js_set_scopes,
            } => {
                w.write_block_header(7, 2);
                w.write_string(js_set_name.as_bytes());
                marshal_string_list(w, js_set_scopes);
            }
            ExternalSpec::JsGet {
                js_get_name,
                js_get_scopes,
            } => {
                w.write_block_header(8, 2);
                w.write_string(js_get_name.as_bytes());
                marshal_string_list(w, js_get_scopes);
            }
            ExternalSpec::JsGetIndex {
                js_get_index_scopes,
            } => {
                w.write_block_header(9, 1);
                marshal_string_list(w, js_get_index_scopes);
            }
            ExternalSpec::JsSetIndex {
                js_set_index_scopes,
            } => {
                w.write_block_header(10, 1);
                marshal_string_list(w, js_set_index_scopes);
            }
        }
    }
}

/// Return wrapper specification
#[derive(Clone, Debug, PartialEq)]
pub enum ReturnWrapper {
    ReturnUnset,
    ReturnIdentity,
    ReturnNullToOpt,
    ReturnNullUndefinedToOpt,
    ReturnReplacedWithUnit,
}

impl Marshal for ReturnWrapper {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            ReturnWrapper::ReturnUnset => w.write_int(0),
            ReturnWrapper::ReturnIdentity => w.write_int(1),
            ReturnWrapper::ReturnNullToOpt => w.write_int(2),
            ReturnWrapper::ReturnNullUndefinedToOpt => w.write_int(3),
            ReturnWrapper::ReturnReplacedWithUnit => w.write_int(4),
        }
    }
}

/// Parameters representation
#[derive(Clone, Debug, PartialEq)]
pub enum Params {
    Params(Vec<Param>),
    ParamNumber(i64),
}

impl Marshal for Params {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            Params::Params(params) => {
                w.write_block_header(0, 1);
                marshal_list(w, params, |w, p| p.marshal(w));
            }
            Params::ParamNumber(n) => {
                w.write_block_header(1, 1);
                w.write_int(*n);
            }
        }
    }
}

/// Main FFI type
#[derive(Clone, Debug, PartialEq)]
pub enum FfiType {
    FfiBs {
        params: Params,
        return_wrapper: ReturnWrapper,
        external_spec: ExternalSpec,
    },
    FfiObjCreate(Vec<ObjParam>),
    FfiInlineConst(LamConstant),
    FfiNormal,
}

impl Marshal for FfiType {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            FfiType::FfiBs {
                params,
                return_wrapper,
                external_spec,
            } => {
                w.write_block_header(0, 3);
                params.marshal(w);
                return_wrapper.marshal(w);
                external_spec.marshal(w);
            }
            FfiType::FfiObjCreate(params) => {
                w.write_block_header(1, 1);
                marshal_list(w, params, |w, p| p.marshal(w));
            }
            FfiType::FfiInlineConst(constant) => {
                w.write_block_header(2, 1);
                constant.marshal(w);
            }
            FfiType::FfiNormal => w.write_int(0),
        }
    }
}

// ========== Lam_constant types ==========

/// Constructor tag for constants
#[derive(Clone, Debug, PartialEq)]
pub struct ConstructorTag {
    pub cstr_name: Tag,
    pub const_: i64,
    pub non_const: i64,
}

impl Marshal for ConstructorTag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 3);
        self.cstr_name.marshal(w);
        w.write_int(self.const_);
        w.write_int(self.non_const);
    }
}

/// Tag type (from Ast_untagged_variants)
#[derive(Clone, Debug, PartialEq)]
pub struct Tag {
    pub name: String,
}

impl Marshal for Tag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 1);
        w.write_string(self.name.as_bytes());
    }
}

/// Pointer info for constants
#[derive(Clone, Debug, PartialEq)]
pub enum PointerInfo {
    None,
    PtConstructor(ConstructorTag),
    PtAssertfalse,
    Some(String),
}

impl Marshal for PointerInfo {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            PointerInfo::None => w.write_int(0),
            PointerInfo::PtConstructor(tag) => {
                w.write_block_header(0, 1);
                tag.marshal(w);
            }
            PointerInfo::PtAssertfalse => w.write_int(1),
            PointerInfo::Some(s) => {
                w.write_block_header(1, 1);
                w.write_string(s.as_bytes());
            }
        }
    }
}

/// Tag info (from Lambda module)
#[derive(Clone, Debug, PartialEq)]
pub enum TagInfo {
    Blk(Option<Vec<String>>),
    PolyvarTag { name: String, num: i64 },
}

impl Marshal for TagInfo {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            TagInfo::Blk(fields) => {
                w.write_block_header(0, 1);
                marshal_option(w, fields, |w, f| marshal_string_list(w, f));
            }
            TagInfo::PolyvarTag { name, num } => {
                w.write_block_header(1, 2);
                w.write_string(name.as_bytes());
                w.write_int(*num);
            }
        }
    }
}

/// Lambda constant type
#[derive(Clone, Debug, PartialEq)]
pub enum LamConstant {
    ConstJsNull,
    ConstJsUndefined { is_unit: bool },
    ConstJsTrue,
    ConstJsFalse,
    ConstInt { i: i32, comment: PointerInfo },
    ConstChar(i64),
    ConstString { s: String, delim: Option<Delim> },
    ConstFloat(String),
    ConstBigint(bool, String),
    ConstPointer(String),
    ConstBlock(i64, TagInfo, Vec<LamConstant>),
    ConstSome(Box<LamConstant>),
    ConstModuleAlias,
}

impl Marshal for LamConstant {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            LamConstant::ConstJsNull => w.write_int(0),
            LamConstant::ConstJsUndefined { is_unit } => {
                w.write_block_header(0, 1);
                w.write_int(if *is_unit { 1 } else { 0 });
            }
            LamConstant::ConstJsTrue => w.write_int(1),
            LamConstant::ConstJsFalse => w.write_int(2),
            LamConstant::ConstInt { i, comment } => {
                w.write_block_header(1, 2);
                w.write_custom_int32(*i);
                comment.marshal(w);
            }
            LamConstant::ConstChar(c) => {
                w.write_block_header(2, 1);
                w.write_int(*c);
            }
            LamConstant::ConstString { s, delim } => {
                w.write_block_header(3, 2);
                w.write_str(s);
                marshal_option(w, delim, |w, d| d.marshal(w));
            }
            LamConstant::ConstFloat(f) => {
                w.write_block_header(4, 1);
                w.write_string(f.as_bytes());
            }
            LamConstant::ConstBigint(sign, s) => {
                w.write_block_header(5, 2);
                w.write_int(if *sign { 1 } else { 0 });
                w.write_string(s.as_bytes());
            }
            LamConstant::ConstPointer(s) => {
                w.write_block_header(6, 1);
                w.write_string(s.as_bytes());
            }
            LamConstant::ConstBlock(tag, info, constants) => {
                w.write_block_header(7, 3);
                w.write_int(*tag);
                info.marshal(w);
                marshal_list(w, constants, |w, c| c.marshal(w));
            }
            LamConstant::ConstSome(c) => {
                w.write_block_header(8, 1);
                c.marshal(w);
            }
            LamConstant::ConstModuleAlias => w.write_int(3),
        }
    }
}

// ========== Helper functions ==========

fn marshal_option<T>(
    w: &mut MarshalWriter<'_>,
    opt: &Option<T>,
    f: impl FnOnce(&mut MarshalWriter<'_>, &T),
) {
    match opt {
        None => w.write_int(0),
        Some(val) => {
            w.write_block_header(0, 1);
            f(w, val);
        }
    }
}

/// Marshal a list of (string, string) pairs with intra-tuple sharing.
///
/// When the two strings in a pair are equal (tag == name, i.e., no @as attribute),
/// OCaml shares them because the same string pointer is used for both fields.
/// We replicate this by writing the first string, recording its object index,
/// then writing a shared reference if the second string is equal.
fn marshal_string_pair_list(w: &mut MarshalWriter<'_>, list: &[(String, String)]) {
    if list.is_empty() {
        w.write_int(0);
        return;
    }

    for (i, (a, b)) in list.iter().enumerate() {
        w.write_block_header(0, 2); // cons cell

        // Write the pair block
        w.write_block_header(0, 2);

        // Record object index before writing first string
        let first_obj_idx = w.obj_counter();
        w.write_string(a.as_bytes());

        // If b == a, write shared reference; otherwise write the string
        if b == a {
            // Distance = current_counter - first_obj_idx
            let d = w.obj_counter() - first_obj_idx;
            w.write_shared_ref(d);
        } else {
            w.write_string(b.as_bytes());
        }

        if i == list.len() - 1 {
            w.write_int(0); // nil tail
        }
    }
}

fn marshal_list<T>(w: &mut MarshalWriter<'_>, list: &[T], f: impl Fn(&mut MarshalWriter<'_>, &T)) {
    // OCaml lists are encoded as linked cons cells
    // [] is int 0
    // [a; b; c] is Block(0, [a, Block(0, [b, Block(0, [c, int 0])])])
    //
    // Since marshal is a streaming format, we write head-to-tail:
    // 1. Write BLOCK(0,2) header for first cons cell
    // 2. Write element a
    // 3. Write BLOCK(0,2) header for second cons cell (this IS the tail of first)
    // 4. Write element b
    // 5. ... and so on
    // 6. Write INT(0) for nil at the end
    if list.is_empty() {
        w.write_int(0);
        return;
    }

    for (i, item) in list.iter().enumerate() {
        w.write_block_header(0, 2); // cons cell
        f(w, item);
        if i == list.len() - 1 {
            w.write_int(0); // nil tail
        }
        // Otherwise the next iteration's block_header IS the tail
    }
}

fn marshal_string_list(w: &mut MarshalWriter<'_>, list: &[String]) {
    if list.is_empty() {
        w.write_int(0);
        return;
    }

    // Build list from end
    fn build_list(w: &mut MarshalWriter<'_>, list: &[String], idx: usize) {
        if idx >= list.len() {
            w.write_int(0); // nil
        } else {
            w.write_block_header(0, 2);
            w.write_string(list[idx].as_bytes());
            build_list(w, list, idx + 1);
        }
    }

    build_list(w, list, 0);
}

fn ocaml_hashtbl_power_2_above(mut x: usize, n: usize) -> usize {
    while x < n {
        if x > (isize::MAX as usize / 2) {
            break;
        }
        x *= 2;
    }
    x
}

fn ocaml_hash_mix_uint32(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h = h.rotate_left(13);
    h.wrapping_mul(5).wrapping_add(0xe6546b64)
}

fn ocaml_hash_final_mix(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h
}

fn ocaml_hashtbl_hash_string(s: &str) -> u32 {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut h = 0u32;
    let mut i = 0usize;

    while i + 4 <= len {
        let w = u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        h = ocaml_hash_mix_uint32(h, w);
        i += 4;
    }

    let rem = len & 3;
    if rem != 0 {
        let mut w = 0u32;
        if rem >= 3 {
            w |= (bytes[i + 2] as u32) << 16;
        }
        if rem >= 2 {
            w |= (bytes[i + 1] as u32) << 8;
        }
        w |= bytes[i] as u32;
        h = ocaml_hash_mix_uint32(h, w);
    }

    h ^= len as u32;
    ocaml_hash_final_mix(h) & 0x3fff_ffff
}

fn rehash_ocaml_string_hashtbl(
    old_buckets: &[Vec<(String, String)>],
) -> Vec<Vec<(String, String)>> {
    let mut new_buckets = vec![Vec::new(); old_buckets.len() * 2];
    for bucket in old_buckets {
        for (key, value) in bucket {
            let idx = (ocaml_hashtbl_hash_string(key) as usize) & (new_buckets.len() - 1);
            // OCaml resize keeps per-bucket traversal order by appending to the tail.
            new_buckets[idx].push((key.clone(), value.clone()));
        }
    }
    new_buckets
}

fn marshal_ocaml_bucketlist(w: &mut MarshalWriter, bucket: &[(String, String)], idx: usize) {
    if idx >= bucket.len() {
        // Empty
        w.write_int(0);
        return;
    }

    // Cons { key; data; next } with tag 0 and 3 fields.
    w.write_block_header(0, 3);
    w.write_string(bucket[idx].0.as_bytes());
    w.write_string(bucket[idx].1.as_bytes());
    marshal_ocaml_bucketlist(w, bucket, idx + 1);
}

fn marshal_hashtbl(w: &mut MarshalWriter, items: &[(String, String)]) {
    // OCaml Hashtbl.t fields:
    // { size; data: bucketlist array; seed; initial_size }
    // external_ffi_types.ml creates the table with Hashtbl.create (List.length attrs)
    // and fills it with Hashtbl.replace in source order.
    let initial_size = ocaml_hashtbl_power_2_above(16, items.len());
    let mut buckets: Vec<Vec<(String, String)>> = vec![Vec::new(); initial_size];
    let mut size = 0usize;

    for (key, value) in items {
        let bucket_idx = (ocaml_hashtbl_hash_string(key) as usize) & (buckets.len() - 1);
        let mut replaced = false;
        for (existing_key, existing_value) in &mut buckets[bucket_idx] {
            if existing_key == key {
                *existing_key = key.clone();
                *existing_value = value.clone();
                replaced = true;
                break;
            }
        }
        if !replaced {
            // OCaml Hashtbl.replace inserts at bucket head when key is absent.
            buckets[bucket_idx].insert(0, (key.clone(), value.clone()));
            size += 1;
            if size > (buckets.len() << 1) {
                buckets = rehash_ocaml_string_hashtbl(&buckets);
            }
        }
    }

    w.write_block_header(0, 4);
    w.write_int(size as i64);

    w.write_block_header(0, buckets.len());
    for bucket in &buckets {
        marshal_ocaml_bucketlist(w, bucket, 0);
    }

    // external_ffi_types uses non-randomized Hashtbl.create in compiler process.
    w.write_int(0); // seed
    w.write_int(initial_size as i64);
}

// ========== Encoding function ==========

/// Encode FFI type to a marshaled byte array (for pval_prim[1])
///
/// Returns the marshaled data as a String using Latin-1 encoding, where each
/// byte (0x00-0xFF) becomes the corresponding Unicode code point (U+0000-U+00FF).
/// This matches how source files are read (Latin-1) and ensures the bytes survive
/// the `chars().map(|c| c as u8)` conversion used for output.
pub fn encode_ffi_type(ffi: &FfiType) -> String {
    let mut w = MarshalWriter::new();
    ffi.marshal(&mut w);

    // Convert each byte to its corresponding Latin-1 character (Unicode U+0000 to U+00FF)
    // This creates valid UTF-8 where:
    // - Bytes 0x00-0x7F: single-byte UTF-8 (same as ASCII)
    // - Bytes 0x80-0xFF: two-byte UTF-8 (0xC2 0x80 to 0xC3 0xBF)
    // When `chars().map(|c| c as u8)` is called later, each char is truncated back
    // to the original byte value.
    w.finish().iter().map(|&b| char::from(b)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_ffi_encoding() {
        // Test encoding a simple Js_call FFI
        let ffi = FfiType::FfiBs {
            params: Params::ParamNumber(1),
            return_wrapper: ReturnWrapper::ReturnUnset,
            external_spec: ExternalSpec::JsCall {
                name: "console.log".to_string(),
                external_module_name: None,
                splice: false,
                scopes: vec![],
            },
        };

        let encoded = encode_ffi_type(&ffi);

        // Check it starts with marshal magic
        let bytes: Vec<u8> = encoded.chars().map(|c| c as u8).collect();
        assert_eq!(&bytes[0..4], &[0x84, 0x95, 0xA6, 0xBE]);
    }

    #[test]
    fn test_import_attributes_hashtbl_matches_ocaml_marshal() {
        let mut w = MarshalWriter::new();
        let attrs = vec![
            ("type".to_string(), "json".to_string()),
            ("some-identifier".to_string(), "yep".to_string()),
        ];

        marshal_hashtbl(&mut w, &attrs);
        let bytes = w.finish();

        // Generated from OCaml 5.3:
        // let tbl = Hashtbl.create 2 in
        // Hashtbl.replace tbl "type" "json";
        // Hashtbl.replace tbl "some-identifier" "yep";
        // Marshal.to_string tbl []
        let expected = vec![
            0x84, 0x95, 0xA6, 0xBE, 0x00, 0x00, 0x00, 0x39, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00,
            0x00, 0x2B, 0x00, 0x00, 0x00, 0x27, 0xC0, 0x42, 0x08, 0x00, 0x00, 0x43, 0x00, 0x40,
            0x40, 0x40, 0xB0, 0x24, 0x74, 0x79, 0x70, 0x65, 0x24, 0x6A, 0x73, 0x6F, 0x6E, 0x40,
            0xB0, 0x2F, 0x73, 0x6F, 0x6D, 0x65, 0x2D, 0x69, 0x64, 0x65, 0x6E, 0x74, 0x69, 0x66,
            0x69, 0x65, 0x72, 0x23, 0x79, 0x65, 0x70, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40,
            0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x50,
        ];
        assert_eq!(bytes, expected);
    }
}
