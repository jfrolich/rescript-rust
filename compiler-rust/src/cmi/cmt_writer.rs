//! Writers for OCaml-compatible `.cmi`, `.cmt` and `.cmti` artifacts.
//!
//! Editor tooling (the analysis binary, reanalyze, `rescript-tools`) is
//! written in OCaml and reads the compiler artifacts with `input_value`. The
//! in-process Rust build therefore has to emit the exact OCaml heap layout of
//! `Cmi_format.cmi_infos` (compiler/ml/cmi_format.ml:64-72) and
//! `Cmt_format.cmt_infos` (compiler/ml/cmt_format_common.ml:37-52), including
//! `Types` (compiler/ml/types.mli) and `Typedtree` (compiler/ml/typedtree.mli)
//! values.
//!
//! Environments are written as `Env.empty`: OCaml's `save_cmt` replaces every
//! environment by `Env.keep_only_summary` (compiler/ml/cmt_format_common.ml:
//! 83-111), whose lookup tables are empty; consumers only use them for
//! best-effort lookups that fall back when nothing is found.
//!
//! Type nodes are shared by physical identity (`TypeExprRef`), so recursive
//! types marshal as the cyclic graphs OCaml's `output_value` produces.

use crate::fast_hash::AHashMap as HashMap;

use crate::binary_ast::current_marshal::marshal_attributes_plain;
use crate::binary_ast::{Marshal, MarshalWriter};
use crate::ident::Ident;
use crate::intern::StrIdx;
use crate::location::{Location, Position};
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena};
use crate::parser::ast::Attributes;
use crate::parser::longident::Longident;
use crate::types::asttypes::{ArgLabel, MutableFlag, PrivateFlag};
use crate::types::context::TypeContext;
use crate::types::decl::{
    AliasPresence, Attribute, AttributePayload, ConstructorArguments, ConstructorDeclaration,
    ConstructorDescription, ConstructorKind, ExtStatus, ExtensionConstructor, LabelDeclaration,
    LabelDescription, ModtypeDeclaration, ModuleDeclaration, ModuleType, PrimitiveDescription,
    RecStatus, RecordRepresentation, SignatureItem, TypeDeclaration, TypeInlinedType, TypeKind,
    TypeRepresentation, ValueDescription, ValueKind,
};
use crate::types::path::Path;
use crate::types::type_expr::{FieldKind, RowDesc, RowField, TypeDesc, TypeExprRef};
use crate::types::typedtree as tt;
use crate::types::variant_runtime::{
    BlockType, ConstructorCase, ConstructorReference, Instance, Layout, LayoutRef, TagType,
};

/// `Config.cmi_magic_number` (compiler/ext/config.ml:1).
pub const CMI_MAGIC: &[u8; 12] = b"Caml1999I024";
/// `Config.cmt_magic_number` (compiler/ext/config.ml:16).
pub const CMT_MAGIC: &[u8; 12] = b"Caml1999T024";

/// Typed annotations saved in a `.cmt`/`.cmti` (`Cmt_format.binary_annots`).
pub enum BinaryAnnots<'t> {
    /// `Implementation of structure`.
    Implementation(&'t tt::Structure),
    /// `Interface of signature`, with the signature's `sig_type`.
    Interface(&'t tt::TypedSignature, &'t [SignatureItem]),
}

/// Metadata stored next to the typed annotations.
pub struct CmtInfo<'s> {
    /// `cmt_modname`.
    pub modname: &'s str,
    /// `cmt_sourcefile`.
    pub sourcefile: Option<&'s str>,
    /// `cmt_builddir`.
    pub builddir: &'s str,
    /// `cmt_loadpath`.
    pub loadpath: &'s [String],
    /// `cmt_args`.
    pub args: &'s [String],
    /// `cmt_source_digest`.
    pub source_digest: Option<[u8; 16]>,
    /// `cmt_imports`.
    pub imports: &'s [(String, Option<[u8; 16]>)],
    /// The `cmi_crcs` imports of a `.cmi` saved with the `.cmt`.
    pub cmi_imports: &'s [(String, Option<[u8; 16]>)],
}

/// Serialize the `(cmi_name, cmi_sign)` pair of a `.cmi`, prefixed with the
/// magic number, and return it together with its CRC (compiler/ml/
/// cmi_format.ml:78-83: the CRC is the digest of exactly these bytes).
fn cmi_head(
    arena: &ParseArena,
    ctx: &TypeContext,
    modname: &str,
    sign: &[SignatureItem],
) -> (Vec<u8>, [u8; 16]) {
    let mut writer = CmtWriter::new(arena, ctx);
    writer.w.write_block_header(0, 2);
    writer.w.write_str(modname);
    writer.signature(sign);
    let mut content = CMI_MAGIC.to_vec();
    content.extend_from_slice(&writer.w.finish());
    let crc = md5(&content);
    (content, crc)
}

fn cmi_tail(
    arena: &ParseArena,
    ctx: &TypeContext,
    modname: &str,
    crc: [u8; 16],
    imports: &[(String, Option<[u8; 16]>)],
    deprecated: Option<&str>,
) -> Vec<u8> {
    let mut out = Vec::new();
    let mut crcs = CmtWriter::new(arena, ctx);
    let mut all = vec![(modname.to_string(), Some(crc))];
    all.extend(imports.iter().cloned());
    crcs.list(&all, |w, (name, digest)| {
        w.w.write_block_header(0, 2);
        w.w.write_str(name);
        w.digest_option(digest);
    });
    out.extend_from_slice(&crcs.w.finish());
    // cmi_flags: `Deprecated of string` list.
    let mut flags = CmtWriter::new(arena, ctx);
    match deprecated {
        None => flags.w.write_int(0),
        Some(reason) => {
            flags.w.write_block_header(0, 2);
            flags.w.write_block_header(0, 1);
            flags.w.write_str(reason);
            flags.w.write_int(0);
        }
    }
    out.extend_from_slice(&flags.w.finish());
    out
}

/// Bytes of a `.cmi` file (compiler/ml/cmi_format.ml:78-112 `create_cmi`).
pub fn cmi_bytes(
    arena: &ParseArena,
    ctx: &TypeContext,
    modname: &str,
    sign: &[SignatureItem],
    imports: &[(String, Option<[u8; 16]>)],
    deprecated: Option<&str>,
) -> (Vec<u8>, [u8; 16]) {
    let (mut content, crc) = cmi_head(arena, ctx, modname, sign);
    content.extend(cmi_tail(arena, ctx, modname, crc, imports, deprecated));
    (content, crc)
}

/// Bytes of a `.cmt`/`.cmti` file (compiler/ml/cmt_format.ml:17-50
/// `save_cmt`). When `cmi` is given, the file starts with the `.cmi` content,
/// as OCaml does for units whose interface it saves at the same time.
pub fn cmt_bytes(
    arena: &ParseArena,
    ctx: &TypeContext,
    annots: BinaryAnnots<'_>,
    info: &CmtInfo<'_>,
    cmi: Option<(&[SignatureItem], Option<&str>)>,
) -> Vec<u8> {
    let mut out = Vec::new();
    let mut interface_digest = None;
    if let Some((sign, deprecated)) = cmi {
        let (content, crc) = cmi_head(arena, ctx, info.modname, sign);
        out.extend_from_slice(&content);
        out.extend(cmi_tail(
            arena,
            ctx,
            info.modname,
            crc,
            info.cmi_imports,
            deprecated,
        ));
        interface_digest = Some(crc);
    }
    out.extend_from_slice(CMT_MAGIC);
    let mut writer = CmtWriter::new(arena, ctx);
    writer.cmt_infos(annots, info, interface_digest);
    out.extend_from_slice(&writer.w.finish());
    out
}

struct CmtWriter<'a> {
    w: MarshalWriter<'a>,
    arena: &'a ParseArena,
    ctx: &'a TypeContext,
    types: HashMap<TypeExprRef, u32>,
    layouts: HashMap<LayoutRef, u32>,
    env_obj: Option<u32>,
    option_layout: Option<LayoutRef>,
    /// `Types.value_description` of every value bound in the signatures being
    /// written, for `Typedtree.value_description.val_val`.
    values: HashMap<(i32, String), ValueDescription>,
    /// The marshalled file-name string of each file positions name: OCaml's
    /// positions of one file point to one `pos_fname` string (and every
    /// `Location.none` to one "_none_"), which Marshal writes once. Indexed by
    /// file-name id.
    file_name_objs: Vec<Option<u32>>,
    /// Distinct resolved file names, by id.
    file_name_ids: HashMap<String, u32>,
    /// Resolved file-name id of each position file-name string index.
    file_name_id_by_idx: HashMap<u32, u32>,
    /// OCaml's `Ident.t` records are single objects referenced from every
    /// path that names them; Marshal writes each once.
    idents: HashMap<(i32, &'static str, i64), u32>,
    /// Positions of `Types` locations, written once per value, keyed by
    /// (file-name id, line, bol, cnum).
    positions: HashMap<(u32, i32, i32, i32), u32>,
}

impl<'a> CmtWriter<'a> {
    fn new(arena: &'a ParseArena, ctx: &'a TypeContext) -> Self {
        let mut w = MarshalWriter::new();
        w.set_arena(arena);
        CmtWriter {
            w,
            arena,
            ctx,
            types: HashMap::new(),
            layouts: HashMap::new(),
            env_obj: None,
            option_layout: None,
            values: HashMap::new(),
            file_name_objs: Vec::new(),
            file_name_ids: HashMap::default(),
            file_name_id_by_idx: HashMap::default(),
            idents: HashMap::default(),
            positions: HashMap::default(),
        }
    }

    /// Id of a resolved file name, shared by every string index naming it.
    fn file_name_id_of_str(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.file_name_ids.get(name) {
            return id;
        }
        let id = self.file_name_objs.len() as u32;
        self.file_name_objs.push(None);
        self.file_name_ids.insert(name.to_string(), id);
        id
    }

    fn file_name_id(&mut self, idx: StrIdx) -> u32 {
        if let Some(&id) = self.file_name_id_by_idx.get(&idx.raw()) {
            return id;
        }
        let name = self.file_name(idx);
        let id = self.file_name_id_of_str(&name);
        self.file_name_id_by_idx.insert(idx.raw(), id);
        id
    }

    fn file_name_str(&mut self, name: &str) {
        let id = self.file_name_id_of_str(name);
        self.file_name_by_id(id, name);
    }

    fn file_name_by_id(&mut self, id: u32, name: &str) {
        if let Some(obj) = self.file_name_objs[id as usize] {
            self.shared(obj);
            return;
        }
        let obj = self.w.obj_counter();
        self.str(name);
        self.file_name_objs[id as usize] = Some(obj);
    }

    // ------------------------------------------------------------------
    // Primitive values
    // ------------------------------------------------------------------

    fn bool(&mut self, b: bool) {
        self.w.write_int(i64::from(b));
    }

    fn int(&mut self, n: i64) {
        self.w.write_int(n);
    }

    fn str(&mut self, s: &str) {
        self.w.write_str(s);
    }

    /// A zero-sized block is an atom: marshalled without an object slot
    /// (runtime/extern.c `extern_rec`, size 0 case).
    fn atom(&mut self, tag: u8) {
        self.w.write_u8(0x80 + tag);
    }

    fn shared(&mut self, obj: u32) {
        let d = self.w.obj_counter() - obj;
        self.w.write_shared_ref(d);
    }

    fn list<T>(&mut self, items: &[T], mut f: impl FnMut(&mut Self, &T)) {
        for item in items {
            self.w.write_block_header(0, 2);
            f(self, item);
        }
        self.w.write_int(0);
    }

    fn array<T>(&mut self, items: &[T], mut f: impl FnMut(&mut Self, &T)) {
        if items.is_empty() {
            self.atom(0);
            return;
        }
        self.w.write_block_header(0, items.len());
        for item in items {
            f(self, item);
        }
    }

    fn option<T>(&mut self, item: Option<&T>, f: impl FnOnce(&mut Self, &T)) {
        match item {
            None => self.w.write_int(0),
            Some(item) => {
                self.w.write_block_header(0, 1);
                f(self, item);
            }
        }
    }

    fn str_option(&mut self, s: Option<&str>) {
        match s {
            None => self.w.write_int(0),
            Some(s) => {
                self.w.write_block_header(0, 1);
                self.str(s);
            }
        }
    }

    fn digest_option(&mut self, digest: &Option<[u8; 16]>) {
        match digest {
            None => self.w.write_int(0),
            Some(d) => {
                self.w.write_block_header(0, 1);
                self.w.write_string(d);
            }
        }
    }

    fn strings(&mut self, items: &[String]) {
        self.list(items, |w, s| w.str(s));
    }

    // ------------------------------------------------------------------
    // Identifiers, paths, locations
    // ------------------------------------------------------------------

    /// `Ident.t = {stamp; name; flags}` (compiler/ext/ident.ml:18-22).
    fn ident(&mut self, id: &Ident) {
        let mut flags = 0;
        if id.is_global() {
            flags |= 1;
        }
        if id.is_predef_exn() {
            flags |= 2;
        }
        let key = (id.stamp(), id.name(), flags);
        if let Some(&obj) = self.idents.get(&key) {
            self.shared(obj);
            return;
        }
        self.idents.insert(key, self.w.obj_counter());
        self.w.write_block_header(0, 3);
        self.int(i64::from(id.stamp()));
        self.str(id.name());
        self.int(flags);
    }

    fn path(&mut self, p: &Path) {
        match p {
            Path::Pident(id) => {
                self.w.write_block_header(0, 1);
                self.ident(id);
            }
            Path::Pdot(prefix, name, pos) => {
                self.w.write_block_header(1, 3);
                self.path(prefix);
                self.str(name);
                self.int(i64::from(*pos));
            }
            Path::Papply(f, a) => {
                self.w.write_block_header(2, 2);
                self.path(f);
                self.path(a);
            }
        }
    }

    fn longident_component(&self, idx: StrIdx) -> String {
        if let Some(name) = self.ctx.resolve_cmi_longident_component(idx) {
            return name;
        }
        if (idx.raw() as usize) < self.arena.string_count() {
            return self.arena.get_string(idx).to_string();
        }
        self.ctx
            .resolve_any_longident_component(idx)
            .unwrap_or_default()
    }

    fn longident(&mut self, lid: &Longident) {
        match lid {
            Longident::Lident(name) => {
                self.w.write_block_header(0, 1);
                let name = self.longident_component(*name);
                self.str(&name);
            }
            Longident::Ldot(prefix, name) => {
                self.w.write_block_header(1, 2);
                self.longident(prefix);
                let name = self.longident_component(*name);
                self.str(&name);
            }
            Longident::Lapply(f, a) => {
                self.w.write_block_header(2, 2);
                self.longident(f);
                self.longident(a);
            }
        }
    }

    fn loc_idx(&mut self, loc: LocIdx) {
        self.w.write_loc_idx(loc);
    }

    /// `Longident.t loc` from the parse arena.
    fn lid_loc(&mut self, lid: &Located<LidentIdx>) {
        self.w.write_block_header(0, 2);
        self.w.write_lident_idx(lid.txt);
        self.loc_idx(lid.loc);
    }

    /// `string loc` from the parse arena.
    fn str_loc(&mut self, s: &Located<String>) {
        self.w.write_block_header(0, 2);
        self.str(&s.txt);
        self.loc_idx(s.loc);
    }

    fn file_name(&self, idx: StrIdx) -> String {
        if let Some(name) = self.ctx.resolve_cmi_longident_component(idx) {
            return name;
        }
        if (idx.raw() as usize) < self.arena.string_count() {
            return self.arena.get_string(idx).to_string();
        }
        "_none_".to_string()
    }

    fn position(&mut self, pos: &Position) {
        let key = if pos.file_name == StrIdx::default() && pos.line == 0 {
            (self.file_name_id_of_str("_none_"), 1, 0, -1)
        } else {
            (self.file_name_id(pos.file_name), pos.line, pos.bol, pos.cnum)
        };
        if let Some(&obj) = self.positions.get(&key) {
            self.shared(obj);
            return;
        }
        self.positions.insert(key, self.w.obj_counter());
        self.position_block(pos);
    }

    fn position_block(&mut self, pos: &Position) {
        self.w.write_block_header(0, 4);
        if pos.file_name == StrIdx::default() && pos.line == 0 {
            // `Location.none` (compiler/ml/location.ml `in_file "_none_"`).
            self.file_name_str("_none_");
            self.int(1);
            self.int(0);
            self.int(-1);
            return;
        }
        let id = self.file_name_id(pos.file_name);
        if let Some(obj) = self.file_name_objs[id as usize] {
            self.shared(obj);
        } else {
            let name = self.file_name(pos.file_name);
            self.file_name_by_id(id, &name);
        }
        self.int(i64::from(pos.line));
        self.int(i64::from(pos.bol));
        self.int(i64::from(pos.cnum));
    }

    /// A `Location.t` stored in a `Types` value.
    fn location(&mut self, loc: &Location) {
        self.w.write_block_header(0, 3);
        self.position(&loc.loc_start);
        self.position(&loc.loc_end);
        self.bool(loc.loc_ghost);
    }

    fn none_location(&mut self) {
        self.location(&Location::none());
    }

    // ------------------------------------------------------------------
    // Attributes
    // ------------------------------------------------------------------

    fn parsetree_attributes(&mut self, attrs: &Attributes) {
        marshal_attributes_plain(attrs, &mut self.w);
    }

    /// `Parsetree.attribute` rebuilt from the simplified `Types` attribute.
    /// Payloads are re-encoded as the structure the parser produces for them
    /// (a single `Pstr_eval` of a constant or identifier).
    fn types_attributes(&mut self, attrs: &[Attribute]) {
        self.list(attrs, |w, attr| w.types_attribute(attr));
    }

    fn types_attribute(&mut self, attr: &Attribute) {
        self.w.write_block_header(0, 2);
        // string loc
        self.w.write_block_header(0, 2);
        self.str(&attr.attr_name.txt);
        self.location(&attr.attr_name.loc);
        // payload: PStr structure
        self.w.write_block_header(0, 1);
        let loc = attr.attr_loc.clone();
        let expr: Option<Box<dyn FnOnce(&mut Self)>> = match &attr.attr_payload {
            AttributePayload::Empty | AttributePayload::Structure(_) => None,
            AttributePayload::Str(s)
            | AttributePayload::Deprecated { reason: s, .. } => {
                let s = s.clone();
                Some(Box::new(move |w: &mut Self| {
                    // Pexp_constant (Pconst_string (s, None))
                    w.w.write_block_header(1, 1);
                    w.w.write_block_header(2, 2);
                    w.str(&s);
                    w.w.write_int(0);
                }))
            }
            AttributePayload::Int(n) => {
                let s = n.to_string();
                Some(Box::new(move |w: &mut Self| w.pconst_integer(&s, None)))
            }
            AttributePayload::IntLiteral(s) => {
                let s = s.clone();
                Some(Box::new(move |w: &mut Self| w.pconst_integer(&s, None)))
            }
            AttributePayload::BigInt(s) => {
                let s = s.clone();
                Some(Box::new(move |w: &mut Self| w.pconst_integer(&s, Some('n'))))
            }
            AttributePayload::Float(s) => {
                let s = s.clone();
                Some(Box::new(move |w: &mut Self| {
                    w.w.write_block_header(1, 1);
                    w.w.write_block_header(3, 2);
                    w.str(&s);
                    w.w.write_int(0);
                }))
            }
            AttributePayload::Bool(b) => {
                let name = if *b { "true" } else { "false" };
                let loc = loc.clone();
                Some(Box::new(move |w: &mut Self| {
                    // Pexp_construct ({txt = Lident name; loc}, None)
                    w.w.write_block_header(8, 2);
                    w.w.write_block_header(0, 2);
                    w.w.write_block_header(0, 1);
                    w.str(name);
                    w.location(&loc);
                    w.w.write_int(0);
                }))
            }
            AttributePayload::Ident(name) => {
                let name = name.clone();
                let loc = loc.clone();
                Some(Box::new(move |w: &mut Self| {
                    // Pexp_ident {txt = Lident name; loc}
                    w.w.write_block_header(0, 1);
                    w.w.write_block_header(0, 2);
                    w.w.write_block_header(0, 1);
                    w.str(&name);
                    w.location(&loc);
                }))
            }
        };
        match expr {
            None => self.w.write_int(0),
            Some(desc) => {
                // [ {pstr_desc = Pstr_eval (expr, []); pstr_loc} ]
                self.w.write_block_header(0, 2);
                self.w.write_block_header(0, 2);
                self.w.write_block_header(0, 2);
                self.w.write_block_header(0, 3);
                desc(self);
                self.location(&loc);
                self.w.write_int(0);
                self.w.write_int(0);
                self.location(&loc);
                self.w.write_int(0);
            }
        }
    }

    fn pconst_integer(&mut self, s: &str, suffix: Option<char>) {
        self.w.write_block_header(1, 1);
        self.w.write_block_header(0, 2);
        self.str(s);
        match suffix {
            None => self.w.write_int(0),
            Some(c) => {
                self.w.write_block_header(0, 1);
                self.int(c as i64);
            }
        }
    }

    // ------------------------------------------------------------------
    // Types.type_expr
    // ------------------------------------------------------------------

    fn type_expr(&mut self, r: TypeExprRef) {
        if let Some(&obj) = self.types.get(&r) {
            self.shared(obj);
            return;
        }
        self.types.insert(r, self.w.obj_counter());
        self.w.write_block_header(0, 3);
        let desc = self.ctx.get_desc(r);
        self.type_desc(&desc);
        self.int(i64::from(self.ctx.get_level(r)));
        self.int(i64::from(r.0));
    }

    fn type_exprs(&mut self, items: &[TypeExprRef]) {
        self.list(items, |w, ty| w.type_expr(*ty));
    }

    fn arg_label(&mut self, lbl: &ArgLabel) {
        match lbl {
            ArgLabel::Nolabel => self.w.write_int(0),
            ArgLabel::Labelled(s) | ArgLabel::Optional(s) => {
                let tag = if matches!(lbl, ArgLabel::Labelled(_)) {
                    0
                } else {
                    1
                };
                self.w.write_block_header(tag, 1);
                self.w.write_block_header(0, 2);
                self.str(&s.txt);
                self.location(&s.loc);
            }
        }
    }

    fn type_desc(&mut self, desc: &TypeDesc) {
        match desc {
            TypeDesc::Tnil => self.w.write_int(0),
            TypeDesc::Tvar(name) => {
                self.w.write_block_header(0, 1);
                self.str_option(name.as_deref());
            }
            TypeDesc::Tarrow { args, ret } => {
                self.w.write_block_header(1, 2);
                self.list(args, |w, arg| {
                    w.w.write_block_header(0, 2);
                    w.arg_label(arg.label());
                    w.type_expr(arg.typ);
                });
                self.type_expr(*ret);
            }
            TypeDesc::Ttuple(items) => {
                self.w.write_block_header(2, 1);
                self.type_exprs(items);
            }
            TypeDesc::Tconstr { path, args, .. } => {
                self.w.write_block_header(3, 3);
                self.path(path);
                self.type_exprs(args);
                // `ref Mnil`: abbreviation memos are cleared before saving
                // (compiler/ml/env.ml:1889 `Btype.cleanup_abbrev`).
                self.w.write_block_header(0, 1);
                self.w.write_int(0);
            }
            TypeDesc::Tobject { fields, name } => {
                self.w.write_block_header(4, 2);
                self.type_expr(*fields);
                self.w.write_block_header(0, 1);
                self.option(name.as_ref(), |w, (path, args)| {
                    w.w.write_block_header(0, 2);
                    w.path(path);
                    w.type_exprs(args);
                });
            }
            TypeDesc::Tfield {
                name,
                kind,
                typ,
                rest,
            } => {
                self.w.write_block_header(5, 4);
                self.str(name);
                self.field_kind(kind);
                self.type_expr(*typ);
                self.type_expr(*rest);
            }
            TypeDesc::Tlink(target) => {
                self.w.write_block_header(6, 1);
                self.type_expr(*target);
            }
            TypeDesc::Tsubst(target) => {
                self.w.write_block_header(7, 1);
                self.type_expr(*target);
            }
            TypeDesc::Tvariant(row) => {
                self.w.write_block_header(8, 1);
                self.row_desc(row);
            }
            TypeDesc::Tunivar(name) => {
                self.w.write_block_header(9, 1);
                self.str_option(name.as_deref());
            }
            TypeDesc::Tpoly { body, vars } => {
                self.w.write_block_header(10, 2);
                self.type_expr(*body);
                self.type_exprs(vars);
            }
            TypeDesc::Tpackage { path, lids, args } => {
                self.w.write_block_header(11, 3);
                self.path(path);
                self.list(lids, |w, lid| w.longident(lid));
                self.type_exprs(args);
            }
        }
    }

    /// `field_kind = Fvar of field_kind option ref | Fpresent | Fabsent`.
    fn field_kind(&mut self, kind: &FieldKind) {
        match kind {
            FieldKind::Fpresent => self.w.write_int(0),
            FieldKind::Fabsent => self.w.write_int(1),
            FieldKind::Fvar(r) => match self.ctx.get_field_kind(*r) {
                // Btype.field_kind_repr: a set variable stands for its value.
                Some(inner) => self.field_kind(&inner),
                None => {
                    self.w.write_block_header(0, 1);
                    self.w.write_block_header(0, 1);
                    self.w.write_int(0);
                }
            },
        }
    }

    fn row_desc(&mut self, row: &RowDesc) {
        self.w.write_block_header(0, 5);
        self.list(&row.row_fields, |w, (label, field)| {
            w.w.write_block_header(0, 2);
            w.str(label);
            w.row_field(field);
        });
        self.type_expr(row.row_more);
        self.bool(row.row_closed);
        self.bool(row.row_fixed);
        self.option(row.row_name.as_ref(), |w, (path, args)| {
            w.w.write_block_header(0, 2);
            w.path(path);
            w.type_exprs(args);
        });
    }

    fn row_field(&mut self, field: &RowField) {
        match field {
            RowField::Rabsent => self.w.write_int(0),
            RowField::Rpresent(ty) => {
                self.w.write_block_header(0, 1);
                self.option(ty.as_ref(), |w, ty| w.type_expr(*ty));
            }
            RowField::Reither {
                constant,
                types,
                matched,
                link,
            } => {
                self.w.write_block_header(1, 4);
                self.bool(*constant);
                self.type_exprs(types);
                self.bool(*matched);
                self.w.write_block_header(0, 1);
                let linked = self.ctx.get_row_field(*link);
                self.option(linked.as_ref(), |w, f| w.row_field(f));
            }
        }
    }

    // ------------------------------------------------------------------
    // Types declarations
    // ------------------------------------------------------------------

    fn private_flag(&mut self, flag: PrivateFlag) {
        self.int(match flag {
            PrivateFlag::Private => 0,
            PrivateFlag::Public => 1,
        });
    }

    fn mutable_flag(&mut self, flag: MutableFlag) {
        self.int(match flag {
            MutableFlag::Immutable => 0,
            MutableFlag::Mutable => 1,
        });
    }

    fn primitive(&mut self, prim: &PrimitiveDescription) {
        // Primitive.description (compiler/ml/primitive.mli:18-26).
        self.w.write_block_header(0, 6);
        self.str(&prim.prim_name);
        self.int(i64::from(prim.prim_arity));
        self.bool(true);
        self.str(&prim.prim_native_name);
        self.bool(prim.prim_from_constructor);
        self.bool(false);
    }

    fn value_description(&mut self, vd: &ValueDescription) {
        self.w.write_block_header(0, 4);
        self.type_expr(vd.val_type);
        match &vd.val_kind {
            ValueKind::ValReg => self.w.write_int(0),
            ValueKind::ValPrim(prim) => {
                self.w.write_block_header(0, 1);
                self.primitive(prim);
            }
        }
        self.location(&vd.val_loc);
        self.types_attributes(&vd.val_attributes);
    }

    fn type_declaration(&mut self, td: &TypeDeclaration) {
        self.w.write_block_header(0, 12);
        self.type_exprs(&td.type_params);
        self.int(i64::from(td.type_arity));
        match &td.type_kind {
            TypeKind::TypeAbstract => self.w.write_int(0),
            TypeKind::TypeOpen => self.w.write_int(1),
            TypeKind::TypeRecord(labels, repr) => {
                self.w.write_block_header(0, 2);
                self.list(labels, |w, ld| w.label_declaration(ld));
                self.record_representation(repr);
            }
            TypeKind::TypeVariant(cds, layout) => {
                self.w.write_block_header(1, 2);
                self.list(cds, |w, cd| w.constructor_declaration(cd));
                self.layout_ref(*layout);
            }
        }
        self.private_flag(td.type_private);
        self.option(td.type_manifest.as_ref(), |w, ty| w.type_expr(*ty));
        self.list(&td.type_variance, |w, v| w.int(i64::from(v.bits())));
        self.option(td.type_newtype_level.as_ref(), |w, (a, b)| {
            w.w.write_block_header(0, 2);
            w.int(i64::from(*a));
            w.int(i64::from(*b));
        });
        self.location(&td.type_loc);
        self.types_attributes(&td.type_attributes);
        self.bool(td.type_immediate);
        self.int(match td.type_representation {
            TypeRepresentation::Boxed => 0,
            TypeRepresentation::Unboxed => 1,
        });
        self.list(&td.type_inlined_types, |w, inlined| match inlined {
            // `Record of {type_name; labels}`: inline records are flat blocks.
            TypeInlinedType::Record { type_name, labels } => {
                w.w.write_block_header(0, 2);
                w.str(type_name);
                w.list(labels, |w, ld| w.label_declaration(ld));
            }
        });
    }

    fn record_representation(&mut self, repr: &RecordRepresentation) {
        match repr {
            RecordRepresentation::RecordRegular => self.w.write_int(0),
            RecordRepresentation::RecordFloatUnused => self.w.write_int(1),
            RecordRepresentation::RecordExtension => self.w.write_int(2),
            RecordRepresentation::RecordUnboxed(b) => {
                self.w.write_block_header(0, 1);
                self.bool(*b);
            }
            RecordRepresentation::RecordInlined {
                name,
                representation,
            } => {
                self.w.write_block_header(1, 2);
                self.str(name);
                self.constructor_reference(representation);
            }
        }
    }

    fn constructor_reference(&mut self, r: &ConstructorReference) {
        self.w.write_block_header(0, 2);
        self.layout_ref(r.variant);
        self.int(r.position as i64);
    }

    /// `Variant_runtime.layout_ref = layout_state ref`
    /// (compiler/ml/variant_runtime.ml:115-126), shared per reference.
    fn layout_ref(&mut self, layout_ref: LayoutRef) {
        if let Some(&obj) = self.layouts.get(&layout_ref) {
            self.shared(obj);
            return;
        }
        self.layouts.insert(layout_ref, self.w.obj_counter());
        self.w.write_block_header(0, 1);
        let layout = self.ctx.variant_layout(layout_ref);
        self.w.write_block_header(0, 1);
        self.layout(&layout);
    }

    fn layout(&mut self, layout: &Layout) {
        self.w.write_block_header(0, 3);
        self.bool(layout.unboxed);
        self.array(&layout.constructors, |w, case| w.constructor_case(case));
        let facts = &layout.matching_facts;
        self.w.write_block_header(0, 6);
        self.str_option(facts.tag_name.as_deref());
        self.list(&facts.block_types, |w, bt| w.block_type(bt));
        self.list(&facts.literal_tags, |w, tag| w.tag_type(tag));
        self.bool(facts.has_null);
        self.bool(facts.has_undefined);
        self.bool(facts.has_other_literal);
    }

    fn variant_tag(&mut self, tag: &crate::types::variant_runtime::Tag) {
        self.w.write_block_header(0, 2);
        self.str(&tag.name);
        self.option(tag.tag_type.as_ref(), |w, t| w.tag_type(t));
    }

    fn constructor_case(&mut self, case: &ConstructorCase) {
        match case {
            ConstructorCase::Constant(tag) => {
                self.w.write_block_header(0, 1);
                self.variant_tag(tag);
            }
            ConstructorCase::Block(block) => {
                self.w.write_block_header(1, 1);
                self.w.write_block_header(0, 2);
                self.w.write_block_header(0, 3);
                self.variant_tag(&block.runtime.tag);
                self.str_option(block.runtime.tag_name.as_deref());
                self.bool(block.runtime.untagged);
                self.option(block.block_type.as_ref(), |w, bt| w.block_type(bt));
            }
        }
    }

    fn tag_type(&mut self, tag: &TagType) {
        match tag {
            TagType::Null => self.w.write_int(0),
            TagType::Undefined => self.w.write_int(1),
            TagType::String(s) => {
                self.w.write_block_header(0, 1);
                self.str(s);
            }
            TagType::Int(n) => {
                self.w.write_block_header(1, 1);
                self.int(i64::from(*n));
            }
            TagType::Float(s) => {
                self.w.write_block_header(2, 1);
                self.str(s);
            }
            TagType::BigInt(s) => {
                self.w.write_block_header(3, 1);
                self.str(s);
            }
            TagType::Bool(b) => {
                self.w.write_block_header(4, 1);
                self.bool(*b);
            }
            TagType::Untagged(bt) => {
                self.w.write_block_header(5, 1);
                self.block_type(bt);
            }
        }
    }

    fn block_type(&mut self, bt: &BlockType) {
        match bt {
            BlockType::Int => self.w.write_int(0),
            BlockType::String => self.w.write_int(1),
            BlockType::Float => self.w.write_int(2),
            BlockType::Bigint => self.w.write_int(3),
            BlockType::Boolean => self.w.write_int(4),
            BlockType::Function => self.w.write_int(5),
            BlockType::Object => self.w.write_int(6),
            BlockType::Unknown => self.w.write_int(7),
            BlockType::Instance(instance) => {
                self.w.write_block_header(0, 1);
                self.int(instance_index(*instance));
            }
        }
    }

    fn label_declaration(&mut self, ld: &LabelDeclaration) {
        self.w.write_block_header(0, 6);
        self.ident(&ld.ld_id);
        self.mutable_flag(ld.ld_mutable);
        self.bool(ld.ld_optional);
        self.type_expr(ld.ld_type);
        self.location(&ld.ld_loc);
        self.types_attributes(&ld.ld_attributes);
    }

    fn constructor_declaration(&mut self, cd: &ConstructorDeclaration) {
        self.w.write_block_header(0, 5);
        self.ident(&cd.cd_id);
        self.constructor_arguments(&cd.cd_args);
        self.option(cd.cd_res.as_ref(), |w, ty| w.type_expr(*ty));
        self.location(&cd.cd_loc);
        self.types_attributes(&cd.cd_attributes);
    }

    fn constructor_arguments(&mut self, args: &ConstructorArguments) {
        match args {
            ConstructorArguments::CstrTuple(types) => {
                self.w.write_block_header(0, 1);
                self.type_exprs(types);
            }
            ConstructorArguments::CstrRecord(labels) => {
                self.w.write_block_header(1, 1);
                self.list(labels, |w, ld| w.label_declaration(ld));
            }
        }
    }

    fn extension_constructor(&mut self, ext: &ExtensionConstructor) {
        self.w.write_block_header(0, 8);
        self.path(&ext.ext_type_path);
        self.type_exprs(&ext.ext_type_params);
        self.constructor_arguments(&ext.ext_args);
        self.option(ext.ext_ret_type.as_ref(), |w, ty| w.type_expr(*ty));
        self.private_flag(ext.ext_private);
        self.location(&ext.ext_loc);
        self.types_attributes(&ext.ext_attributes);
        self.bool(ext.ext_is_exception);
    }

    fn module_type(&mut self, mty: &ModuleType) {
        match mty {
            ModuleType::MtyIdent(path) => {
                self.w.write_block_header(0, 1);
                self.path(path);
            }
            ModuleType::MtySignature(sig) => {
                self.w.write_block_header(1, 1);
                self.signature(sig);
            }
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                self.w.write_block_header(2, 3);
                self.ident(param);
                self.option(param_type.as_deref(), |w, mt| w.module_type(mt));
                self.module_type(result);
            }
            ModuleType::MtyAlias(presence, path) => {
                self.w.write_block_header(3, 2);
                self.int(match presence {
                    AliasPresence::MtaPresent => 0,
                    AliasPresence::MtaAbsent => 1,
                });
                self.path(path);
            }
        }
    }

    fn rec_status(&mut self, status: &RecStatus) {
        self.int(match status {
            RecStatus::TrecNot => 0,
            RecStatus::TrecFirst => 1,
            RecStatus::TrecNext => 2,
        });
    }

    fn signature(&mut self, sig: &[SignatureItem]) {
        let items: Vec<&SignatureItem> = sig
            .iter()
            .filter(|item| {
                !matches!(item, SignatureItem::SigClass | SignatureItem::SigClassType)
            })
            .collect();
        self.list(&items, |w, item| w.signature_item(item));
    }

    fn signature_item(&mut self, item: &SignatureItem) {
        match item {
            SignatureItem::SigValue(id, vd) => {
                self.w.write_block_header(0, 2);
                self.ident(id);
                self.value_description(vd);
            }
            SignatureItem::SigType(id, td, rs) => {
                self.w.write_block_header(1, 3);
                self.ident(id);
                self.type_declaration(td);
                self.rec_status(rs);
            }
            SignatureItem::SigTypext(id, ext, es) => {
                self.w.write_block_header(2, 3);
                self.ident(id);
                self.extension_constructor(ext);
                self.int(match es {
                    ExtStatus::TextFirst => 0,
                    ExtStatus::TextNext => 1,
                    ExtStatus::TextException => 2,
                });
            }
            SignatureItem::SigModule(id, md, rs) => {
                self.w.write_block_header(3, 3);
                self.ident(id);
                self.module_declaration(md);
                self.rec_status(rs);
            }
            SignatureItem::SigModtype(id, mtd) => {
                self.w.write_block_header(4, 2);
                self.ident(id);
                self.modtype_declaration(mtd);
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {
                unreachable!("class items are filtered out")
            }
        }
    }

    fn module_declaration(&mut self, md: &ModuleDeclaration) {
        self.w.write_block_header(0, 3);
        self.module_type(&md.md_type);
        self.types_attributes(&md.md_attributes);
        self.location(&md.md_loc);
    }

    fn modtype_declaration(&mut self, mtd: &ModtypeDeclaration) {
        self.w.write_block_header(0, 3);
        self.option(mtd.mtd_type.as_ref(), |w, mt| w.module_type(mt));
        self.types_attributes(&mtd.mtd_attributes);
        self.location(&mtd.mtd_loc);
    }

    fn constructor_description(&mut self, cd: &ConstructorDescription) {
        self.w.write_block_header(0, 11);
        self.str(&cd.cstr_name);
        self.type_expr(cd.cstr_res);
        self.type_exprs(&cd.cstr_existentials);
        self.type_exprs(&cd.cstr_args);
        self.int(i64::from(cd.cstr_arity));
        match &cd.cstr_kind {
            ConstructorKind::Ordinary(r) => {
                self.w.write_block_header(0, 1);
                self.constructor_reference(r);
            }
            ConstructorKind::Extension(path) => {
                self.w.write_block_header(1, 1);
                self.path(path);
            }
        }
        self.bool(cd.cstr_generalized);
        self.private_flag(cd.cstr_private);
        self.location(&cd.cstr_loc);
        self.types_attributes(&cd.cstr_attributes);
        self.option(cd.cstr_inlined.as_deref(), |w, td| w.type_declaration(td));
    }

    /// `constructor_description` of the predefined `None`, for omitted
    /// optional record fields (compiler/ml/typecore.ml:2833-2842).
    fn none_constructor_description(&mut self, option_ty: TypeExprRef) {
        let layout = *self.option_layout.get_or_insert_with(|| {
            crate::types::variant_runtime::plain_layout(
                self.ctx,
                [("None".to_string(), false), ("Some".to_string(), true)],
            )
        });
        self.w.write_block_header(0, 11);
        self.str("None");
        self.type_expr(option_ty);
        self.w.write_int(0);
        self.w.write_int(0);
        self.int(0);
        self.w.write_block_header(0, 1);
        self.constructor_reference(&ConstructorReference {
            variant: layout,
            position: 0,
        });
        self.bool(false);
        self.private_flag(PrivateFlag::Public);
        self.none_location();
        self.w.write_int(0);
        self.w.write_int(0);
    }

    fn label_description(&mut self, lbl: &LabelDescription) {
        self.w.write_block_header(0, 11);
        self.str(&lbl.lbl_name);
        self.type_expr(lbl.lbl_res);
        self.type_expr(lbl.lbl_arg);
        self.mutable_flag(lbl.lbl_mut);
        self.bool(lbl.lbl_optional);
        self.int(i64::from(lbl.lbl_pos));
        // `lbl_all`: Rust does not keep the shared label array.
        self.atom(0);
        self.record_representation(&lbl.lbl_repres);
        self.private_flag(lbl.lbl_private);
        self.location(&lbl.lbl_loc);
        self.types_attributes(&lbl.lbl_attributes);
    }

    // ------------------------------------------------------------------
    // Typedtree
    // ------------------------------------------------------------------

    /// `Env.empty` (compiler/ml/env.ml:479-493), shared by every node.
    fn env(&mut self) {
        if let Some(obj) = self.env_obj {
            self.shared(obj);
            return;
        }
        self.env_obj = Some(self.w.obj_counter());
        self.w.write_block_header(0, 12);
        // values, constrs, labels, types, modules, modtypes, components:
        // `{current = Ident.empty; opened = None}`.
        for _ in 0..7 {
            self.w.write_block_header(0, 2);
            self.w.write_int(0);
            self.w.write_int(0);
        }
        self.w.write_int(0); // functor_args
        self.w.write_int(0); // summary = Env_empty
        self.w.write_int(0); // local_constraints
        self.w.write_int(0); // gadt_instances
        self.w.write_int(0); // flags
    }

    fn collect_values(&mut self, sig: &[SignatureItem]) {
        for item in sig {
            match item {
                SignatureItem::SigValue(id, vd) => {
                    self.values
                        .entry((id.stamp(), id.name().to_string()))
                        .or_insert_with(|| vd.clone());
                }
                SignatureItem::SigModule(_, md, _) => self.collect_module_type(&md.md_type),
                SignatureItem::SigModtype(_, mtd) => {
                    if let Some(mt) = &mtd.mtd_type {
                        self.collect_module_type(mt);
                    }
                }
                _ => {}
            }
        }
    }

    fn collect_module_type(&mut self, mt: &ModuleType) {
        match mt {
            ModuleType::MtySignature(sig) => self.collect_values(sig),
            ModuleType::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(p) = param_type {
                    self.collect_module_type(p);
                }
                self.collect_module_type(result);
            }
            ModuleType::MtyIdent(_) | ModuleType::MtyAlias(..) => {}
        }
    }

    fn typed_constant(&mut self, c: &tt::Constant) {
        match c {
            tt::Constant::Int(n) => {
                self.w.write_block_header(0, 1);
                self.int(*n);
            }
            tt::Constant::Char(c) => {
                self.w.write_block_header(1, 1);
                self.int(i64::from(*c));
            }
            tt::Constant::String(s, delim) => {
                self.w.write_block_header(2, 2);
                self.str(s);
                self.str_option(delim.as_deref());
            }
            tt::Constant::Float(s) => {
                self.w.write_block_header(3, 1);
                self.str(s);
            }
            tt::Constant::BigInt(sign, s) => {
                self.w.write_block_header(6, 2);
                self.bool(*sign);
                self.str(s);
            }
        }
    }

    fn partial(&mut self, p: tt::Partial) {
        self.int(match p {
            tt::Partial::Partial => 0,
            tt::Partial::Total => 1,
        });
    }

    fn pattern(&mut self, pat: &tt::Pattern) {
        self.w.write_block_header(0, 6);
        self.pattern_desc(&pat.pat_desc, pat.pat_type);
        self.loc_idx(pat.pat_loc);
        let extras: Vec<_> = pat.pat_extra.iter().collect();
        self.list(&extras, |w, (extra, loc, attrs)| {
            w.w.write_block_header(0, 3);
            match extra {
                tt::PatExtra::Tpat_constraint(ct) => {
                    w.w.write_block_header(0, 1);
                    w.core_type(ct);
                }
                tt::PatExtra::Tpat_type(path, lid) => {
                    w.w.write_block_header(1, 2);
                    w.path(path);
                    w.lid_loc(lid);
                }
                tt::PatExtra::Tpat_open(path, lid, _) => {
                    w.w.write_block_header(2, 3);
                    w.path(path);
                    w.lid_loc(lid);
                    w.env();
                }
                tt::PatExtra::Tpat_unpack => w.w.write_int(0),
            }
            w.loc_idx(*loc);
            w.parsetree_attributes(attrs);
        });
        self.type_expr(pat.pat_type);
        self.env();
        self.parsetree_attributes(&pat.pat_attributes);
    }

    /// `row_desc ref` of a variant pattern: typecore stores the expected
    /// row (compiler/ml/typecore.ml `type_pat_aux`, Ppat_variant).
    fn pattern_row_ref(&mut self, ty: TypeExprRef) {
        self.w.write_block_header(0, 1);
        let mut current = ty;
        for _ in 0..64 {
            let desc = self.ctx.get_desc(current);
            match &*desc {
                TypeDesc::Tlink(next) => current = *next,
                TypeDesc::Tvariant(row) => {
                    let row = row.clone();
                    drop(desc);
                    self.row_desc(&row);
                    return;
                }
                _ => break,
            }
        }
        self.row_desc(&RowDesc {
            row_fields: Default::default(),
            row_more: ty,
            row_closed: false,
            row_fixed: false,
            row_name: None,
        });
    }

    fn pattern_desc(&mut self, desc: &tt::PatternDesc, pat_type: TypeExprRef) {
        use tt::PatternDesc as P;
        match desc {
            P::Tpat_any => self.w.write_int(0),
            P::Tpat_var(id, name) => {
                self.w.write_block_header(0, 2);
                self.ident(id);
                self.str_loc(name);
            }
            P::Tpat_alias(p, id, name) => {
                self.w.write_block_header(1, 3);
                self.pattern(p);
                self.ident(id);
                self.str_loc(name);
            }
            P::Tpat_constant(c) => {
                self.w.write_block_header(2, 1);
                self.typed_constant(c);
            }
            P::Tpat_tuple(items) => {
                self.w.write_block_header(3, 1);
                self.list(items, |w, p| w.pattern(p));
            }
            P::Tpat_construct(lid, cstr, args) => {
                self.w.write_block_header(4, 3);
                self.lid_loc(lid);
                self.constructor_description(cstr);
                self.list(args, |w, p| w.pattern(p));
            }
            P::Tpat_variant(label, arg, _) => {
                self.w.write_block_header(5, 3);
                self.str(label);
                self.option(arg.as_deref(), |w, p| w.pattern(p));
                self.pattern_row_ref(pat_type);
            }
            P::Tpat_record(fields, closed, rest) => {
                self.w.write_block_header(6, 3);
                self.list(fields, |w, (lid, lbl, p, optional)| {
                    w.w.write_block_header(0, 4);
                    w.lid_loc(lid);
                    w.label_description(lbl);
                    w.pattern(p);
                    w.bool(*optional);
                });
                closed.marshal(&mut self.w);
                self.option(rest.as_ref(), |w, rest| {
                    w.w.write_block_header(0, 4);
                    w.ident(&rest.rest_ident);
                    w.str_loc(&rest.rest_name);
                    w.type_expr(rest.rest_type);
                    w.strings(&rest.excluded_runtime_labels);
                });
            }
            P::Tpat_array(items) => {
                self.w.write_block_header(7, 1);
                self.list(items, |w, p| w.pattern(p));
            }
            P::Tpat_or(p1, p2, row) => {
                self.w.write_block_header(8, 3);
                self.pattern(p1);
                self.pattern(p2);
                self.option(row.as_ref(), |w, row| w.row_desc(row));
            }
        }
    }

    /// The `Parsetree.pattern` of a `for` loop index, rebuilt from its typed
    /// form (compiler/ml/typedtree.mli: `Texp_for of Ident.t *
    /// Parsetree.pattern * ...`).
    fn for_index_pattern(&mut self, pat: &tt::Pattern) {
        self.w.write_block_header(0, 3);
        match &pat.pat_desc {
            tt::PatternDesc::Tpat_var(_, name) => {
                self.w.write_block_header(0, 1);
                self.str_loc(name);
            }
            _ => self.w.write_int(0),
        }
        self.loc_idx(pat.pat_loc);
        self.parsetree_attributes(&pat.pat_attributes);
    }

    fn expression(&mut self, e: &tt::Expression) {
        self.w.write_block_header(0, 6);
        self.expression_desc(&e.exp_desc);
        self.loc_idx(e.exp_loc);
        let extras: Vec<_> = e
            .exp_extra
            .iter()
            .filter(|(extra, _, _)| !matches!(extra, tt::ExpExtra::Texp_newtype(_)))
            .collect();
        self.list(&extras, |w, (extra, loc, attrs)| {
            w.w.write_block_header(0, 3);
            match extra {
                tt::ExpExtra::Texp_constraint(ct) => {
                    w.w.write_block_header(0, 1);
                    w.core_type(ct);
                }
                tt::ExpExtra::Texp_coerce(ct) => {
                    w.w.write_block_header(1, 1);
                    w.core_type(ct);
                }
                tt::ExpExtra::Texp_open(flag, path, lid, _) => {
                    w.w.write_block_header(2, 4);
                    flag.marshal(&mut w.w);
                    w.path(path);
                    w.lid_loc(lid);
                    w.env();
                }
                tt::ExpExtra::Texp_newtype(_) => unreachable!("filtered out"),
            }
            w.loc_idx(*loc);
            w.parsetree_attributes(attrs);
        });
        self.type_expr(e.exp_type);
        self.env();
        self.parsetree_attributes(&e.exp_attributes);
    }

    /// `option_none ty loc` (compiler/ml/typecore.ml `option_none`):
    /// `Texp_construct (mknoloc (Lident "None"), cstr_none, [])`.
    fn omitted_none_expression(&mut self, loc: LocIdx, ty: TypeExprRef) {
        self.w.write_block_header(0, 6);
        self.w.write_block_header(8, 3);
        self.w.write_block_header(0, 2);
        self.w.write_lident_idx(self.arena.none_lid());
        self.loc_idx(self.arena.none_loc());
        self.none_constructor_description(ty);
        self.w.write_int(0);
        self.loc_idx(loc);
        self.w.write_int(0);
        self.type_expr(ty);
        self.env();
        self.w.write_int(0);
    }

    fn record_field(&mut self, lbl: &LabelDescription, def: &tt::RecordLabelDefinition, opt: bool) {
        self.w.write_block_header(0, 3);
        self.label_description(lbl);
        match def {
            tt::RecordLabelDefinition::Kept(ty) => {
                self.w.write_block_header(0, 1);
                self.type_expr(*ty);
            }
            tt::RecordLabelDefinition::Overridden(lid, e) => {
                self.w.write_block_header(1, 2);
                self.lid_loc(lid);
                self.expression(e);
            }
            tt::RecordLabelDefinition::OmittedOptionalNone(lid, ty) => {
                self.w.write_block_header(1, 2);
                self.lid_loc(lid);
                self.omitted_none_expression(lid.loc, *ty);
            }
        }
        self.bool(opt);
    }

    fn record_representation_of(&mut self, first: Option<&LabelDescription>) {
        match first {
            Some(lbl) => self.record_representation(&lbl.lbl_repres),
            None => self.w.write_int(0),
        }
    }

    fn expression_desc(&mut self, desc: &tt::ExpressionDesc) {
        use tt::ExpressionDesc as E;
        match desc {
            E::Texp_ident(path, lid, vd) => {
                self.w.write_block_header(0, 3);
                self.path(path);
                self.lid_loc(lid);
                self.value_description(vd);
            }
            E::Texp_constant(c) => {
                self.w.write_block_header(1, 1);
                self.typed_constant(c);
            }
            E::Texp_let(flag, vbs, body) => {
                self.w.write_block_header(2, 3);
                flag.marshal(&mut self.w);
                self.list(vbs, |w, vb| w.value_binding(vb));
                self.expression(body);
            }
            E::Texp_function {
                params,
                body,
                async_,
            } => {
                self.w.write_block_header(3, 3);
                self.list(params, |w, p| {
                    w.w.write_block_header(0, 4);
                    w.arg_label(&p.fp_lbl);
                    w.ident(&p.fp_param);
                    w.pattern(&p.fp_pat);
                    w.partial(p.fp_partial);
                });
                self.expression(body);
                self.bool(*async_);
            }
            E::Texp_apply {
                funct,
                args,
                partial,
                transformed_jsx,
            } => {
                self.w.write_block_header(4, 4);
                self.expression(funct);
                self.list(args, |w, arg| {
                    w.w.write_block_header(0, 2);
                    w.arg_label(&arg.label);
                    w.option(arg.expression.as_ref(), |w, e| w.expression(e));
                });
                self.bool(*partial);
                self.bool(*transformed_jsx);
            }
            E::Texp_match(e, cases, exn_cases, partial) => {
                self.w.write_block_header(5, 4);
                self.expression(e);
                self.cases(cases);
                self.cases(exn_cases);
                self.partial(*partial);
            }
            E::Texp_try(e, cases) => {
                self.w.write_block_header(6, 2);
                self.expression(e);
                self.cases(cases);
            }
            E::Texp_tuple(items) => {
                self.w.write_block_header(7, 1);
                self.list(items, |w, e| w.expression(e));
            }
            E::Texp_construct(lid, cstr, args) => {
                self.w.write_block_header(8, 3);
                self.lid_loc(lid);
                self.constructor_description(cstr);
                self.list(args, |w, e| w.expression(e));
            }
            E::Texp_variant(label, arg) => {
                self.w.write_block_header(9, 2);
                self.str(label);
                self.option(arg.as_deref(), |w, e| w.expression(e));
            }
            E::Texp_record {
                fields,
                empty_representation,
                extended_expression,
            } => {
                self.w.write_block_header(10, 3);
                self.array(fields, |w, (_, lbl, def, opt)| w.record_field(lbl, def, *opt));
                match empty_representation.as_deref() {
                    Some(repr) if fields.is_empty() => self.record_representation(repr),
                    _ => self.record_representation_of(fields.first().map(|f| &f.1)),
                }
                self.option(extended_expression.as_deref(), |w, e| w.expression(e));
            }
            E::Texp_record_sparse {
                fields,
                all_labels,
                omitted_loc,
                extended_expression,
            } => {
                // Expand the sparse storage back to typecore's full
                // `lbl_all`-ordered field array (compiler/ml/typecore.ml:
                // 2833-2842).
                let mut explicit: HashMap<i32, &tt::RecordField> = HashMap::new();
                for field in fields {
                    explicit.insert(field.1.lbl_pos, field);
                }
                enum Slot<'f> {
                    Explicit(&'f tt::RecordField),
                    Omitted(&'f LabelDescription),
                }
                let mut slots = Vec::with_capacity(all_labels.len());
                for (idx, label) in all_labels.iter().enumerate() {
                    let pos = if label.lbl_pos >= 0 {
                        label.lbl_pos
                    } else {
                        idx as i32
                    };
                    if let Some(field) = explicit.get(&pos) {
                        slots.push(Slot::Explicit(field));
                    } else if label.lbl_optional {
                        slots.push(Slot::Omitted(label));
                    }
                }
                self.w.write_block_header(10, 3);
                let omitted_loc = *omitted_loc;
                self.array(&slots, |w, slot| match slot {
                    Slot::Explicit((_, lbl, def, opt)) => w.record_field(lbl, def, *opt),
                    Slot::Omitted(label) => {
                        w.w.write_block_header(0, 3);
                        w.label_description(label);
                        w.w.write_block_header(1, 2);
                        w.w.write_block_header(0, 2);
                        w.str_lident(&label.lbl_name);
                        w.loc_idx(omitted_loc);
                        w.omitted_none_expression(omitted_loc, label.lbl_arg);
                        w.bool(false);
                    }
                });
                self.record_representation_of(all_labels.first());
                self.option(extended_expression.as_deref(), |w, e| w.expression(e));
            }
            E::Texp_field(e, lid, lbl) => {
                self.w.write_block_header(11, 3);
                self.expression(e);
                self.lid_loc(lid);
                self.label_description(lbl);
            }
            E::Texp_setfield(e1, lid, lbl, e2) => {
                self.w.write_block_header(12, 4);
                self.expression(e1);
                self.lid_loc(lid);
                self.label_description(lbl);
                self.expression(e2);
            }
            E::Texp_array(items) => {
                self.w.write_block_header(13, 1);
                self.list(items, |w, e| w.expression(e));
            }
            E::Texp_ifthenelse(c, t, f) => {
                self.w.write_block_header(14, 3);
                self.expression(c);
                self.expression(t);
                self.option(f.as_deref(), |w, e| w.expression(e));
            }
            E::Texp_sequence(a, b) => {
                self.w.write_block_header(15, 2);
                self.expression(a);
                self.expression(b);
            }
            E::Texp_break => self.w.write_int(0),
            E::Texp_continue => self.w.write_int(1),
            E::Texp_while(c, body) => {
                self.w.write_block_header(16, 2);
                self.expression(c);
                self.expression(body);
            }
            E::Texp_for(id, pat, lo, hi, dir, body) => {
                self.w.write_block_header(17, 6);
                self.ident(id);
                self.for_index_pattern(pat);
                self.expression(lo);
                self.expression(hi);
                dir.marshal(&mut self.w);
                self.expression(body);
            }
            E::Texp_send(e, meth, arg) => {
                self.w.write_block_header(18, 3);
                self.expression(e);
                self.w.write_block_header(0, 1);
                match meth {
                    tt::MethKind::Tmeth_name(name) => self.str(name),
                    tt::MethKind::Tmeth_val(id) => self.str(id.name()),
                }
                self.option(arg.as_deref(), |w, e| w.expression(e));
            }
            E::Texp_letmodule(id, name, me, body) => {
                self.w.write_block_header(19, 4);
                self.ident(id);
                self.str_loc(name);
                self.module_expr(me);
                self.expression(body);
            }
            E::Texp_letexception(ext, body) => {
                self.w.write_block_header(20, 2);
                self.typed_extension_constructor(ext);
                self.expression(body);
            }
            E::Texp_assert(e) => {
                self.w.write_block_header(21, 1);
                self.expression(e);
            }
            E::Texp_pack(me) => {
                self.w.write_block_header(22, 1);
                self.module_expr(me);
            }
            E::Texp_extension_constructor(lid, path) => {
                self.w.write_block_header(23, 2);
                self.lid_loc(lid);
                self.path(path);
            }
            E::Texp_for_of(id, pat, iterable, body) | E::Texp_for_await_of(id, pat, iterable, body) => {
                let tag = if matches!(desc, E::Texp_for_of(..)) { 24 } else { 25 };
                self.w.write_block_header(tag, 4);
                self.ident(id);
                pat.marshal(&mut self.w);
                self.expression(iterable);
                self.expression(body);
            }
        }
    }

    /// `{txt = Lident name; loc}` payload for a synthesized label.
    fn str_lident(&mut self, name: &str) {
        self.w.write_block_header(0, 1);
        self.str(name);
    }

    fn cases(&mut self, cases: &[tt::Case]) {
        self.list(cases, |w, c| {
            w.w.write_block_header(0, 3);
            w.pattern(&c.c_lhs);
            w.option(c.c_guard.as_ref(), |w, e| w.expression(e));
            w.expression(&c.c_rhs);
        });
    }

    fn value_binding(&mut self, vb: &tt::ValueBinding) {
        self.w.write_block_header(0, 4);
        self.pattern(&vb.vb_pat);
        self.expression(&vb.vb_expr);
        self.parsetree_attributes(&vb.vb_attributes);
        self.loc_idx(vb.vb_loc);
    }

    fn module_expr(&mut self, me: &tt::ModuleExpr) {
        self.w.write_block_header(0, 5);
        use tt::ModuleExprDesc as M;
        match &me.mod_desc {
            M::Tmod_ident(path, lid) => {
                self.w.write_block_header(0, 2);
                self.path(path);
                self.lid_loc(lid);
            }
            M::Tmod_structure(s) => {
                self.w.write_block_header(1, 1);
                self.structure(s);
            }
            M::Tmod_functor(id, name, arg, body) => {
                self.w.write_block_header(2, 4);
                self.ident(id);
                self.str_loc(name);
                self.option(arg.as_deref(), |w, mt| w.typed_module_type(mt));
                self.module_expr(body);
            }
            M::Tmod_apply(f, a, c) => {
                self.w.write_block_header(3, 3);
                self.module_expr(f);
                self.module_expr(a);
                self.coercion(c);
            }
            M::Tmod_constraint(inner, mty, constraint, c) => {
                self.w.write_block_header(4, 4);
                self.module_expr(inner);
                self.module_type(mty);
                match constraint {
                    tt::ModuleTypeConstraint::Tmodtype_implicit => self.w.write_int(0),
                    tt::ModuleTypeConstraint::Tmodtype_explicit(mt) => {
                        self.w.write_block_header(0, 1);
                        self.typed_module_type(mt);
                    }
                }
                self.coercion(c);
            }
            M::Tmod_unpack(e, mty) => {
                self.w.write_block_header(5, 2);
                self.expression(e);
                self.module_type(mty);
            }
        }
        self.loc_idx(me.mod_loc);
        self.module_type(&me.mod_type);
        self.env();
        self.parsetree_attributes(&me.mod_attributes);
    }

    fn coercion(&mut self, c: &tt::ModuleCoercion) {
        use tt::ModuleCoercion as C;
        match c {
            C::Tcoerce_none => self.w.write_int(0),
            C::Tcoerce_structure(pos, ids, runtime_fields) => {
                self.w.write_block_header(0, 3);
                self.list(pos, |w, (n, c)| {
                    w.w.write_block_header(0, 2);
                    w.int(*n as i64);
                    w.coercion(c);
                });
                self.list(ids, |w, (id, n, c)| {
                    w.w.write_block_header(0, 3);
                    w.ident(id);
                    w.int(*n as i64);
                    w.coercion(c);
                });
                self.strings(runtime_fields);
            }
            C::Tcoerce_functor(a, b) => {
                self.w.write_block_header(1, 2);
                self.coercion(a);
                self.coercion(b);
            }
            C::Tcoerce_primitive(pc) => {
                self.w.write_block_header(2, 1);
                self.w.write_block_header(0, 5);
                self.primitive(&pc.pc_desc);
                self.type_expr(pc.pc_type);
                self.env();
                self.location(&pc.pc_loc);
                self.ident(&pc.pc_id);
            }
            C::Tcoerce_alias(_, path, c) => {
                self.w.write_block_header(3, 2);
                self.path(path);
                self.coercion(c);
            }
        }
    }

    fn structure(&mut self, s: &tt::Structure) {
        self.collect_values(&s.str_type);
        self.w.write_block_header(0, 3);
        self.list(&s.str_items, |w, item| w.structure_item(item));
        self.signature(&s.str_type);
        self.env();
    }

    fn structure_item(&mut self, item: &tt::StructureItem) {
        self.w.write_block_header(0, 3);
        use tt::StructureItemDesc as S;
        match &item.str_desc {
            S::Tstr_eval(e, attrs) => {
                self.w.write_block_header(0, 2);
                self.expression(e);
                self.parsetree_attributes(attrs);
            }
            S::Tstr_value(flag, vbs) => {
                self.w.write_block_header(1, 2);
                flag.marshal(&mut self.w);
                self.list(vbs, |w, vb| w.value_binding(vb));
            }
            S::Tstr_primitive(vd) => {
                self.w.write_block_header(2, 1);
                self.typed_value_description(vd);
            }
            S::Tstr_type(flag, tds) => {
                self.w.write_block_header(3, 2);
                flag.marshal(&mut self.w);
                self.list(tds, |w, td| w.typed_type_declaration(td));
            }
            S::Tstr_typext(te) => {
                self.w.write_block_header(4, 1);
                self.type_extension(te);
            }
            S::Tstr_exception(ext) => {
                self.w.write_block_header(5, 1);
                self.typed_extension_constructor(ext);
            }
            S::Tstr_module(mb) => {
                self.w.write_block_header(6, 1);
                self.module_binding(mb);
            }
            S::Tstr_recmodule(mbs) => {
                self.w.write_block_header(7, 1);
                self.list(mbs, |w, mb| w.module_binding(mb));
            }
            S::Tstr_modtype(mtd) => {
                self.w.write_block_header(8, 1);
                self.module_type_declaration(mtd);
            }
            S::Tstr_open(od) => {
                self.w.write_block_header(9, 1);
                self.open_description(od);
            }
            S::Tstr_include(incl) => {
                self.w.write_block_header(10, 1);
                self.w.write_block_header(0, 4);
                self.module_expr(&incl.incl_mod);
                self.signature(&incl.incl_type);
                self.loc_idx(incl.incl_loc);
                self.parsetree_attributes(&incl.incl_attributes);
            }
            S::Tstr_attribute(attr) => {
                self.w.write_block_header(11, 1);
                self.parsetree_attribute(attr);
            }
        }
        self.loc_idx(item.str_loc);
        self.env();
    }

    fn parsetree_attribute(&mut self, attr: &crate::parser::ast::Attribute) {
        self.w.write_block_header(0, 2);
        attr.0.marshal(&mut self.w);
        attr.1.marshal(&mut self.w);
    }

    fn module_binding(&mut self, mb: &tt::ModuleBinding) {
        self.w.write_block_header(0, 5);
        self.ident(&mb.mb_id);
        self.str_loc(&mb.mb_name);
        self.module_expr(&mb.mb_expr);
        self.parsetree_attributes(&mb.mb_attributes);
        self.loc_idx(mb.mb_loc);
    }

    fn open_description(&mut self, od: &tt::OpenDeclaration) {
        self.w.write_block_header(0, 4);
        self.path(&od.open_path);
        self.lid_loc(&od.open_txt);
        od.open_override.marshal(&mut self.w);
        self.parsetree_attributes(&od.open_attributes);
    }

    fn module_type_declaration(&mut self, mtd: &tt::ModuleTypeDeclaration) {
        self.w.write_block_header(0, 5);
        self.ident(&mtd.mtd_id);
        self.str_loc(&mtd.mtd_name);
        self.option(mtd.mtd_type.as_ref(), |w, mt| w.typed_module_type(mt));
        self.parsetree_attributes(&mtd.mtd_attributes);
        self.loc_idx(mtd.mtd_loc);
    }

    fn typed_module_type(&mut self, mt: &tt::ModuleType) {
        self.w.write_block_header(0, 5);
        use tt::ModuleTypeDesc as T;
        match &mt.mty_desc {
            T::Tmty_ident(path, lid) => {
                self.w.write_block_header(0, 2);
                self.path(path);
                self.lid_loc(lid);
            }
            T::Tmty_signature(sig) => {
                self.w.write_block_header(1, 1);
                let sig_type = match &mt.mty_type {
                    ModuleType::MtySignature(items) => items.as_slice(),
                    _ => &[],
                };
                self.typed_signature(sig, sig_type);
            }
            T::Tmty_placeholder => {
                self.w.write_block_header(1, 1);
                self.typed_signature(&tt::TypedSignature { sig_items: vec![] }, &[]);
            }
            T::Tmty_functor(id, name, arg, body) => {
                self.w.write_block_header(2, 4);
                self.ident(id);
                self.str_loc(name);
                self.option(arg.as_deref(), |w, mt| w.typed_module_type(mt));
                self.typed_module_type(body);
            }
            T::Tmty_with(inner, constraints) => {
                self.w.write_block_header(3, 2);
                self.typed_module_type(inner);
                self.list(constraints, |w, (path, lid, wc)| {
                    w.w.write_block_header(0, 3);
                    w.path(path);
                    w.lid_loc(lid);
                    match wc {
                        tt::WithConstraint::Twith_type(td) => {
                            w.w.write_block_header(0, 1);
                            w.typed_type_declaration(td);
                        }
                        tt::WithConstraint::Twith_module(path, lid) => {
                            w.w.write_block_header(1, 2);
                            w.path(path);
                            w.lid_loc(lid);
                        }
                        tt::WithConstraint::Twith_typesubst(td) => {
                            w.w.write_block_header(2, 1);
                            w.typed_type_declaration(td);
                        }
                        tt::WithConstraint::Twith_modsubst(path, lid) => {
                            w.w.write_block_header(3, 2);
                            w.path(path);
                            w.lid_loc(lid);
                        }
                    }
                });
            }
            T::Tmty_typeof(me) => {
                self.w.write_block_header(4, 1);
                self.module_expr(me);
            }
            T::Tmty_alias(path, lid) => {
                self.w.write_block_header(5, 2);
                self.path(path);
                self.lid_loc(lid);
            }
        }
        self.module_type(&mt.mty_type);
        self.env();
        self.loc_idx(mt.mty_loc);
        self.parsetree_attributes(&mt.mty_attributes);
    }

    fn typed_signature(&mut self, sig: &tt::TypedSignature, sig_type: &[SignatureItem]) {
        self.collect_values(sig_type);
        self.w.write_block_header(0, 3);
        self.list(&sig.sig_items, |w, item| w.typed_signature_item(item));
        self.signature(sig_type);
        self.env();
    }

    fn typed_signature_item(&mut self, item: &tt::TypedSignatureItem) {
        self.w.write_block_header(0, 3);
        use tt::TypedSignatureItemDesc as S;
        match &item.sig_desc {
            S::Tsig_value(vd) => {
                self.w.write_block_header(0, 1);
                self.typed_value_description(vd);
            }
            S::Tsig_type(flag, tds) => {
                self.w.write_block_header(1, 2);
                flag.marshal(&mut self.w);
                self.list(tds, |w, td| w.typed_type_declaration(td));
            }
            S::Tsig_typext(te) => {
                self.w.write_block_header(2, 1);
                self.type_extension(te);
            }
            S::Tsig_exception(ext) => {
                self.w.write_block_header(3, 1);
                self.typed_extension_constructor(ext);
            }
            S::Tsig_module(md) => {
                self.w.write_block_header(4, 1);
                self.typed_module_declaration(md);
            }
            S::Tsig_recmodule(mds) => {
                self.w.write_block_header(5, 1);
                self.list(mds, |w, md| w.typed_module_declaration(md));
            }
            S::Tsig_modtype(mtd) => {
                self.w.write_block_header(6, 1);
                self.module_type_declaration(mtd);
            }
            S::Tsig_open(od) => {
                self.w.write_block_header(7, 1);
                self.open_description(od);
            }
            S::Tsig_include(incl) => {
                self.w.write_block_header(8, 1);
                self.w.write_block_header(0, 4);
                self.typed_module_type(&incl.incl_mod);
                self.signature(&incl.incl_type);
                self.loc_idx(incl.incl_loc);
                self.parsetree_attributes(&incl.incl_attributes);
            }
            S::Tsig_attribute(attr) => {
                self.w.write_block_header(9, 1);
                self.parsetree_attribute(attr);
            }
        }
        self.env();
        self.loc_idx(item.sig_loc);
    }

    fn typed_module_declaration(&mut self, md: &tt::TypedModuleDeclaration) {
        self.w.write_block_header(0, 5);
        self.ident(&md.md_id);
        self.str_loc(&md.md_name);
        self.typed_module_type(&md.md_type);
        self.parsetree_attributes(&md.md_attributes);
        self.loc_idx(md.md_loc);
    }

    fn core_type(&mut self, ct: &tt::TypedCoreType) {
        self.w.write_block_header(0, 5);
        use tt::TypedCoreTypeDesc as C;
        match &ct.ctyp_desc {
            C::Ttyp_var(None) => self.w.write_int(0),
            C::Ttyp_var(Some(name)) => {
                self.w.write_block_header(0, 1);
                self.str(name);
            }
            C::Ttyp_arrow(args, ret) => {
                self.w.write_block_header(1, 2);
                self.list(args, |w, arg| {
                    w.w.write_block_header(0, 3);
                    w.parsetree_attributes(&arg.attrs);
                    w.arg_label(&arg.lbl);
                    w.core_type(&arg.typ);
                });
                self.core_type(ret);
            }
            C::Ttyp_tuple(items) => {
                self.w.write_block_header(2, 1);
                self.list(items, |w, ct| w.core_type(ct));
            }
            C::Ttyp_constr(path, lid, args) => {
                self.w.write_block_header(3, 3);
                self.path(path);
                self.lid_loc(lid);
                self.list(args, |w, ct| w.core_type(ct));
            }
            C::Ttyp_object(fields, closed) => {
                self.w.write_block_header(4, 2);
                self.list(fields, |w, field| match &field.of_desc {
                    tt::ObjectFieldDesc::OTtag(name, ct) => {
                        w.w.write_block_header(0, 3);
                        w.str_loc(name);
                        w.parsetree_attributes(&field.of_attributes);
                        w.core_type(ct);
                    }
                    tt::ObjectFieldDesc::OTinherit(ct) => {
                        w.w.write_block_header(1, 1);
                        w.core_type(ct);
                    }
                });
                closed.marshal(&mut self.w);
            }
            C::Ttyp_alias(inner, name) => {
                self.w.write_block_header(5, 2);
                self.core_type(inner);
                self.str(name);
            }
            C::Ttyp_variant(fields, closed, labels) => {
                self.w.write_block_header(6, 3);
                self.list(fields, |w, field| match &field.rf_desc {
                    tt::RowFieldDesc::Rtag(name, constant, cts) => {
                        w.w.write_block_header(0, 4);
                        w.str_loc(name);
                        w.parsetree_attributes(&field.rf_attributes);
                        w.bool(*constant);
                        w.list(cts, |w, ct| w.core_type(ct));
                    }
                    tt::RowFieldDesc::Rinherit(ct) => {
                        w.w.write_block_header(1, 1);
                        w.core_type(ct);
                    }
                });
                closed.marshal(&mut self.w);
                self.option(labels.as_ref(), |w, labels| w.strings(labels));
            }
            C::Ttyp_poly(vars, body) => {
                self.w.write_block_header(7, 2);
                self.strings(vars);
                self.core_type(body);
            }
            C::Ttyp_package(pack) => {
                self.w.write_block_header(8, 1);
                self.w.write_block_header(0, 2);
                self.path(&pack.pack_path);
                self.list(&pack.pack_fields, |w, (lid, ct)| {
                    w.w.write_block_header(0, 2);
                    w.lid_loc(lid);
                    w.core_type(ct);
                });
            }
        }
        self.type_expr(ct.ctyp_type);
        self.env();
        self.loc_idx(ct.ctyp_loc);
        self.parsetree_attributes(&ct.ctyp_attributes);
    }

    fn typed_value_description(&mut self, vd: &tt::TypedValueDescription) {
        self.w.write_block_header(0, 7);
        self.ident(&vd.val_id);
        self.str_loc(&vd.val_name);
        self.core_type(&vd.val_desc);
        let key = (vd.val_id.stamp(), vd.val_id.name().to_string());
        match self.values.get(&key).cloned() {
            Some(val) => self.value_description(&val),
            None => {
                let val = ValueDescription {
                    val_type: vd.val_desc.ctyp_type,
                    val_kind: ValueKind::ValReg,
                    val_loc: self.arena.to_location(vd.val_loc),
                    val_attributes: Vec::new(),
                    val_path: None,
                };
                self.value_description(&val);
            }
        }
        self.strings(&vd.val_prim);
        self.loc_idx(vd.val_loc);
        self.parsetree_attributes(&vd.val_attributes);
    }

    fn typed_variance(&mut self, v: &crate::types::Variance) {
        self.int(if v.is_covariant() {
            0
        } else if v.is_contravariant() {
            1
        } else {
            2
        });
    }

    fn typed_type_declaration(&mut self, td: &tt::TypedTypeDeclaration) {
        self.w.write_block_header(0, 10);
        self.ident(&td.typ_id);
        self.str_loc(&td.typ_name);
        self.list(&td.typ_params, |w, (ct, v)| {
            w.w.write_block_header(0, 2);
            w.core_type(ct);
            w.typed_variance(v);
        });
        self.type_declaration(&td.typ_type);
        self.list(&td.typ_cstrs, |w, (a, b, loc)| {
            w.w.write_block_header(0, 3);
            w.core_type(a);
            w.core_type(b);
            w.loc_idx(*loc);
        });
        match &td.typ_kind {
            tt::TypedTypeKind::Ttype_abstract => self.w.write_int(0),
            tt::TypedTypeKind::Ttype_open => self.w.write_int(1),
            tt::TypedTypeKind::Ttype_variant(cds) => {
                self.w.write_block_header(0, 1);
                self.list(cds, |w, cd| {
                    w.w.write_block_header(0, 6);
                    w.ident(&cd.cd_id);
                    w.str_loc(&cd.cd_name);
                    match &cd.cd_args {
                        tt::TypedConstructorArguments::Cstr_tuple(cts) => {
                            w.w.write_block_header(0, 1);
                            w.list(cts, |w, ct| w.core_type(ct));
                        }
                        tt::TypedConstructorArguments::Cstr_record(lds) => {
                            w.w.write_block_header(1, 1);
                            w.list(lds, |w, ld| {
                                w.typed_label_declaration(
                                    &ld.ld_id,
                                    &ld.ld_name,
                                    ld.ld_mutable,
                                    ld.ld_optional,
                                    &ld.ld_type,
                                    ld.ld_loc,
                                    &ld.ld_attributes,
                                )
                            });
                        }
                    }
                    w.option(cd.cd_res.as_ref(), |w, ct| w.core_type(ct));
                    w.loc_idx(cd.cd_loc);
                    w.parsetree_attributes(&cd.cd_attributes);
                });
            }
            tt::TypedTypeKind::Ttype_record(lds) => {
                self.w.write_block_header(1, 1);
                self.list(lds, |w, ld| {
                    w.typed_label_declaration(
                        &ld.ld_id,
                        &ld.ld_name,
                        ld.ld_mutable,
                        ld.ld_optional,
                        &ld.ld_type,
                        ld.ld_loc,
                        &ld.ld_attributes,
                    )
                });
            }
        }
        td.typ_private.marshal(&mut self.w);
        self.option(td.typ_manifest.as_ref(), |w, ct| w.core_type(ct));
        self.loc_idx(td.typ_loc);
        self.parsetree_attributes(&td.typ_attributes);
    }

    #[allow(clippy::too_many_arguments)]
    fn typed_label_declaration(
        &mut self,
        id: &Ident,
        name: &Located<String>,
        mutable: crate::parser::ast::MutableFlag,
        optional: bool,
        ct: &tt::TypedCoreType,
        loc: LocIdx,
        attrs: &Attributes,
    ) {
        self.w.write_block_header(0, 7);
        self.ident(id);
        self.str_loc(name);
        mutable.marshal(&mut self.w);
        self.bool(optional);
        self.core_type(ct);
        self.loc_idx(loc);
        self.parsetree_attributes(attrs);
    }

    fn type_extension(&mut self, te: &tt::TypeExtension) {
        self.w.write_block_header(0, 5);
        self.path(&te.tyext_path);
        self.list(&te.tyext_params, |w, (ct, v)| {
            w.w.write_block_header(0, 2);
            w.core_type(ct);
            w.typed_variance(v);
        });
        self.list(&te.tyext_constructors, |w, ext| {
            w.typed_extension_constructor(ext)
        });
        te.tyext_private.marshal(&mut self.w);
        self.parsetree_attributes(&te.tyext_attributes);
    }

    fn typed_extension_constructor(&mut self, ext: &tt::ExtensionConstructor) {
        self.w.write_block_header(0, 6);
        self.ident(&ext.ext_id);
        self.str_loc(&ext.ext_name);
        self.extension_constructor(&ext.ext_type);
        match &ext.ext_kind {
            tt::ExtensionConstructorKind::Text_decl(args, res) => {
                self.w.write_block_header(0, 2);
                match args {
                    tt::ConstructorArgument::Cstr_tuple(cts) => {
                        self.w.write_block_header(0, 1);
                        self.list(cts, |w, ct| w.core_type(ct));
                    }
                    tt::ConstructorArgument::Cstr_record(lds) => {
                        self.w.write_block_header(1, 1);
                        self.list(lds, |w, ld| {
                            w.typed_label_declaration(
                                &ld.ld_id,
                                &ld.ld_name,
                                ld.ld_mutable,
                                ld.ld_optional,
                                &ld.ld_type,
                                ld.ld_loc,
                                &ld.ld_attributes,
                            )
                        });
                    }
                }
                self.option(res.as_ref(), |w, ct| w.core_type(ct));
            }
            tt::ExtensionConstructorKind::Text_rebind(path, lid) => {
                self.w.write_block_header(1, 2);
                self.path(path);
                self.lid_loc(lid);
            }
        }
        self.loc_idx(ext.ext_loc);
        self.parsetree_attributes(&ext.ext_attributes);
    }

    // ------------------------------------------------------------------
    // cmt_infos
    // ------------------------------------------------------------------

    fn cmt_infos(
        &mut self,
        annots: BinaryAnnots<'_>,
        info: &CmtInfo<'_>,
        interface_digest: Option<[u8; 16]>,
    ) {
        self.w.write_block_header(0, 14);
        self.str(info.modname);
        match annots {
            BinaryAnnots::Implementation(s) => {
                self.w.write_block_header(1, 1);
                self.structure(s);
            }
            BinaryAnnots::Interface(sig, sig_type) => {
                self.w.write_block_header(2, 1);
                self.typed_signature(sig, sig_type);
            }
        }
        let deps = self.ctx.value_dependencies();
        self.list(&deps, |w, (vd1, vd2)| {
            w.w.write_block_header(0, 2);
            w.value_description(vd1);
            w.value_description(vd2);
        });
        self.w.write_int(0); // cmt_comments
        self.array(info.args, |w, arg| w.str(arg));
        self.str_option(info.sourcefile);
        self.str(info.builddir);
        self.strings(info.loadpath);
        self.digest_option(&info.source_digest);
        self.env(); // cmt_initial_env
        self.list(info.imports, |w, (name, digest)| {
            w.w.write_block_header(0, 2);
            w.str(name);
            w.digest_option(digest);
        });
        self.digest_option(&interface_digest);
        self.bool(true); // cmt_use_summaries
        // cmt_extra_info = {deprecated_used} (cmt_utils.ml:1-11).
        self.w.write_block_header(0, 1);
        let uses = self.ctx.deprecated_uses();
        self.list(&uses, |w, used| {
            w.w.write_block_header(0, 5);
            w.location(&used.source_loc);
            w.str(&used.text);
            w.option(used.migrate.as_ref(), |w, template| w.w.write_fragment(template));
            w.option(used.migrate_in_pipe_chain.as_ref(), |w, template| {
                w.w.write_fragment(template)
            });
            w.option(used.context.as_ref(), |w, context| {
                w.int(match context {
                    crate::types::context::DeprecatedContext::FunctionCall => 0,
                    crate::types::context::DeprecatedContext::Reference => 1,
                })
            });
        });
    }
}

fn instance_index(instance: Instance) -> i64 {
    match instance {
        Instance::Array => 0,
        Instance::ArrayBuffer => 1,
        Instance::BigInt64Array => 2,
        Instance::BigUint64Array => 3,
        Instance::Blob => 4,
        Instance::DataView => 5,
        Instance::Date => 6,
        Instance::File => 7,
        Instance::Float32Array => 8,
        Instance::Float64Array => 9,
        Instance::Int16Array => 10,
        Instance::Int32Array => 11,
        Instance::Int8Array => 12,
        Instance::Promise => 13,
        Instance::RegExp => 14,
        Instance::Uint16Array => 15,
        Instance::Uint32Array => 16,
        Instance::Uint8Array => 17,
        Instance::Uint8ClampedArray => 18,
        Instance::Set => 19,
        Instance::Map => 20,
        Instance::WeakSet => 21,
        Instance::WeakMap => 22,
    }
}

/// MD5 digest, as computed by OCaml's `Digest.string`/`Digest.file`.
pub fn md5(data: &[u8]) -> [u8; 16] {
    const S: [u32; 64] = [
        7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 5, 9, 14, 20, 5, 9, 14, 20, 5,
        9, 14, 20, 5, 9, 14, 20, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 6, 10,
        15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
    ];
    let k: Vec<u32> = (0..64)
        .map(|i| ((i as f64 + 1.0).sin().abs() * 4294967296.0) as u32)
        .collect();
    let mut a0: u32 = 0x67452301;
    let mut b0: u32 = 0xefcdab89;
    let mut c0: u32 = 0x98badcfe;
    let mut d0: u32 = 0x10325476;

    let mut msg = data.to_vec();
    let bit_len = (data.len() as u64).wrapping_mul(8);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_le_bytes());

    for chunk in msg.chunks(64) {
        let m: Vec<u32> = chunk
            .chunks(4)
            .map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
            .collect();
        let (mut a, mut b, mut c, mut d) = (a0, b0, c0, d0);
        for i in 0..64 {
            let (f, g) = match i / 16 {
                0 => ((b & c) | (!b & d), i),
                1 => ((d & b) | (!d & c), (5 * i + 1) % 16),
                2 => (b ^ c ^ d, (3 * i + 5) % 16),
                _ => (c ^ (b | !d), (7 * i) % 16),
            };
            let f = f.wrapping_add(a).wrapping_add(k[i]).wrapping_add(m[g]);
            a = d;
            d = c;
            c = b;
            b = b.wrapping_add(f.rotate_left(S[i]));
        }
        a0 = a0.wrapping_add(a);
        b0 = b0.wrapping_add(b);
        c0 = c0.wrapping_add(c);
        d0 = d0.wrapping_add(d);
    }

    let mut out = [0u8; 16];
    out[0..4].copy_from_slice(&a0.to_le_bytes());
    out[4..8].copy_from_slice(&b0.to_le_bytes());
    out[8..12].copy_from_slice(&c0.to_le_bytes());
    out[12..16].copy_from_slice(&d0.to_le_bytes());
    out
}

#[cfg(test)]
mod tests {
    use super::md5;

    fn hex(d: [u8; 16]) -> String {
        d.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn md5_matches_reference_vectors() {
        assert_eq!(hex(md5(b"")), "d41d8cd98f00b204e9800998ecf8427e");
        assert_eq!(
            hex(md5(b"The quick brown fox jumps over the lazy dog")),
            "9e107d9d372bb6826bd81d3542a419d6"
        );
        assert_eq!(hex(md5(&[b'a'; 200])), hex(md5(&vec![b'a'; 200])));
    }
}
