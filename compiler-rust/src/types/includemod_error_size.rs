//! `Includemod.is_big` (compiler/ml/includemod.ml:635-667).
//!
//! `report_error` prints every entry of an inclusion error list but the last
//! one only when its symptom is small: the symptom's heap representation,
//! counting each distinct reachable block once (its header plus its fields,
//! or its header alone when it has no scannable fields, such as a string),
//! must not exceed [`ERROR_SIZE`] words. A big entry prints as `...`.
//!
//! The Rust symptom is not an OCaml heap value, so this module counts the
//! words that OCaml's representation of the same symptom occupies: it walks
//! the Rust declarations in the field order of `types.mli` and adds the size
//! of the block each OCaml value is. Immediate values (integers, booleans,
//! constant constructors, `[]`, `None`) are not blocks and count nothing.
//!
//! The expected side of a symptom is `Subst.modtype subst mty2` (and
//! `Subst.modtype_declaration subst info2`), a copy that `includemod.ml` makes
//! when it raises the error. The copy is counted as `Subst` builds it: type
//! nodes by their representative (no `Tlink`), once per copy session, with a
//! fresh `ref Mnil` and rebuilt `Pdot` paths, type variables of the typing
//! graph kept, and every use of an identifier bound by a copied signature
//! sharing one `Pident` (subst.ml:132-389).
//!
//! A block shared by several parts of the symptom counts once, as
//! `List.memq` makes it in OCaml. Sharing is followed through the identities
//! Rust keeps for OCaml's physical ones:
//!
//! - type nodes, `abbrev_memo ref`, `field_mutability ref` and
//!   `row_field option ref` cells by their arena handles;
//! - signatures, type declarations and path prefixes by their `Arc`s;
//! - variant layouts by their `layout_ref` handle, whose tags share their
//!   name string with the constructor's `Ident.t` and their literal with the
//!   constructor's `cd_runtime_tag` (variant_layout.ml `get_tag`);
//! - an `Ident.t` by its stamp and name, its name string being its own;
//! - a `Location.t` and a `Lexing.position` by their coordinates: a
//!   position record is made once per token boundary by the scanner and a
//!   location once per source node, which declarations derived from that
//!   node share (typedecl.ml gives `t#row` the `ptype_loc` of `t`); and a
//!   file name string by the file, one per compiled source.
//!
//! String contents never count, so the decision does not depend on the
//! length of identifiers or of the source file name.

use std::collections::HashSet;
use std::sync::Arc;

use super::Path;
use super::context::TypeContext;
use super::decl::{
    Attribute, AttributePayload, ConstructorArguments, ConstructorDeclaration,
    ExtensionConstructor, LabelDeclaration, ModtypeDeclaration, ModuleDeclaration, ModuleType,
    PrimKind, RecordRepresentation, Signature, SignatureItem, TypeDeclaration, TypeInlinedType,
    TypeKind, ValueDescription, ValueKind,
};
use super::includemod::{InclusionSubst, SubstEntry};
use super::type_expr::{
    AbbrevMemo, AbbrevMemoRef, FieldMutability, MutabilityRef, PathBlock, PathBlockOwner, RowField,
    RowFieldRef, TypeDesc, TypeExprRef,
};
use super::variant_runtime::{
    Block as VariantBlock, BlockType, ConstructorCase, LayoutRef, LiteralTag, Tag,
};
use crate::ident::Ident;
use crate::location::{Location, Position};
use crate::types::DeclLoc;
use crate::types::asttypes::{ArgLabel, Located};
use crate::types::external_ffi_types::{
    Attr, Cst, DeclKind, ExternalFfi, InlineConst, Label, ModuleBindName, ModuleSource,
};

/// `Includemod.error_size`, in heap words.
const ERROR_SIZE: usize = 400;

/// Raised as soon as the count exceeds [`ERROR_SIZE`], like `Big`.
struct Big;

type Walk = Result<(), Big>;

/// `is_big (Module_types (mty1, Subst.modtype subst mty2))`.
pub(crate) fn module_types_is_big(
    ctx: &TypeContext,
    actual: &ModuleType,
    expected: &ModuleType,
    subst: &InclusionSubst,
) -> bool {
    let mut size = ErrorSize::new(ctx, subst);
    let walk = (|| {
        // Module_types (mty1, mty2)
        size.block(4, 2)?;
        size.module_type(actual)?;
        size.substituted(|size| size.module_type(expected))
    })();
    walk.is_err()
}

/// `is_big (Modtype_infos (id, info1, Subst.modtype_declaration subst info2))`.
pub(crate) fn modtype_infos_is_big(
    ctx: &TypeContext,
    id: &Ident,
    actual: &ModtypeDeclaration,
    expected: &ModtypeDeclaration,
    subst: &InclusionSubst,
) -> bool {
    let mut size = ErrorSize::new(ctx, subst);
    let walk = (|| {
        size.block(5, 3)?;
        size.ident(id)?;
        size.modtype_declaration(actual)?;
        size.substituted(|size| size.modtype_declaration(expected))
    })();
    walk.is_err()
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PositionKey {
    file: u32,
    line: i32,
    bol: i32,
    cnum: i32,
}

fn position_key(pos: &Position) -> PositionKey {
    PositionKey {
        file: pos.file_name.0,
        line: pos.line,
        bol: pos.bol,
        cnum: pos.cnum,
    }
}

type IdentKey = (i32, usize);

type AttributeKey = (String, PositionKey, PositionKey);

fn ident_key(id: &Ident) -> IdentKey {
    (id.stamp(), id.name().as_ptr() as usize)
}

struct ErrorSize<'a> {
    ctx: &'a TypeContext,
    /// The `subst` the expected side is copied with.
    subst: &'a InclusionSubst,
    words: usize,
    idents: HashSet<IdentKey>,
    /// Type nodes by copy session (0 for the nodes themselves) and node.
    types: HashSet<(u32, TypeExprRef)>,
    /// Walking the `Subst` copy rather than the declarations themselves.
    substituted: bool,
    /// The current `with_copy_session` of `Subst` (subst.ml:235-306).
    session: u32,
    sessions: u32,
    /// Identifiers bound by a copied signature or functor: `Subst` maps each
    /// to one `Pident id'` (`Mty_ident (Pident id')`) shared by every use
    /// (subst.ml:310-336).
    renamed: HashSet<IdentKey>,
    abbrev_refs: HashSet<AbbrevMemoRef>,
    mutability_refs: HashSet<MutabilityRef>,
    row_field_refs: HashSet<RowFieldRef>,
    layouts: HashSet<LayoutRef>,
    /// Constructors whose `cd_runtime_tag` block has been counted, keyed by
    /// the constructor ident: the layout tag shares it.
    runtime_tags: HashSet<IdentKey>,
    signatures: HashSet<usize>,
    type_declarations: HashSet<usize>,
    paths: HashSet<usize>,
    positions: HashSet<PositionKey>,
    locations: HashSet<(PositionKey, PositionKey, bool)>,
    files: HashSet<u32>,
    inline_const_name: bool,
    attributes: HashSet<AttributeKey>,
    /// `@tag` attributes whose decoded name has been counted: a variant's
    /// layout holds that string as its tag name.
    tag_names: HashSet<AttributeKey>,
    /// The static `Rpresent None` of the type checker.
    rpresent_none: bool,
    /// The `Tconstr` path blocks counted (see [`PathBlock`]).
    path_blocks: HashSet<PathBlockKey>,
    /// The arrow argument label blocks counted, by allocation.
    labels: HashSet<usize>,
}

/// The identity of a path block of the error.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum PathBlockKey {
    /// The path allocated for this type node.
    Node(TypeExprRef),
    /// The global `Predef.path_X`, by the stamp of its ident.
    Predef(i32),
    /// A path written into an existing node.
    Token(u32),
    /// The target path of a substitution entry.
    Target(Target),
    /// The target `Mty_ident` of a module type substitution entry.
    TargetMty(Target),
}

/// A substitution entry of the expected side's copy.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Target {
    /// An `add_*` call of includemod's `subst`.
    Outer(SubstEntry),
    /// The renaming of a bound identifier by `Subst.signature` or
    /// `Subst.modtype` on a functor.
    Renamed(IdentKey),
}

impl<'a> ErrorSize<'a> {
    fn new(ctx: &'a TypeContext, subst: &'a InclusionSubst) -> Self {
        Self {
            ctx,
            subst,
            words: 0,
            idents: HashSet::default(),
            types: HashSet::default(),
            substituted: false,
            session: 0,
            sessions: 0,
            renamed: HashSet::default(),
            abbrev_refs: HashSet::default(),
            mutability_refs: HashSet::default(),
            row_field_refs: HashSet::default(),
            layouts: HashSet::default(),
            runtime_tags: HashSet::default(),
            signatures: HashSet::default(),
            type_declarations: HashSet::default(),
            paths: HashSet::default(),
            positions: HashSet::default(),
            locations: HashSet::default(),
            files: HashSet::default(),
            inline_const_name: false,
            attributes: HashSet::default(),
            tag_names: HashSet::default(),
            rpresent_none: false,
            path_blocks: HashSet::default(),
            labels: HashSet::default(),
        }
    }

    /// Walk `f` over the `Subst` copy of what it visits.
    fn substituted(&mut self, f: impl FnOnce(&mut Self) -> Walk) -> Walk {
        let outer = std::mem::replace(&mut self.substituted, true);
        let walk = f(self);
        self.substituted = outer;
        walk
    }

    /// Walk `f` over values `Subst` keeps rather than copies.
    fn original(&mut self, f: impl FnOnce(&mut Self) -> Walk) -> Walk {
        let substituted = std::mem::replace(&mut self.substituted, false);
        let session = std::mem::replace(&mut self.session, 0);
        let walk = f(self);
        self.substituted = substituted;
        self.session = session;
        walk
    }

    /// `with_copy_session`: copies made in one session share their copy of a
    /// shared node; another session copies it again.
    fn copy_session(&mut self, f: impl FnOnce(&mut Self) -> Walk) -> Walk {
        if !self.substituted {
            return f(self);
        }
        self.sessions += 1;
        let outer = std::mem::replace(&mut self.session, self.sessions);
        let walk = f(self);
        self.session = outer;
        walk
    }

    /// A block with `fields` scannable fields: its header and its fields.
    /// `_tag` is the OCaml constructor tag, kept for reading the walk.
    fn block(&mut self, _tag: u8, fields: usize) -> Walk {
        self.add(1 + fields)
    }

    /// A string, or any block without scannable fields: its header only.
    fn string(&mut self) -> Walk {
        self.add(1)
    }

    fn add(&mut self, words: usize) -> Walk {
        self.words += words;
        if self.words > ERROR_SIZE {
            Err(Big)
        } else {
            Ok(())
        }
    }

    /// `'a list`: one cons block per element.
    fn list<T>(&mut self, items: &[T], mut item: impl FnMut(&mut Self, &T) -> Walk) -> Walk {
        for value in items {
            self.block(0, 2)?;
            item(self, value)?;
        }
        Ok(())
    }

    /// `Some x`: a block holding `x`.
    fn option<T>(&mut self, value: Option<&T>, item: impl FnOnce(&mut Self, &T) -> Walk) -> Walk {
        match value {
            None => Ok(()),
            Some(value) => {
                self.block(0, 1)?;
                item(self, value)
            }
        }
    }

    fn option_string(&mut self, value: Option<&String>) -> Walk {
        self.option(value, |size, _| size.string())
    }

    // Ident.t = {stamp; name; flags}
    fn ident(&mut self, id: &Ident) -> Walk {
        if !self.idents.insert(ident_key(id)) {
            return Ok(());
        }
        self.block(0, 3)?;
        self.string()
    }

    /// A path the walk reaches as it is (not through a `Subst` copy).
    fn path(&mut self, path: &Path) -> Walk {
        debug_assert!(!self.substituted);
        match path {
            Path::Pident(id) => {
                self.block(0, 1)?;
                self.ident(id)
            }
            Path::Pdot(prefix, _, _) => {
                self.block(1, 3)?;
                self.shared_path(prefix)?;
                self.string()
            }
            Path::Papply(functor, argument) => {
                self.block(2, 2)?;
                self.shared_path(functor)?;
                self.shared_path(argument)
            }
        }
    }

    fn shared_path(&mut self, path: &Arc<Path>) -> Walk {
        if !self.paths.insert(Arc::as_ptr(path) as usize) {
            return Ok(());
        }
        self.path(path)
    }

    fn renamed_ident(&self, path: &Path) -> Option<Target> {
        match path {
            Path::Pident(id) if self.renamed.contains(&ident_key(id)) => {
                Some(Target::Renamed(ident_key(id)))
            }
            _ => None,
        }
    }

    /// The target path of a substitution entry: one block for every use.
    fn target_path(&mut self, target: Target, path: &Path) -> Walk {
        if !self.path_blocks.insert(PathBlockKey::Target(target)) {
            return Ok(());
        }
        self.original(|size| size.path(path))
    }

    /// `Subst.type_path s p` (subst.ml:87-102). `kept` is the block of `p`
    /// itself, which the copy returns when it does not replace it.
    fn copied_type_path(&mut self, path: &Path, kept: Option<PathBlockKey>) -> Walk {
        if let Some(target) = self.renamed_ident(path) {
            return self.target_path(target, path);
        }
        if let Some((target, entry)) = self.subst.type_target(path) {
            return self.target_path(Target::Outer(entry), &target);
        }
        match path {
            Path::Pident(_) => {
                if let Some(kept) = kept
                    && !self.path_blocks.insert(kept)
                {
                    return Ok(());
                }
                self.original(|size| size.path(path))
            }
            _ => self.copied_dotted_path(path),
        }
    }

    /// `Subst.module_path s p` (subst.ml:69-75). `kept` is the address of
    /// `p`, returned by the copy when it is an unreplaced `Pident`.
    fn copied_module_path(&mut self, path: &Path, kept: Option<usize>) -> Walk {
        if let Some(target) = self.renamed_ident(path) {
            return self.target_path(target, path);
        }
        if let Some((target, entry)) = self.subst.module_target(path) {
            return self.target_path(Target::Outer(entry), &target);
        }
        match path {
            Path::Pident(_) => {
                if let Some(kept) = kept
                    && !self.paths.insert(kept)
                {
                    return Ok(());
                }
                self.original(|size| size.path(path))
            }
            _ => self.copied_dotted_path(path),
        }
    }

    /// A `Pdot` or `Papply` rebuilt around the copies of its module paths.
    fn copied_dotted_path(&mut self, path: &Path) -> Walk {
        match path {
            Path::Pident(_) => unreachable!(),
            Path::Pdot(prefix, _, _) => {
                self.block(1, 3)?;
                self.copied_module_path(prefix, Some(Arc::as_ptr(prefix) as usize))?;
                self.string()
            }
            Path::Papply(functor, argument) => {
                self.block(2, 2)?;
                self.copied_module_path(functor, Some(Arc::as_ptr(functor) as usize))?;
                self.copied_module_path(argument, Some(Arc::as_ptr(argument) as usize))
            }
        }
    }

    /// The `Mty_ident` target of a module type substitution, if any.
    fn modtype_target(&self, path: &Path) -> Option<(Target, Path)> {
        if let Some(target) = self.renamed_ident(path) {
            return Some((target, path.clone()));
        }
        match path {
            Path::Pident(_) => self
                .subst
                .modtype_target(path)
                .map(|(target, entry)| (Target::Outer(entry), target)),
            _ => None,
        }
    }

    /// `Subst.modtype_path s p` (subst.ml:77-86): the path inside the
    /// target `Mty_ident` of `p`, or `p` rebuilt.
    fn copied_modtype_path(&mut self, path: &Path) -> Walk {
        if let Some((target, target_path)) = self.modtype_target(path) {
            return self.target_path(target, &target_path);
        }
        match path {
            Path::Pident(_) => self.original(|size| size.path(path)),
            _ => self.copied_dotted_path(path),
        }
    }

    fn longident(&mut self, lid: &crate::parser::longident::Longident) -> Walk {
        use crate::parser::longident::Longident;
        match lid {
            Longident::Lident(_) => {
                self.block(0, 1)?;
                self.string()
            }
            Longident::Ldot(prefix, _) => {
                self.block(1, 2)?;
                self.longident(prefix)?;
                self.string()
            }
            Longident::Lapply(functor, argument) => {
                self.block(2, 2)?;
                self.longident(functor)?;
                self.longident(argument)
            }
        }
    }

    // Lexing.position = {pos_fname; pos_lnum; pos_bol; pos_cnum}
    fn position(&mut self, pos: &Position) -> Walk {
        if !self.positions.insert(position_key(pos)) {
            return Ok(());
        }
        self.block(0, 4)?;
        if self.files.insert(pos.file_name.0) {
            self.string()?;
        }
        Ok(())
    }

    // Location.t = {loc_start; loc_end; loc_ghost}
    fn location(&mut self, loc: &Location) -> Walk {
        let key = (
            position_key(&loc.loc_start),
            position_key(&loc.loc_end),
            loc.loc_ghost,
        );
        if !self.locations.insert(key) {
            return Ok(());
        }
        self.block(0, 3)?;
        self.position(&loc.loc_start)?;
        self.position(&loc.loc_end)
    }

    fn decl_loc(&mut self, loc: DeclLoc) -> Walk {
        let loc = self.ctx.resolve_loc(loc);
        self.location(&loc)
    }

    // 'a loc = {txt; loc}
    fn string_loc(&mut self, located: &Located<String, DeclLoc>) -> Walk {
        self.block(0, 2)?;
        self.string()?;
        self.decl_loc(located.loc)
    }

    /// An attribute is shared by every declaration it is copied to
    /// (typedecl.ml `copy_tag_attr_from_decl`): its name location identifies
    /// it.
    fn attribute_key(&self, attr: &Attribute) -> AttributeKey {
        let loc = self.ctx.resolve_loc(attr.attr_name.loc);
        (
            attr.attr_name.txt.clone(),
            position_key(&loc.loc_start),
            position_key(&loc.loc_end),
        )
    }

    // attribute = string loc * payload
    fn attributes(&mut self, attrs: &[Attribute]) -> Walk {
        self.list(attrs, |size, attr| {
            if !size.attributes.insert(size.attribute_key(attr)) {
                return Ok(());
            }
            size.block(0, 2)?;
            size.string_loc(&attr.attr_name)?;
            size.payload(attr)
        })
    }

    /// The parse tree of an attribute payload: `PStr []` when empty, else
    /// `PStr [{pstr_desc = Pstr_eval (e, []); pstr_loc}]` where `e` is the
    /// payload expression and `pstr_loc` a record of its own with the
    /// positions of `e.pexp_loc`. Rust keeps the decoded payload, not the
    /// expression's location, so the positions of `pexp_loc` count as the
    /// payload's own.
    fn payload(&mut self, attr: &Attribute) -> Walk {
        // PStr structure
        self.block(0, 1)?;
        match &attr.attr_payload {
            AttributePayload::Empty => return Ok(()),
            AttributePayload::Structure(items) if items.is_empty() => return Ok(()),
            AttributePayload::StrTuple(items) if items.is_empty() => return Ok(()),
            _ => {}
        }
        // [{pstr_desc = Pstr_eval (e, []); pstr_loc}]
        self.block(0, 2)?;
        self.block(0, 2)?;
        self.block(0, 2)?;
        match &attr.attr_payload {
            AttributePayload::StrTuple(items) => {
                // {pexp_desc = Pexp_tuple [...]; pexp_loc; pexp_attributes}
                self.block(0, 3)?;
                self.block(0, 1)?;
                for _ in items {
                    self.block(0, 2)?;
                    self.block(0, 3)?;
                    self.string_constant()?;
                    self.payload_location()?;
                }
            }
            AttributePayload::Bool(_) | AttributePayload::Ident(_) => {
                // Pexp_construct / Pexp_ident ({txt = Lident s; loc}, ...)
                self.block(0, 3)?;
                self.block(0, 2)?;
                self.block(0, 2)?;
                self.block(0, 1)?;
                self.string()?;
                self.payload_location()?;
            }
            AttributePayload::Int(_)
            | AttributePayload::IntLiteral(_)
            | AttributePayload::Float(_)
            | AttributePayload::BigInt(_) => {
                // Pexp_constant (Pconst_integer (s, suffix))
                self.block(0, 3)?;
                self.block(2, 1)?;
                self.block(0, 2)?;
                self.string()?;
            }
            AttributePayload::Str(_)
            | AttributePayload::Deprecated { .. }
            | AttributePayload::Structure(_)
            | AttributePayload::Empty => {
                self.block(0, 3)?;
                self.string_constant()?;
                if attr.attr_name.txt == "tag" {
                    self.tag_names.insert(self.attribute_key(attr));
                }
            }
        }
        // pexp_loc, then pstr_loc sharing its positions
        self.payload_location()?;
        self.block(0, 3)
    }

    /// `Pexp_constant (Pconst_string {source; semantic})`.
    fn string_constant(&mut self) -> Walk {
        self.block(2, 1)?;
        self.block(2, 1)?;
        self.block(0, 2)?;
        self.string()?;
        self.string()
    }

    /// A location of the payload expression, with positions of its own.
    fn payload_location(&mut self) -> Walk {
        self.block(0, 3)?;
        self.block(0, 4)?;
        self.block(0, 4)
    }

    fn module_type(&mut self, mty: &ModuleType) -> Walk {
        if self.substituted {
            return self.copied_module_type(mty);
        }
        match mty {
            ModuleType::MtyIdent(path) => {
                self.block(0, 1)?;
                self.path(path)
            }
            ModuleType::MtySignature(sig) => {
                self.block(1, 1)?;
                self.signature(sig)
            }
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                self.block(2, 3)?;
                self.ident(param)?;
                self.option(param_type.as_deref(), |size, mty| size.module_type(mty))?;
                self.module_type(result)
            }
            ModuleType::MtyAlias(_, path) => {
                self.block(3, 2)?;
                self.path(path)
            }
        }
    }

    /// `Subst.modtype s mty` (subst.ml:326-337).
    fn copied_module_type(&mut self, mty: &ModuleType) -> Walk {
        match mty {
            ModuleType::MtyIdent(path) => {
                if let Some((target, target_path)) = self.modtype_target(path) {
                    // `Tbl.find id s.modtypes`: the shared `Mty_ident`.
                    if !self.path_blocks.insert(PathBlockKey::TargetMty(target)) {
                        return Ok(());
                    }
                    self.block(0, 1)?;
                    return self.target_path(target, &target_path);
                }
                self.block(0, 1)?;
                match path {
                    // The original `mty`.
                    Path::Pident(_) => self.original(|size| size.path(path)),
                    _ => self.copied_dotted_path(path),
                }
            }
            ModuleType::MtySignature(sig) => {
                self.block(1, 1)?;
                self.signature(sig)
            }
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                // `Mty_functor (Ident.rename id, may_map (modtype s) arg,
                //  modtype (add_module id (Pident id') s) res)`
                self.block(2, 3)?;
                self.ident(param)?;
                self.option(param_type.as_deref(), |size, mty| size.module_type(mty))?;
                self.renamed.insert(ident_key(param));
                self.module_type(result)
            }
            ModuleType::MtyAlias(_, path) => {
                self.block(3, 2)?;
                self.copied_module_path(path, None)
            }
        }
    }

    fn signature(&mut self, sig: &Arc<Signature>) -> Walk {
        if self.substituted {
            for item in sig.iter() {
                if let SignatureItem::SigType(id, ..)
                | SignatureItem::SigModule(id, ..)
                | SignatureItem::SigModtype(id, _) = item
                {
                    self.renamed.insert(ident_key(id));
                }
            }
        } else if !self.signatures.insert(Arc::as_ptr(sig) as usize) {
            return Ok(());
        }
        let items: Vec<&SignatureItem> = sig
            .iter()
            .filter(|item| !matches!(item, SignatureItem::SigClass | SignatureItem::SigClassType))
            .collect();
        self.list(&items, |size, item| size.signature_item(item))
    }

    fn signature_item(&mut self, item: &SignatureItem) -> Walk {
        match item {
            SignatureItem::SigValue(id, vd) => {
                self.block(0, 2)?;
                self.ident(id)?;
                self.value_description(vd)
            }
            SignatureItem::SigType(id, decl, _) => {
                self.block(1, 3)?;
                self.ident(id)?;
                self.shared_type_declaration(decl)
            }
            SignatureItem::SigTypext(id, ext, _) => {
                self.block(2, 3)?;
                self.ident(id)?;
                self.extension_constructor(ext)
            }
            SignatureItem::SigModule(id, md, _) => {
                self.block(3, 3)?;
                self.ident(id)?;
                self.module_declaration(md)
            }
            SignatureItem::SigModtype(id, mtd) => {
                self.block(4, 2)?;
                self.ident(id)?;
                self.modtype_declaration(mtd)
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => Ok(()),
        }
    }

    // {md_type; md_attributes; md_loc}
    fn module_declaration(&mut self, md: &ModuleDeclaration) -> Walk {
        self.block(0, 3)?;
        self.module_type(&md.md_type)?;
        self.attributes(&md.md_attributes)?;
        self.decl_loc(md.md_loc)
    }

    // {mtd_type; mtd_attributes; mtd_loc}
    fn modtype_declaration(&mut self, mtd: &ModtypeDeclaration) -> Walk {
        self.block(0, 3)?;
        self.option(mtd.mtd_type.as_ref(), |size, mty| size.module_type(mty))?;
        self.attributes(&mtd.mtd_attributes)?;
        self.decl_loc(mtd.mtd_loc)
    }

    // {val_type; val_kind; val_loc; val_attributes}
    fn value_description(&mut self, vd: &ValueDescription) -> Walk {
        self.block(0, 4)?;
        self.copy_session(|size| size.type_expr(vd.val_type))?;
        if let ValueKind::ValPrim(prim) = &vd.val_kind {
            // Val_prim {prim_name; prim_arity; prim_alloc; prim_kind;
            //           prim_from_constructor}
            self.block(0, 1)?;
            self.block(0, 5)?;
            // `Primitive.parse_declaration` names every inline constant with
            // the one static `""`.
            if !matches!(prim.prim_kind, PrimKind::KindInlineConst(_))
                || !std::mem::replace(&mut self.inline_const_name, true)
            {
                self.string()?;
            }
            match &prim.prim_kind {
                PrimKind::KindIntrinsic => {}
                PrimKind::KindExternal(ffi) => {
                    self.block(0, 1)?;
                    self.external_ffi(ffi, &prim.prim_name)?;
                }
                PrimKind::KindInlineConst(constant) => {
                    self.block(1, 1)?;
                    self.inline_const(constant)?;
                }
            }
        }
        self.decl_loc(vd.val_loc)?;
        self.attributes(&vd.val_attributes)
    }

    /// The declaration and module names of an external are its primitive
    /// name string itself unless an attribute payload names them
    /// (ast_external_process.ml `prim_name_or_pval_prim`).
    fn ffi_name(&mut self, name: &str, prim_name: &str) -> Walk {
        if name == prim_name {
            return Ok(());
        }
        self.string()
    }

    fn external_ffi(&mut self, ffi: &ExternalFfi, prim_name: &str) -> Walk {
        match ffi {
            ExternalFfi::FfiBs(params, _, decl) => {
                self.block(0, 3)?;
                // param = {arg_type; arg_label}
                self.list(params, |size, param| {
                    size.block(0, 2)?;
                    size.ffi_attr(&param.arg_type)
                })?;
                // {kind; module_; scopes; variadic; effective_arity}
                self.block(0, 5)?;
                match &decl.kind {
                    DeclKind::DeclVal { name }
                    | DeclKind::DeclSend { name }
                    | DeclKind::DeclNew { name }
                    | DeclKind::DeclGet { name }
                    | DeclKind::DeclSet { name } => {
                        self.block(0, 1)?;
                        self.ffi_name(name, prim_name)?;
                    }
                    DeclKind::DeclGetIndex | DeclKind::DeclSetIndex => {}
                }
                self.option(decl.module_.as_ref(), |size, source| match source {
                    ModuleSource::ModuleItself => Ok(()),
                    ModuleSource::ModuleNamed(name) => {
                        size.block(0, 1)?;
                        // {bundle; module_bind_name; import_attributes}
                        size.block(0, 3)?;
                        size.ffi_name(&name.bundle, prim_name)?;
                        if let ModuleBindName::PhintName(_) = &name.module_bind_name {
                            size.block(0, 1)?;
                            size.string()?;
                        }
                        size.option(name.import_attributes.as_ref(), |size, attrs| {
                            size.list(attrs, |size, _| {
                                size.block(0, 2)?;
                                size.string()?;
                                size.string()
                            })
                        })
                    }
                })?;
                self.list(&decl.scopes, |size, _| size.string())
            }
            ExternalFfi::FfiObjCreate(params) => {
                self.block(1, 1)?;
                // obj_param = {obj_arg_type; obj_arg_label}
                self.list(params, |size, param| {
                    size.block(0, 2)?;
                    size.ffi_attr(&param.obj_arg_type)?;
                    match &param.obj_arg_label {
                        Label::ObjEmpty => Ok(()),
                        Label::ObjLabel { .. } => {
                            size.block(0, 1)?;
                            size.string()
                        }
                        Label::ObjOptional { .. } => {
                            size.block(1, 2)?;
                            size.string()
                        }
                    }
                })
            }
        }
    }

    fn ffi_attr(&mut self, attr: &Attr) -> Walk {
        let pairs = |size: &mut Self, descr: &Vec<(String, String)>| {
            size.list(descr, |size, _| {
                size.block(0, 2)?;
                size.string()?;
                size.string()
            })
        };
        match attr {
            Attr::PolyVarString { descr } => {
                self.block(0, 1)?;
                pairs(self, descr)
            }
            Attr::PolyVar { descr } => {
                self.block(1, 1)?;
                self.option(descr.as_ref(), |size, descr| pairs(size, descr))
            }
            Attr::Int(cases) => {
                self.block(2, 1)?;
                self.list(cases, |size, _| {
                    size.block(0, 2)?;
                    size.string()
                })
            }
            Attr::ArgCst(cst) => {
                self.block(3, 1)?;
                match cst {
                    Cst::ArgIntLit(_) => self.block(0, 1),
                    Cst::ArgStringLit(_) | Cst::ArgJsonLit(_) => {
                        self.block(1, 1)?;
                        self.string()
                    }
                }
            }
            Attr::ExternUnit | Attr::Nothing | Attr::Ignore | Attr::Unwrap => Ok(()),
        }
    }

    fn inline_const(&mut self, constant: &InlineConst) -> Walk {
        match constant {
            InlineConst::ConstString(_) | InlineConst::ConstFloat(_) => {
                self.block(0, 1)?;
                self.string()
            }
            InlineConst::ConstBool(_) => self.block(1, 1),
            // Const_int of int32: the boxed int32 is a custom block.
            InlineConst::ConstInt(_) => {
                self.block(2, 1)?;
                self.string()
            }
            InlineConst::ConstBigint { .. } => {
                self.block(3, 2)?;
                self.string()
            }
        }
    }

    fn shared_type_declaration(&mut self, decl: &Arc<TypeDeclaration>) -> Walk {
        if !self.substituted && !self.type_declarations.insert(Arc::as_ptr(decl) as usize) {
            return Ok(());
        }
        self.copy_session(|size| size.type_declaration(decl))
    }

    fn type_declaration(&mut self, decl: &TypeDeclaration) -> Walk {
        self.block(0, 12)?;
        self.list(&decl.type_params, |size, ty| size.type_expr(*ty))?;
        match &decl.type_kind {
            TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
            TypeKind::TypeRecord(labels, repr) => {
                self.block(0, 2)?;
                self.list(labels, |size, label| size.label_declaration(label))?;
                self.record_representation(repr)?;
            }
            TypeKind::TypeVariant(constructors, layout) => {
                self.block(1, 2)?;
                self.list(constructors, |size, cd| size.constructor_declaration(cd))?;
                let tag_attribute = decl
                    .type_attributes
                    .iter()
                    .find(|attr| attr.attr_name.txt == "tag")
                    .map(|attr| self.attribute_key(attr));
                self.layout(*layout, constructors, tag_attribute.as_ref())?;
            }
        }
        self.option(decl.type_manifest.as_ref(), |size, ty| size.type_expr(*ty))?;
        // Variance.t is an int
        self.list(&decl.type_variance, |_, _| Ok(()))?;
        // `Subst.type_declaration` resets `type_newtype_level`.
        if !self.substituted {
            self.option(decl.type_newtype_level.as_ref(), |size, _| size.block(0, 2))?;
        }
        self.decl_loc(decl.type_loc)?;
        self.attributes(&decl.type_attributes)?;
        // Record {type_name; labels}, which `Subst` keeps.
        self.original(|size| {
            size.list(&decl.type_inlined_types, |size, inlined| {
                let TypeInlinedType::Record { labels, .. } = inlined;
                size.block(0, 2)?;
                size.string()?;
                size.list(labels, |size, label| size.label_declaration(label))
            })
        })
    }

    fn record_representation(&mut self, repr: &RecordRepresentation) -> Walk {
        match repr {
            RecordRepresentation::RecordRegular | RecordRepresentation::RecordExtension => Ok(()),
            RecordRepresentation::RecordUnboxed(_) => self.block(0, 1),
            RecordRepresentation::RecordInlined { representation, .. } => {
                self.block(1, 2)?;
                self.string()?;
                // constructor_reference = {variant; position}
                self.block(0, 2)?;
                self.layout(representation.variant, &[], None)
            }
        }
    }

    // {ld_id; ld_runtime_name; ld_mutable; ld_optional; ld_type; ld_loc;
    //  ld_attributes}
    fn label_declaration(&mut self, label: &LabelDeclaration) -> Walk {
        self.block(0, 7)?;
        self.ident(&label.ld_id)?;
        self.option_string(label.ld_runtime_name.as_ref())?;
        self.type_expr(label.ld_type)?;
        self.decl_loc(label.ld_loc)?;
        self.attributes(&label.ld_attributes)
    }

    // {cd_id; cd_runtime_tag; cd_args; cd_res; cd_loc; cd_attributes}
    fn constructor_declaration(&mut self, cd: &ConstructorDeclaration) -> Walk {
        self.block(0, 6)?;
        self.ident(&cd.cd_id)?;
        if let Some(tag) = &cd.cd_runtime_tag
            && self.runtime_tags.insert(ident_key(&cd.cd_id))
        {
            self.block(0, 1)?;
            self.literal_tag(tag)?;
        }
        self.constructor_arguments(&cd.cd_args)?;
        self.option(cd.cd_res.as_ref(), |size, ty| size.type_expr(*ty))?;
        self.decl_loc(cd.cd_loc)?;
        self.attributes(&cd.cd_attributes)
    }

    fn constructor_arguments(&mut self, args: &ConstructorArguments) -> Walk {
        match args {
            ConstructorArguments::CstrTuple(tys) => {
                self.block(0, 1)?;
                self.list(tys, |size, ty| size.type_expr(*ty))
            }
            ConstructorArguments::CstrRecord(labels) => {
                self.block(1, 1)?;
                self.list(labels, |size, label| size.label_declaration(label))
            }
        }
    }

    fn extension_constructor(&mut self, ext: &ExtensionConstructor) -> Walk {
        self.copy_session(|size| size.extension_constructor_fields(ext))
    }

    // {ext_type_path; ext_type_params; ext_args; ext_ret_type; ext_private;
    //  ext_loc; ext_attributes; ext_is_exception}
    fn extension_constructor_fields(&mut self, ext: &ExtensionConstructor) -> Walk {
        self.block(0, 8)?;
        if self.substituted {
            self.copied_type_path(&ext.ext_type_path, None)?;
        } else {
            self.path(&ext.ext_type_path)?;
        }
        self.list(&ext.ext_type_params, |size, ty| size.type_expr(*ty))?;
        self.constructor_arguments(&ext.ext_args)?;
        self.option(ext.ext_ret_type.as_ref(), |size, ty| size.type_expr(*ty))?;
        self.decl_loc(ext.ext_loc)?;
        self.attributes(&ext.ext_attributes)
    }

    fn literal_tag(&mut self, tag: &LiteralTag) -> Walk {
        match tag {
            LiteralTag::String(_) | LiteralTag::Float(_) | LiteralTag::BigInt(_) => {
                self.block(0, 1)?;
                self.string()
            }
            LiteralTag::Int(_) | LiteralTag::Bool(_) => self.block(1, 1),
            LiteralTag::Null | LiteralTag::Undefined => Ok(()),
        }
    }

    /// `layout_ref = layout_state ref`, completed with
    /// `{unboxed; constructors; matching_facts}`.
    fn layout(
        &mut self,
        layout_ref: LayoutRef,
        constructors: &[ConstructorDeclaration],
        tag_attribute: Option<&AttributeKey>,
    ) -> Walk {
        if !self.layouts.insert(layout_ref) {
            return Ok(());
        }
        let layout = self.ctx.variant_layout(layout_ref);
        // ref (Complete layout)
        self.block(0, 1)?;
        self.block(0, 1)?;
        self.block(0, 3)?;
        // constructor_case array
        self.block(0, layout.constructors.len())?;
        for (position, case) in layout.constructors.iter().enumerate() {
            let owner = constructors.get(position).map(|cd| &cd.cd_id);
            match case {
                ConstructorCase::Constant(tag) => {
                    self.block(0, 1)?;
                    self.tag(tag, owner)?;
                }
                ConstructorCase::Block(block) => {
                    self.block(1, 1)?;
                    match block {
                        VariantBlock::Tagged(tagged) => {
                            // Tagged {tag; tag_name}
                            self.block(0, 1)?;
                            self.block(0, 2)?;
                            self.tag(&tagged.tag, owner)?;
                            self.option(tagged.tag_name.as_ref(), |size, _| {
                                size.tag_name(tag_attribute)
                            })?;
                        }
                        VariantBlock::Untagged { tag, block_type } => {
                            self.block(1, 2)?;
                            self.tag(tag, owner)?;
                            self.block_type(block_type)?;
                        }
                    }
                }
            }
        }
        // matching_facts = {tag_name; block_types; literal_tags; has_null;
        //                   has_undefined; has_other_literal}
        let facts = &layout.matching_facts;
        self.block(0, 6)?;
        self.option(facts.tag_name.as_ref(), |size, _| {
            size.tag_name(tag_attribute)
        })?;
        self.list(&facts.block_types, |size, block_type| {
            size.block_type(block_type)
        })?;
        // `literal_tags` (variant_runtime.ml `compute_matching_facts`): a
        // constant's literal is the payload of its tag's `Some`, already
        // counted, or a fresh `String name` sharing the tag's name string.
        for case in &layout.constructors {
            let ConstructorCase::Constant(tag) = case else {
                continue;
            };
            self.block(0, 2)?;
            if tag.literal.is_none() {
                self.block(0, 1)?;
            }
        }
        Ok(())
    }

    /// The decoded name of the type's `@tag` attribute
    /// (`Ast_untagged_variants.process_tag_name`).
    fn tag_name(&mut self, tag_attribute: Option<&AttributeKey>) -> Walk {
        match tag_attribute {
            Some(key) if !self.tag_names.insert(key.clone()) => Ok(()),
            _ => self.string(),
        }
    }

    /// `{name; literal}`: the name is the constructor's ident name and the
    /// literal its `cd_runtime_tag` (variant_layout.ml `get_tag`).
    fn tag(&mut self, tag: &Tag, owner: Option<&Ident>) -> Walk {
        self.block(0, 2)?;
        if owner.is_none() {
            self.string()?;
        }
        if let Some(literal) = &tag.literal {
            let shared = owner.is_some_and(|id| self.runtime_tags.contains(&ident_key(id)));
            if !shared {
                self.block(0, 1)?;
                self.literal_tag(literal)?;
            }
        }
        Ok(())
    }

    fn block_type(&mut self, block_type: &BlockType) -> Walk {
        match block_type {
            BlockType::Instance(_) => self.block(0, 1),
            _ => Ok(()),
        }
    }

    // type_expr = {mutable desc; mutable level; id}
    fn type_expr(&mut self, ty: TypeExprRef) -> Walk {
        if self.substituted {
            return self.copied_type_expr(ty);
        }
        if !self.types.insert((0, ty)) {
            return Ok(());
        }
        self.block(0, 3)?;
        let desc = self.ctx.get_desc(ty).into_desc();
        self.type_desc(ty, &desc)
    }

    /// The path of the `Tconstr` node `node`, counted once per block. The
    /// `Subst` copy keeps a `Pident` it does not rename and rebuilds the
    /// others (subst.ml:87-94).
    fn tconstr_path(&mut self, node: TypeExprRef, path: &Path, block: PathBlock) -> Walk {
        let key = match (block.owner(), path) {
            (PathBlockOwner::Own, _) => PathBlockKey::Node(node),
            (PathBlockOwner::Of(owner), _) => PathBlockKey::Node(owner),
            (PathBlockOwner::Predef, Path::Pident(id)) => PathBlockKey::Predef(id.stamp()),
            (PathBlockOwner::Predef, _) => PathBlockKey::Node(node),
            (PathBlockOwner::Token(token), _) => PathBlockKey::Token(token),
        };
        if self.substituted {
            return self.copied_type_path(path, Some(key));
        }
        if !self.path_blocks.insert(key) {
            return Ok(());
        }
        self.path(path)
    }

    fn type_desc(&mut self, node: TypeExprRef, desc: &TypeDesc) -> Walk {
        match desc {
            TypeDesc::Tvar(name) | TypeDesc::Tunivar(name) => {
                self.block(0, 1)?;
                self.option_string(name.as_ref())
            }
            TypeDesc::Tarrow { args, ret } => {
                self.block(1, 2)?;
                // arg = {lbl; typ}
                self.list(args, |size, arg| {
                    size.block(0, 2)?;
                    // A copy of the arrow shares each `lbl` block.
                    if let Some(block) = arg.label_block()
                        && !size.labels.insert(block)
                    {
                        return size.type_expr(arg.typ);
                    }
                    match arg.label() {
                        ArgLabel::Nolabel => {}
                        ArgLabel::Labelled(label) => {
                            size.block(0, 1)?;
                            size.string_loc(label)?;
                        }
                        ArgLabel::Optional(label) => {
                            size.block(1, 1)?;
                            size.string_loc(label)?;
                        }
                    }
                    size.type_expr(arg.typ)
                })?;
                self.type_expr(*ret)
            }
            TypeDesc::Ttuple(tys) => {
                self.block(2, 1)?;
                self.list(tys.as_slice(), |size, ty| size.type_expr(*ty))
            }
            TypeDesc::Tconstr {
                path,
                args,
                abbrev,
                path_block,
            } => {
                self.block(3, 3)?;
                self.tconstr_path(node, path, *path_block)?;
                self.list(args.as_slice(), |size, ty| size.type_expr(*ty))?;
                self.abbrev_ref(*abbrev)
            }
            TypeDesc::Tobject { fields } => {
                self.block(4, 1)?;
                self.type_expr(*fields)
            }
            TypeDesc::Tfield {
                mutability,
                typ,
                rest,
                ..
            } => {
                self.block(5, 4)?;
                self.string()?;
                self.mutability_ref(*mutability)?;
                self.type_expr(*typ)?;
                self.type_expr(*rest)
            }
            TypeDesc::Tnil => Ok(()),
            TypeDesc::Tlink(ty) | TypeDesc::Tsubst(ty) => {
                self.block(6, 1)?;
                self.type_expr(*ty)
            }
            TypeDesc::Tvariant(row) => {
                self.block(8, 1)?;
                // {row_fields; row_more; row_closed; row_fixed; row_name}
                self.block(0, 5)?;
                let fields = row.row_fields.to_vec();
                self.list(&fields, |size, (_, field)| {
                    size.block(0, 2)?;
                    size.string()?;
                    size.row_field(field)
                })?;
                self.type_expr(row.row_more)?;
                self.option(row.row_name.as_ref(), |size, (path, tys)| {
                    size.block(0, 2)?;
                    size.path(path)?;
                    size.list(tys, |size, ty| size.type_expr(*ty))
                })
            }
            TypeDesc::Tpoly { body, vars } => {
                self.block(10, 2)?;
                self.type_expr(*body)?;
                self.list(vars.as_slice(), |size, ty| size.type_expr(*ty))
            }
            TypeDesc::Tpackage { path, lids, args } => {
                self.block(11, 3)?;
                if self.substituted {
                    self.copied_modtype_path(path)?;
                } else {
                    self.path(path)?;
                }
                self.list(lids, |size, lid| size.longident(lid))?;
                self.list(args.as_slice(), |size, ty| size.type_expr(*ty))
            }
        }
    }

    /// `Subst.typexp_rec` (subst.ml:132-232): the copy of `ty`'s
    /// representative, made once per copy session. A type variable of the
    /// typing graph is kept, not copied.
    fn copied_type_expr(&mut self, ty: TypeExprRef) -> Walk {
        let ty = self.ctx.repr(ty);
        let desc = self.ctx.get_desc(ty).into_desc();
        if matches!(desc, TypeDesc::Tvar(_) | TypeDesc::Tunivar(_)) && !ty.is_store() {
            return self.original(|size| size.type_expr(ty));
        }
        if !self.types.insert((self.session, ty)) {
            return Ok(());
        }
        self.block(0, 3)?;
        match &desc {
            // `newty2 ty.level desc` shares the descriptor.
            TypeDesc::Tvar(name) | TypeDesc::Tunivar(name) => {
                self.block(0, 1)?;
                self.option_string(name.as_ref())
            }
            TypeDesc::Tconstr {
                path,
                args,
                path_block,
                ..
            } => {
                // Tconstr (type_path s p, args, ref Mnil)
                self.block(3, 3)?;
                self.tconstr_path(ty, path, *path_block)?;
                self.list(args.as_slice(), |size, ty| size.type_expr(*ty))?;
                self.block(0, 1)
            }
            TypeDesc::Tvariant(row) => {
                self.block(8, 1)?;
                self.block(0, 5)?;
                let fields = row.row_fields.to_vec();
                self.list(&fields, |size, (_, field)| {
                    size.block(0, 2)?;
                    size.string()?;
                    // `copy_row` copies present payloads and gives an
                    // undetermined field a fresh `ref None`.
                    match field {
                        RowField::Rpresent(None) => size.rpresent_none(),
                        RowField::Rpresent(ty) => {
                            size.block(0, 1)?;
                            size.option(ty.as_ref(), |size, ty| size.type_expr(*ty))
                        }
                        RowField::Reither { types, .. } => {
                            size.block(1, 4)?;
                            size.list(types, |size, ty| size.type_expr(*ty))?;
                            size.block(0, 1)
                        }
                        RowField::Rabsent => Ok(()),
                    }
                })?;
                self.type_expr(row.row_more)?;
                self.option(row.row_name.as_ref(), |size, (path, tys)| {
                    size.block(0, 2)?;
                    size.copied_type_path(path, None)?;
                    size.list(tys, |size, ty| size.type_expr(*ty))
                })
            }
            // `Btype.copy_type_desc`: the same shape as the original.
            _ => self.type_desc(ty, &desc),
        }
    }

    /// `Rpresent None` is a constant constructor application, which the
    /// OCaml compiler allocates statically: every use shares one block.
    fn rpresent_none(&mut self) -> Walk {
        if std::mem::replace(&mut self.rpresent_none, true) {
            return Ok(());
        }
        self.block(0, 1)
    }

    fn row_field(&mut self, field: &RowField) -> Walk {
        match field {
            RowField::Rpresent(None) => self.rpresent_none(),
            RowField::Rpresent(ty) => {
                self.block(0, 1)?;
                self.option(ty.as_ref(), |size, ty| size.type_expr(*ty))
            }
            RowField::Reither { types, link, .. } => {
                self.block(1, 4)?;
                self.list(types, |size, ty| size.type_expr(*ty))?;
                self.row_field_ref(*link)
            }
            RowField::Rabsent => Ok(()),
        }
    }

    // row_field option ref
    fn row_field_ref(&mut self, link: RowFieldRef) -> Walk {
        if !self.row_field_refs.insert(link) {
            return Ok(());
        }
        self.block(0, 1)?;
        let field = self.ctx.get_row_field(link);
        self.option(field.as_ref(), |size, field| size.row_field(field))
    }

    // abbrev_memo ref
    fn abbrev_ref(&mut self, memo: AbbrevMemoRef) -> Walk {
        // The nil handle stands for each node's own `ref Mnil`.
        if memo != AbbrevMemoRef::nil() && !self.abbrev_refs.insert(memo) {
            return Ok(());
        }
        self.block(0, 1)?;
        self.abbrev_memo(memo)
    }

    fn abbrev_memo(&mut self, memo: AbbrevMemoRef) -> Walk {
        match self.ctx.get_abbrev_memo(memo) {
            AbbrevMemo::Mnil => Ok(()),
            AbbrevMemo::Mcons {
                path,
                abbrev,
                expansion,
                next,
                ..
            } => {
                self.block(0, 5)?;
                self.path(&path)?;
                self.type_expr(abbrev)?;
                self.type_expr(expansion)?;
                self.abbrev_memo(next)
            }
            AbbrevMemo::Mlink(target) => {
                self.block(1, 1)?;
                self.abbrev_ref(target)
            }
        }
    }

    // field_mutability ref
    fn mutability_ref(&mut self, cell: MutabilityRef) -> Walk {
        if !self.mutability_refs.insert(cell) {
            return Ok(());
        }
        self.block(0, 1)?;
        match self.ctx.get_mutability(cell) {
            FieldMutability::Value(_) => self.block(0, 1),
            FieldMutability::Link(target) => {
                self.block(1, 1)?;
                self.mutability_ref(target)
            }
        }
    }
}
