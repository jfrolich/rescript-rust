//! A module's items, from its typed tree: a port of
//! analysis/src/process_cmt.ml.
//!
//! OCaml builds a `File.t` from a `.cmt`'s annotations; here the typed tree
//! comes straight from type-checking the module.

use super::process_attributes::{self as attrs, Attrs};
use super::shared_types::*;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::types::decl::{self, RecStatus, SignatureItem};
use crate::types::typedtree as tt;
use crate::types::{TypeContext, TypeDesc, TypeExprRef};
use std::sync::Arc;

/// What processing a typed tree reads: the module's parse arena (typed-tree
/// locations and attributes point into it) and type context.
#[derive(Clone, Copy)]
pub struct Ctx<'a> {
    /// The module's parse arena.
    pub arena: &'a ParseArena,
    /// The module's type context.
    pub types: &'a TypeContext,
    /// Where an attribute reader's error is kept (see [`attrs::Raised`]).
    pub raised: &'a attrs::Raised,
    /// Node storage of the typed tree.
    pub ta: &'a tt::TypedArena,
}

impl Ctx<'_> {
    fn loc(&self, idx: LocIdx) -> Loc {
        Loc::of_idx(self.arena, idx)
    }

    fn located(&self, l: &tt::Loc<String>) -> Located<String> {
        Located {
            txt: l.txt.clone(),
            loc: self.loc(l.loc),
        }
    }

    fn parsed<'b>(&'b self, a: &'b crate::parser::ast::Attributes) -> Attrs<'b> {
        Attrs::Parsed(a.as_slice(), self.arena)
    }
}

/// `Shared.dig`.
pub fn dig(types: &TypeContext, mut te: TypeExprRef) -> TypeExprRef {
    loop {
        match &*types.get_desc(te) {
            TypeDesc::Tlink(inner) | TypeDesc::Tsubst(inner) => te = *inner,
            TypeDesc::Tpoly { body, .. } => te = *body,
            _ => return te,
        }
    }
}

fn is_module_type(declared: &Declared<Module>) -> bool {
    matches!(
        declared.module_path,
        ModulePath::ExportedModule { is_type: true, .. }
    )
}

/// `add_declared`.
#[allow(clippy::too_many_arguments)]
fn add_declared<T: Clone>(
    name: Located<String>,
    extent: Loc,
    stamp: i32,
    env: &ProcessEnv,
    item: T,
    attributes: Attrs<'_>,
    exported: Option<(&mut Exported, ExportedKind)>,
    add_stamp: impl FnOnce(i32, Declared<T>),
    raised: &attrs::Raised,
) -> Declared<T> {
    let is_exported = match exported {
        Some((exported, kind)) => exported.add(kind, &name.txt, stamp),
        None => true,
    };
    let declared = attrs::new_declared(
        item,
        extent,
        name,
        stamp,
        env.module_path.clone(),
        is_exported,
        raised.declared_attributes(attributes),
    );
    add_stamp(stamp, declared.clone());
    declared
}

fn attrs_to_docstring(raised: &attrs::Raised, attributes: Attrs<'_>) -> Vec<String> {
    raised
        .read(attrs::find_doc_attribute(attributes))
        .into_iter()
        .collect()
}

fn module_item(
    kind: ModuleItemKind,
    name: &Located<String>,
    docstring: &[String],
    deprecated: &Option<String>,
    loc: Loc,
) -> ModuleItem {
    ModuleItem {
        kind,
        name: name.txt.clone(),
        docstring: docstring.to_vec(),
        deprecated: deprecated.clone(),
        loc,
    }
}

fn value_item(declared: &Declared<TypeExprRef>) -> ModuleItem {
    module_item(
        ModuleItemKind::Value(declared.item),
        &declared.name,
        &declared.docstring,
        &declared.deprecated,
        declared.extent_loc,
    )
}

fn module_item_of(declared: &Declared<Module>) -> ModuleItem {
    module_item(
        ModuleItemKind::Module {
            type_: declared.item.clone(),
            is_module_type: is_module_type(declared),
        },
        &declared.name,
        &declared.docstring,
        &declared.deprecated,
        declared.extent_loc,
    )
}

fn type_item(declared: &Declared<Type>, rec_status: RecStatus) -> ModuleItem {
    module_item(
        ModuleItemKind::Type(declared.item.clone(), rec_status),
        &declared.name,
        &declared.docstring,
        &declared.deprecated,
        declared.extent_loc,
    )
}

/// `map_record_field`.
fn map_record_field(raised: &attrs::Raised, ld: &decl::LabelDeclaration) -> Field {
    let attributes = Attrs::Decl(&ld.ld_attributes);
    Field {
        stamp: ld.ld_id.binding_time(),
        fname: Located::mknoloc(ld.ld_id.name().to_string()),
        typ: ld.ld_type,
        optional: ld.ld_optional,
        docstring: attrs_to_docstring(raised, attributes),
        deprecated: raised.read(attrs::find_deprecated_attribute(attributes)),
    }
}

/// The processing state shared by a file's items: its stamps.
pub struct Processor<'a> {
    /// What the items are read from.
    pub ctx: Ctx<'a>,
    /// The declarations found so far, by stamp.
    pub stamps: Stamps,
}

impl Processor<'_> {
    /// `for_type_signature_item`.
    fn for_type_signature_item(
        &mut self,
        env: &ProcessEnv,
        exported: &mut Exported,
        item: &SignatureItem,
    ) -> Vec<ModuleItem> {
        match item {
            SignatureItem::SigValue(ident, vd) => {
                let stamp = ident.binding_time();
                let old_declared = self.stamps.find_value(stamp).cloned();
                let loc = Loc::of_location(&self.ctx.types.resolve_loc(vd.val_loc));
                let stamps = &mut self.stamps;
                let declared = add_declared(
                    Located {
                        txt: ident.name().to_string(),
                        loc,
                    },
                    loc,
                    stamp,
                    env,
                    vd.val_type,
                    Attrs::Decl(&vd.val_attributes),
                    Some((exported, ExportedKind::Value)),
                    |stamp, d| stamps.add_value(stamp, d),
                    self.ctx.raised,
                );
                // When an id is shadowed, a module constraint without the doc
                // comment is created; restore the existing doc comment.
                let declared = match old_declared {
                    Some(old) if declared.docstring.is_empty() => {
                        let new_declared = Declared {
                            docstring: old.docstring,
                            ..declared
                        };
                        self.stamps.add_value(stamp, new_declared.clone());
                        new_declared
                    }
                    _ => declared,
                };
                vec![value_item(&declared)]
            }
            SignatureItem::SigType(ident, decl, rec_status) => {
                let name = Located::mknoloc(ident.name().to_string());
                let kind = match &decl.type_kind {
                    decl::TypeKind::TypeAbstract => match decl.type_manifest {
                        Some(manifest) => match &*self.ctx.types.get_desc(manifest) {
                            TypeDesc::Tconstr { path, args, .. } => TypeKind::Abstract(Some((
                                *path,
                                self.ctx.types.type_list(args).iter().collect(),
                            ))),
                            TypeDesc::Ttuple(items) => TypeKind::Tuple(
                                self.ctx.types.type_list(items).iter().collect(),
                            ),
                            _ => TypeKind::Abstract(None),
                        },
                        None => TypeKind::Abstract(None),
                    },
                    decl::TypeKind::TypeOpen => TypeKind::Open,
                    decl::TypeKind::TypeVariant(constructors, _) => TypeKind::Variant(
                        constructors
                            .iter()
                            .map(|cd| {
                                let cname = cd.cd_id.name().to_string();
                                let stamp = cd.cd_id.binding_time();
                                let cd_attributes = Attrs::Decl(&cd.cd_attributes);
                                let item = Constructor {
                                    stamp,
                                    cname: Located::mknoloc(cname.clone()),
                                    args: match &cd.cd_args {
                                        decl::ConstructorArguments::CstrTuple(args) => {
                                            ConstructorArgs::Args(
                                                args.iter().map(|t| (*t, Loc::none())).collect(),
                                            )
                                        }
                                        decl::ConstructorArguments::CstrRecord(fields) => {
                                            ConstructorArgs::InlineRecord(
                                                fields
                                                    .iter()
                                                    .map(|ld| map_record_field(self.ctx.raised, ld))
                                                    .collect(),
                                            )
                                        }
                                    },
                                    res: cd.cd_res,
                                    type_decl: (cname.clone(), decl.clone()),
                                    docstring: attrs_to_docstring(self.ctx.raised, cd_attributes),
                                    deprecated: self
                                        .ctx
                                        .raised
                                        .read(attrs::find_deprecated_attribute(cd_attributes)),
                                };
                                let declared = attrs::new_declared(
                                    item.clone(),
                                    Loc::of_location(&self.ctx.types.resolve_loc(cd.cd_loc)),
                                    Located::mknoloc(cname),
                                    stamp,
                                    env.module_path.clone(),
                                    true,
                                    self.ctx.raised.declared_attributes(cd_attributes),
                                );
                                self.stamps.add_constructor(stamp, declared);
                                item
                            })
                            .collect(),
                    ),
                    decl::TypeKind::TypeRecord(fields, _) => TypeKind::Record(
                        fields
                            .iter()
                            .map(|ld| map_record_field(self.ctx.raised, ld))
                            .collect(),
                    ),
                };
                let attributes = Attrs::Decl(&decl.type_attributes);
                let item = Type {
                    kind,
                    decl: decl.clone(),
                    name: name.txt.clone(),
                    editor_complete_from: attrs::find_editor_complete_from_attribute(attributes),
                };
                let stamps = &mut self.stamps;
                let declared = add_declared(
                    name,
                    Loc::of_location(&self.ctx.types.resolve_loc(decl.type_loc)),
                    ident.binding_time(),
                    env,
                    item,
                    attributes,
                    Some((exported, ExportedKind::Type)),
                    |stamp, d| stamps.add_type(stamp, d),
                    self.ctx.raised,
                );
                vec![type_item(&declared, *rec_status)]
            }
            SignatureItem::SigModule(ident, md, _) => {
                let name = ident.name().to_string();
                let item = self.for_type_module(&name, env, &md.md_type);
                let loc = Loc::of_location(&self.ctx.types.resolve_loc(md.md_loc));
                let stamps = &mut self.stamps;
                let declared = add_declared(
                    Located { txt: name, loc },
                    loc,
                    ident.binding_time(),
                    env,
                    item,
                    Attrs::Decl(&md.md_attributes),
                    Some((exported, ExportedKind::Module)),
                    |stamp, d| stamps.add_module(stamp, d),
                    self.ctx.raised,
                );
                vec![module_item_of(&declared)]
            }
            _ => Vec::new(),
        }
    }

    /// `for_type_signature`.
    fn for_type_signature(
        &mut self,
        name: &str,
        env: &ProcessEnv,
        signature: &[SignatureItem],
    ) -> Structure {
        let mut exported = Exported::default();
        let items = fold_right_items(signature, |item| {
            self.for_type_signature_item(env, &mut exported, item)
        });
        Structure {
            name: name.to_string(),
            docstring: Vec::new(),
            exported: Arc::new(exported),
            items,
            deprecated: None,
        }
    }

    /// `for_type_module`.
    fn for_type_module(
        &mut self,
        name: &str,
        env: &ProcessEnv,
        module_type: &decl::ModuleType,
    ) -> Module {
        match module_type {
            decl::ModuleType::MtyIdent(_) | decl::ModuleType::MtyAlias(..) => {
                let path = module_type.ident_or_alias_path().unwrap();
                Module::Ident(*path)
            }
            decl::ModuleType::MtySignature(signature) => {
                Module::Structure(Arc::new(self.for_type_signature(name, env, signature)))
            }
            decl::ModuleType::MtyFunctor { result, .. } => self.for_type_module(name, env, result),
        }
    }

    /// `for_type_declaration`.
    fn for_type_declaration(
        &mut self,
        env: &ProcessEnv,
        exported: &mut Exported,
        td: &tt::TypedTypeDeclaration,
        rec_status: RecStatus,
    ) -> ModuleItem {
        let stamp = td.typ_id.binding_time();
        let typ_type = Arc::new(td.typ_type.clone());
        let kind = match &td.typ_kind {
            tt::TypedTypeKind::Ttype_abstract => match &td.typ_manifest {
                Some(manifest) => match &self.ctx.ta.core_type(*manifest).ctyp_desc {
                    tt::TypedCoreTypeDesc::Ttyp_constr(path, _, args) => {
                        TypeKind::Abstract(Some((
                            *path,
                            self.ctx.ta.core_types(*args).map(|t| t.ctyp_type).collect(),
                        )))
                    }
                    tt::TypedCoreTypeDesc::Ttyp_tuple(items) => TypeKind::Tuple(
                        self.ctx
                            .ta
                            .core_types(*items)
                            .map(|t| t.ctyp_type)
                            .collect(),
                    ),
                    _ => TypeKind::Abstract(None),
                },
                None => TypeKind::Abstract(None),
            },
            tt::TypedTypeKind::Ttype_open => TypeKind::Open,
            tt::TypedTypeKind::Ttype_variant(constructors) => TypeKind::Variant(
                constructors
                    .iter()
                    .map(|cd| {
                        let stamp = cd.cd_id.binding_time();
                        let cd_attributes = self.ctx.parsed(&cd.cd_attributes);
                        let cname = self.ctx.located(&cd.cd_name);
                        let item = Constructor {
                            stamp,
                            cname: cname.clone(),
                            deprecated: self
                                .ctx
                                .raised
                                .read(attrs::find_deprecated_attribute(cd_attributes)),
                            args: match &cd.cd_args {
                                tt::TypedConstructorArguments::Cstr_tuple(args) => {
                                    ConstructorArgs::Args(
                                        self.ctx
                                            .ta
                                            .core_types(*args)
                                            .map(|t| (t.ctyp_type, self.ctx.loc(t.ctyp_loc)))
                                            .collect(),
                                    )
                                }
                                tt::TypedConstructorArguments::Cstr_record(fields) => {
                                    ConstructorArgs::InlineRecord(
                                        fields
                                            .iter()
                                            .map(|f| {
                                                let f_attributes =
                                                    self.ctx.parsed(&f.ld_attributes);
                                                Field {
                                                    stamp: f.ld_id.binding_time(),
                                                    fname: Located::mknoloc(
                                                        f.ld_id.name().to_string(),
                                                    ),
                                                    typ: self.ctx.ta.core_type(f.ld_type).ctyp_type,
                                                    optional: f.ld_optional,
                                                    docstring: attrs_to_docstring(
                                                        self.ctx.raised,
                                                        f_attributes,
                                                    ),
                                                    deprecated: self.ctx.raised.read(
                                                        attrs::find_deprecated_attribute(
                                                            f_attributes,
                                                        ),
                                                    ),
                                                }
                                            })
                                            .collect(),
                                    )
                                }
                            },
                            res: cd
                                .cd_res
                                .as_ref()
                                .map(|t| self.ctx.ta.core_type(*t).ctyp_type),
                            type_decl: (td.typ_name.txt.clone(), typ_type.clone()),
                            docstring: attrs_to_docstring(self.ctx.raised, cd_attributes),
                        };
                        let declared = attrs::new_declared(
                            item.clone(),
                            self.ctx.loc(cd.cd_loc),
                            cname,
                            stamp,
                            env.module_path.clone(),
                            true,
                            self.ctx.raised.declared_attributes(cd_attributes),
                        );
                        self.stamps.add_constructor(stamp, declared);
                        item
                    })
                    .collect(),
            ),
            tt::TypedTypeKind::Ttype_record(fields) => TypeKind::Record(
                fields
                    .iter()
                    .map(|f| {
                        let f_attributes = self.ctx.parsed(&f.ld_attributes);
                        Field {
                            stamp: f.ld_id.binding_time(),
                            fname: self.ctx.located(&f.ld_name),
                            typ: self.ctx.ta.core_type(f.ld_type).ctyp_type,
                            optional: f.ld_optional,
                            docstring: attrs_to_docstring(self.ctx.raised, f_attributes),
                            deprecated: self
                                .ctx
                                .raised
                                .read(attrs::find_deprecated_attribute(f_attributes)),
                        }
                    })
                    .collect(),
            ),
        };
        let attributes = self.ctx.parsed(&td.typ_attributes);
        let name = self.ctx.located(&td.typ_name);
        let item = Type {
            kind,
            decl: typ_type,
            name: name.txt.clone(),
            editor_complete_from: attrs::find_editor_complete_from_attribute(attributes),
        };
        let stamps = &mut self.stamps;
        let declared = add_declared(
            name,
            Loc::of_idx(self.ctx.arena, td.typ_loc),
            stamp,
            env,
            item,
            attributes,
            Some((exported, ExportedKind::Type)),
            |stamp, d| stamps.add_type(stamp, d),
            self.ctx.raised,
        );
        type_item(&declared, rec_status)
    }

    fn type_declarations(
        &mut self,
        env: &ProcessEnv,
        exported: &mut Exported,
        rec_flag: &crate::parser::ast::RecFlag,
        decls: &[tt::TypedTypeDeclaration],
    ) -> Vec<ModuleItem> {
        decls
            .iter()
            .enumerate()
            .map(|(i, decl)| {
                let rec_status = match (rec_flag, i) {
                    (crate::parser::ast::RecFlag::Recursive, 0) => RecStatus::TrecFirst,
                    (crate::parser::ast::RecFlag::Nonrecursive, 0) => RecStatus::TrecNot,
                    _ => RecStatus::TrecNext,
                };
                self.for_type_declaration(env, exported, decl, rec_status)
            })
            .collect()
    }

    /// The `Tsig_module` case of `for_signature_item`.
    fn for_module_declaration(
        &mut self,
        env: &ProcessEnv,
        exported: &mut Exported,
        md: &tt::TypedModuleDeclaration,
    ) -> ModuleItem {
        let name = self.ctx.located(&md.md_name);
        let item = self.for_type_module(
            &name.txt,
            &env.add_module(&name.txt),
            &self.ctx.ta.module_type(md.md_type).mty_type,
        );
        let stamps = &mut self.stamps;
        let declared = add_declared(
            name,
            Loc::of_idx(self.ctx.arena, md.md_loc),
            md.md_id.binding_time(),
            env,
            item,
            Attrs::Parsed(md.md_attributes.as_slice(), self.ctx.arena),
            Some((exported, ExportedKind::Module)),
            |stamp, d| stamps.add_module(stamp, d),
            self.ctx.raised,
        );
        module_item_of(&declared)
    }

    /// `for_signature_item`.
    fn for_signature_item(
        &mut self,
        env: &ProcessEnv,
        exported: &mut Exported,
        item: &tt::TypedSignatureItemDesc,
    ) -> Vec<ModuleItem> {
        match item {
            tt::TypedSignatureItemDesc::Tsig_value(vd) => {
                let stamps = &mut self.stamps;
                let declared = add_declared(
                    Located {
                        txt: self.ctx.ta.value_description(*vd).val_name.txt.clone(),
                        loc: Loc::of_idx(
                            self.ctx.arena,
                            self.ctx.ta.value_description(*vd).val_name.loc,
                        ),
                    },
                    Loc::of_idx(self.ctx.arena, self.ctx.ta.value_description(*vd).val_loc),
                    self.ctx.ta.value_description(*vd).val_id.binding_time(),
                    env,
                    self.ctx
                        .ta
                        .core_type(self.ctx.ta.value_description(*vd).val_desc)
                        .ctyp_type,
                    Attrs::Parsed(
                        self.ctx.ta.value_description(*vd).val_attributes.as_slice(),
                        self.ctx.arena,
                    ),
                    Some((exported, ExportedKind::Value)),
                    |stamp, d| stamps.add_value(stamp, d),
                    self.ctx.raised,
                );
                vec![value_item(&declared)]
            }
            tt::TypedSignatureItemDesc::Tsig_type(rec_flag, decls) => {
                self.type_declarations(env, exported, rec_flag, decls)
            }
            tt::TypedSignatureItemDesc::Tsig_module(md) => {
                vec![self.for_module_declaration(env, exported, md)]
            }
            tt::TypedSignatureItemDesc::Tsig_recmodule(mds) => mds
                .iter()
                .map(|md| self.for_module_declaration(env, exported, md))
                .collect(),
            tt::TypedSignatureItemDesc::Tsig_include(incl) => {
                let env = match &self.ctx.ta.module_type(incl.incl_mod).mty_desc {
                    tt::ModuleTypeDesc::Tmty_ident(path, _)
                    | tt::ModuleTypeDesc::Tmty_alias(path, _) => ProcessEnv {
                        module_path: ModulePath::IncludedModule(
                            *path,
                            Box::new(env.module_path.clone()),
                        ),
                    },
                    _ => env.clone(),
                };
                fold_right_items(incl.incl_type.iter(), |item| {
                    self.for_type_signature_item(&env, exported, item)
                })
            }
            _ => Vec::new(),
        }
    }

    /// `for_signature`.
    pub fn for_signature(
        &mut self,
        name: &str,
        env: &ProcessEnv,
        sig_items: &[tt::TypedSignatureItem],
    ) -> Structure {
        let mut exported = Exported::default();
        let items = sig_items
            .iter()
            .flat_map(|item| self.for_signature_item(env, &mut exported, &item.sig_desc))
            .collect();
        let attributes: Vec<crate::parser::ast::Attribute> = match sig_items.first() {
            Some(tt::TypedSignatureItem {
                sig_desc: tt::TypedSignatureItemDesc::Tsig_attribute(attribute),
                ..
            }) => vec![attribute.clone()],
            _ => Vec::new(),
        };
        let attributes = Attrs::Parsed(&attributes, self.ctx.arena);
        Structure {
            name: name.to_string(),
            docstring: attrs_to_docstring(self.ctx.raised, attributes),
            exported: Arc::new(exported),
            items,
            deprecated: self
                .ctx
                .raised
                .read(attrs::find_deprecated_attribute(attributes)),
        }
    }

    /// `handle_pattern` of a `Tstr_value`.
    fn handle_pattern(
        &mut self,
        env: &ProcessEnv,
        exported: &mut Exported,
        items: &mut Vec<ModuleItem>,
        attributes: Option<&crate::parser::ast::Attributes>,
        pat: &tt::Pattern,
    ) {
        let empty = crate::parser::ast::Attributes::new();
        let attributes = attributes.unwrap_or(&empty);
        match &pat.pat_desc {
            tt::PatternDesc::Tpat_var(ident, name)
            | tt::PatternDesc::Tpat_alias(_, ident, name) => {
                let name = self.ctx.located(name);
                let stamp = ident.binding_time();
                // Detect first-class module unpack patterns and register them
                // as modules.
                let unpack_loc = self
                    .ctx
                    .ta
                    .pat_extra(pat)
                    .iter()
                    .find_map(|(extra, loc, _)| {
                        matches!(extra, tt::PatExtra::Tpat_unpack).then_some(*loc)
                    });
                let unpacked_path = unpack_loc.and_then(|_| {
                    match &*self.ctx.types.get_desc(dig(self.ctx.types, pat.pat_type)) {
                        TypeDesc::Tpackage { path, .. } => Some(*path),
                        _ => None,
                    }
                });
                if let (Some(unpack_loc), Some(path)) = (unpack_loc, unpacked_path) {
                    let declared = attrs::new_declared(
                        Module::Ident(path),
                        self.ctx.loc(unpack_loc),
                        name,
                        stamp,
                        ModulePath::NotVisible,
                        false,
                        self.ctx
                            .raised
                            .declared_attributes(self.ctx.parsed(attributes)),
                    );
                    self.stamps.add_module(stamp, declared.clone());
                    items.insert(0, module_item_of(&declared));
                } else {
                    let stamps = &mut self.stamps;
                    let declared = add_declared(
                        name,
                        Loc::of_idx(self.ctx.arena, pat.pat_loc),
                        stamp,
                        env,
                        pat.pat_type,
                        Attrs::Parsed(attributes.as_slice(), self.ctx.arena),
                        Some((exported, ExportedKind::Value)),
                        |stamp, d| stamps.add_value(stamp, d),
                        self.ctx.raised,
                    );
                    items.insert(0, value_item(&declared));
                }
            }
            tt::PatternDesc::Tpat_tuple(pats)
            | tt::PatternDesc::Tpat_array(pats)
            | tt::PatternDesc::Tpat_construct(_, _, pats) => {
                for p in self.ctx.ta.patterns(*pats) {
                    self.handle_pattern(env, exported, items, None, p);
                }
            }
            tt::PatternDesc::Tpat_or(p, _, _) => {
                self.handle_pattern(env, exported, items, None, self.ctx.ta.pattern(*p))
            }
            tt::PatternDesc::Tpat_dict(entries) => {
                for entry in entries {
                    let p = self.ctx.ta.pattern(entry.tdp_pattern);
                    self.handle_pattern(env, exported, items, None, p);
                }
            }
            tt::PatternDesc::Tpat_record(record_items, _, rest) => {
                for (_, _, p, _) in record_items {
                    self.handle_pattern(env, exported, items, None, self.ctx.ta.pattern(*p));
                }
                if let Some(rest) = rest {
                    let name = self.ctx.located(&rest.rest_name);
                    let extent = name.loc;
                    let stamps = &mut self.stamps;
                    let declared = add_declared(
                        name,
                        extent,
                        rest.rest_ident.binding_time(),
                        env,
                        rest.rest_type,
                        Attrs::Parsed(&[], self.ctx.arena),
                        Some((exported, ExportedKind::Value)),
                        |stamp, d| stamps.add_value(stamp, d),
                        self.ctx.raised,
                    );
                    items.insert(0, value_item(&declared));
                }
            }
            tt::PatternDesc::Tpat_variant(_, Some(p), _) => {
                self.handle_pattern(env, exported, items, None, self.ctx.ta.pattern(*p))
            }
            tt::PatternDesc::Tpat_variant(_, None, _)
            | tt::PatternDesc::Tpat_any
            | tt::PatternDesc::Tpat_constant(_)
            | tt::PatternDesc::Tpat_interval(..) => {}
        }
    }

    /// `for_structure_item`.
    fn for_structure_item(
        &mut self,
        env: &ProcessEnv,
        exported: &mut Exported,
        item: &tt::StructureItemDesc,
    ) -> Vec<ModuleItem> {
        match item {
            tt::StructureItemDesc::Tstr_value(_, bindings) => {
                let mut items = Vec::new();
                for binding in self.ctx.ta.value_bindings(*bindings) {
                    self.handle_pattern(
                        env,
                        exported,
                        &mut items,
                        Some(&binding.vb_attributes),
                        self.ctx.ta.pattern(binding.vb_pat),
                    );
                }
                for binding in self.ctx.ta.value_bindings(*bindings) {
                    self.scan_let_modules(env, binding.vb_expr);
                }
                items
            }
            // The bindings of a derived item, as the variables they bind.
            tt::StructureItemDesc::Tstr_derived(idx) => {
                let arena = self.ctx.arena;
                let plans = arena.plans();
                let item = plans.item(*idx);
                let mut items = Vec::new();
                for (binding, bound) in
                    plans.bindings(item).iter().zip(self.ctx.ta.derived.bound(*idx))
                {
                    let pattern = tt::Pattern::new(
                        tt::PatternDesc::Tpat_var(
                            bound.ident,
                            tt::Loc {
                                txt: bound.ident.name().to_string(),
                                loc: arena.none_loc(),
                            },
                        ),
                        arena.none_loc(),
                        bound.ty,
                        bound.env,
                    );
                    self.handle_pattern(
                        env,
                        exported,
                        &mut items,
                        Some(&binding.attributes),
                        &pattern,
                    );
                }
                items
            }
            // %%private generates a dummy module called local_...
            tt::StructureItemDesc::Tstr_module(mb) if !is_private_module(mb) => {
                vec![self.for_module_binding(env, exported, mb)]
            }
            tt::StructureItemDesc::Tstr_recmodule(mbs) => mbs
                .iter()
                .filter(|mb| !is_private_module(mb))
                .map(|mb| self.for_module_binding(env, exported, mb))
                .collect(),
            tt::StructureItemDesc::Tstr_modtype(mtd) => {
                let Some(mtd_type) = &mtd.mtd_type else {
                    return Vec::new();
                };
                let name = self.ctx.located(&mtd.mtd_name);
                let env = env.add_module_type(&name.txt);
                let item = self.for_type_module(
                    &name.txt,
                    &env,
                    &self.ctx.ta.module_type(*mtd_type).mty_type,
                );
                let stamps = &mut self.stamps;
                let declared = add_declared(
                    name,
                    Loc::of_idx(self.ctx.arena, mtd.mtd_loc),
                    mtd.mtd_id.binding_time(),
                    &env,
                    item,
                    Attrs::Parsed(mtd.mtd_attributes.as_slice(), self.ctx.arena),
                    Some((exported, ExportedKind::Module)),
                    |stamp, d| stamps.add_module(stamp, d),
                    self.ctx.raised,
                );
                vec![module_item_of(&declared)]
            }
            tt::StructureItemDesc::Tstr_include(incl) => {
                let env = match get_module_path(
                    self.ctx.ta,
                    &self.ctx.ta.module_expr(incl.incl_mod).mod_desc,
                ) {
                    Some(path) => ProcessEnv {
                        module_path: ModulePath::IncludedModule(
                            path,
                            Box::new(env.module_path.clone()),
                        ),
                    },
                    None => env.clone(),
                };
                fold_right_items(incl.incl_type.iter(), |item| {
                    self.for_type_signature_item(&env, exported, item)
                })
            }
            tt::StructureItemDesc::Tstr_primitive(vd) => {
                let stamps = &mut self.stamps;
                let declared = add_declared(
                    self.ctx
                        .located(&self.ctx.ta.value_description(*vd).val_name),
                    Loc::of_idx(self.ctx.arena, self.ctx.ta.value_description(*vd).val_loc),
                    self.ctx.ta.value_description(*vd).val_id.binding_time(),
                    env,
                    self.ctx
                        .ta
                        .core_type(self.ctx.ta.value_description(*vd).val_desc)
                        .ctyp_type,
                    Attrs::Parsed(
                        self.ctx.ta.value_description(*vd).val_attributes.as_slice(),
                        self.ctx.arena,
                    ),
                    Some((exported, ExportedKind::Value)),
                    |stamp, d| stamps.add_value(stamp, d),
                    self.ctx.raised,
                );
                vec![value_item(&declared)]
            }
            tt::StructureItemDesc::Tstr_type(rec_flag, decls) => {
                self.type_declarations(env, exported, rec_flag, decls)
            }
            _ => Vec::new(),
        }
    }

    /// The `Tstr_module` case of `for_structure_item`.
    fn for_module_binding(
        &mut self,
        env: &ProcessEnv,
        exported: &mut Exported,
        mb: &tt::ModuleBinding,
    ) -> ModuleItem {
        let name = self.ctx.located(&mb.mb_name);
        let item = self.for_module(
            env,
            &self.ctx.ta.module_expr(mb.mb_expr).mod_desc,
            &name.txt,
        );
        let stamps = &mut self.stamps;
        let declared = add_declared(
            name,
            Loc::of_idx(self.ctx.arena, mb.mb_loc),
            mb.mb_id.binding_time(),
            env,
            item,
            Attrs::Parsed(mb.mb_attributes.as_slice(), self.ctx.arena),
            Some((exported, ExportedKind::Module)),
            |stamp, d| stamps.add_module(stamp, d),
            self.ctx.raised,
        );
        module_item_of(&declared)
    }

    /// `for_module`.
    fn for_module(
        &mut self,
        env: &ProcessEnv,
        mod_desc: &tt::ModuleExprDesc,
        module_name: &str,
    ) -> Module {
        match mod_desc {
            tt::ModuleExprDesc::Tmod_ident(path, _) => Module::Ident(*path),
            tt::ModuleExprDesc::Tmod_structure(structure) => {
                let env = env.add_module(module_name);
                Module::Structure(Arc::new(self.for_structure(
                    module_name,
                    &env,
                    self.ctx.ta.structure_items(structure.str_items),
                )))
            }
            tt::ModuleExprDesc::Tmod_functor(ident, arg_name, maybe_type, result) => {
                if let Some(t) = maybe_type {
                    let name = self.ctx.located(arg_name);
                    let kind =
                        self.for_type_module(&name.txt, env, &self.ctx.ta.module_type(*t).mty_type);
                    let stamp = ident.binding_time();
                    let extent = name.loc;
                    let declared = attrs::new_declared(
                        kind,
                        extent,
                        name,
                        stamp,
                        ModulePath::NotVisible,
                        false,
                        self.ctx.raised.declared_attributes(Attrs::Decl(&[])),
                    );
                    self.stamps.add_module(stamp, declared);
                }
                self.for_module(env, &self.ctx.ta.module_expr(*result).mod_desc, module_name)
            }
            tt::ModuleExprDesc::Tmod_apply(functor, _, _) => self.for_module(
                env,
                &self.ctx.ta.module_expr(*functor).mod_desc,
                module_name,
            ),
            tt::ModuleExprDesc::Tmod_unpack(_, module_type) => {
                let env = env.add_module(module_name);
                self.for_type_module(module_name, &env, module_type)
            }
            tt::ModuleExprDesc::Tmod_constraint(expr, typ, _, _) => {
                let mod_kind =
                    self.for_module(env, &self.ctx.ta.module_expr(*expr).mod_desc, module_name);
                let env = env.add_module(module_name);
                let mod_type_kind = self.for_type_module(module_name, &env, typ);
                Module::Constraint(Box::new(mod_kind), Box::new(mod_type_kind))
            }
        }
    }

    /// `scan_let_modules`: register `let module M = ...` bindings inside
    /// expressions as local modules.
    fn scan_let_modules(&mut self, env: &ProcessEnv, e: tt::TExprIdx) {
        let ta = self.ctx.ta;
        match &ta.expr(e).exp_desc {
            tt::ExpressionDesc::Texp_letmodule(id, name, mexpr, body) => {
                let stamp = id.binding_time();
                let item =
                    self.for_module(env, &self.ctx.ta.module_expr(*mexpr).mod_desc, &name.txt);
                let name = self.ctx.located(name);
                let extent = name.loc;
                let declared = attrs::new_declared(
                    item,
                    extent,
                    name,
                    stamp,
                    ModulePath::NotVisible,
                    false,
                    self.ctx.raised.declared_attributes(Attrs::Decl(&[])),
                );
                self.stamps.add_module(stamp, declared);
                self.scan_let_modules(env, *body);
            }
            tt::ExpressionDesc::Texp_let(_, bindings, body) => {
                for binding in self.ctx.ta.value_bindings(*bindings) {
                    self.scan_let_modules(env, binding.vb_expr);
                }
                self.scan_let_modules(env, *body);
            }
            tt::ExpressionDesc::Texp_apply { funct, args, .. } => {
                self.scan_let_modules(env, *funct);
                for arg in self.ctx.ta.apply_args(*args) {
                    if let Some(e) = arg.expression {
                        self.scan_let_modules(env, e);
                    }
                }
            }
            tt::ExpressionDesc::Texp_tuple(exprs) => {
                for e in ta.expr_list(*exprs) {
                    self.scan_let_modules(env, *e);
                }
            }
            tt::ExpressionDesc::Texp_sequence(e1, e2) => {
                self.scan_let_modules(env, *e1);
                self.scan_let_modules(env, *e2);
            }
            tt::ExpressionDesc::Texp_match(e, cases, exn_cases, _) => {
                self.scan_let_modules(env, *e);
                for case in ta.cases(*cases).iter().chain(ta.cases(*exn_cases)) {
                    if let Some(g) = case.c_guard {
                        self.scan_let_modules(env, g);
                    }
                    self.scan_let_modules(env, case.c_rhs);
                }
            }
            tt::ExpressionDesc::Texp_function { body, .. } => self.scan_let_modules(env, *body),
            tt::ExpressionDesc::Texp_try(e, cases, finally) => {
                self.scan_let_modules(env, *e);
                for case in self.ctx.ta.cases(*cases) {
                    if let Some(g) = case.c_guard {
                        self.scan_let_modules(env, g);
                    }
                    self.scan_let_modules(env, case.c_rhs);
                }
                if let Some(finally) = finally {
                    self.scan_let_modules(env, *finally);
                }
            }
            tt::ExpressionDesc::Texp_ifthenelse(e1, e2, e3) => {
                self.scan_let_modules(env, *e1);
                self.scan_let_modules(env, *e2);
                if let Some(e3) = e3 {
                    self.scan_let_modules(env, *e3);
                }
            }
            _ => {}
        }
    }

    /// `for_structure`.
    pub fn for_structure(
        &mut self,
        name: &str,
        env: &ProcessEnv,
        str_items: &[tt::StructureItem],
    ) -> Structure {
        let mut exported = Exported::default();
        let items = fold_right_items(str_items, |item| {
            self.for_structure_item(env, &mut exported, &item.str_desc)
        });
        let attributes: Vec<crate::parser::ast::Attribute> = str_items
            .iter()
            .filter_map(|item| match &item.str_desc {
                tt::StructureItemDesc::Tstr_attribute(attr) => Some(attr.clone()),
                _ => None,
            })
            .collect();
        let attributes = Attrs::Parsed(&attributes, self.ctx.arena);
        Structure {
            name: name.to_string(),
            docstring: attrs_to_docstring(self.ctx.raised, attributes),
            exported: Arc::new(exported),
            items,
            deprecated: self
                .ctx
                .raised
                .read(attrs::find_deprecated_attribute(attributes)),
        }
    }
}

/// `get_module_path`.
fn get_module_path(
    ta: &tt::TypedArena,
    mod_desc: &tt::ModuleExprDesc,
) -> Option<crate::types::Path> {
    match mod_desc {
        tt::ModuleExprDesc::Tmod_ident(path, _) => Some(*path),
        tt::ModuleExprDesc::Tmod_apply(functor, _, _) => {
            get_module_path(ta, &ta.module_expr(*functor).mod_desc)
        }
        tt::ModuleExprDesc::Tmod_constraint(expr, _, _, _) => {
            get_module_path(ta, &ta.module_expr(*expr).mod_desc)
        }
        tt::ModuleExprDesc::Tmod_structure(_)
        | tt::ModuleExprDesc::Tmod_functor(..)
        | tt::ModuleExprDesc::Tmod_unpack(..) => None,
    }
}

/// What a module's typed annotations are (`Cmt_format.binary_annots`).
#[derive(Clone, Copy)]
pub enum Annots<'a> {
    /// A `.res` file's structure.
    Implementation(&'a [tt::StructureItem]),
    /// A `.resi` file's signature.
    Interface(&'a [tt::TypedSignatureItem]),
}

/// `file_for_cmt_infos`.
pub fn file_for_annots(
    ctx: Ctx<'_>,
    module: ModuleId,
    module_name: &str,
    uri: String,
    annots: Annots<'_>,
) -> File {
    let env = ProcessEnv {
        module_path: ModulePath::File {
            uri: uri.clone(),
            module_name: module_name.to_string(),
        },
    };
    let mut processor = Processor {
        ctx,
        stamps: Stamps::default(),
    };
    let structure = match annots {
        Annots::Implementation(items) => processor.for_structure(module_name, &env, items),
        Annots::Interface(items) => processor.for_signature(module_name, &env, items),
    };
    File {
        uri,
        stamps: processor.stamps,
        module_name: module_name.to_string(),
        structure: Arc::new(structure),
        module,
    }
}

/// `%%private` generates a dummy module called `local_...`.
fn is_private_module(mb: &tt::ModuleBinding) -> bool {
    mb.mb_name.txt.starts_with("local_")
}

/// `List.fold_right` concatenating each item's module items: `f` runs on the
/// last item first, and the results keep source order.
fn fold_right_items<'i, I: 'i>(
    items: impl IntoIterator<Item = &'i I, IntoIter: DoubleEndedIterator>,
    mut f: impl FnMut(&'i I) -> Vec<ModuleItem>,
) -> Vec<ModuleItem> {
    let mut chunks: Vec<Vec<ModuleItem>> = items.into_iter().rev().map(&mut f).collect();
    chunks.reverse();
    chunks.into_iter().flatten().collect()
}
