//! Type printing: a port of the type-expression part of OCaml `Printtyp`
//! (compiler/ml/printtyp.ml) and of `Res_outcome_printer.print_out_type`
//! (compiler/syntax/src/res_outcome_printer.ml).
//!
//! `Printtyp` turns a type into an `Outcometree.out_type`, naming type
//! variables through a table that lives until the next `reset`; the outcome
//! printer lays the tree out with `Res_doc` at width 80.

// Variant names follow OCaml's Outcometree constructors.
#![allow(non_camel_case_types)]

use crate::parser::doc::Doc;
use crate::parser::longident::Longident;
use crate::types::asttypes::ArgLabel;
use crate::types::btype;
use crate::types::context::TypeContext;
use crate::types::path::Path;
use crate::types::type_expr::{GENERIC_LEVEL, RowDesc, RowField, TypeDesc, TypeExprRef};

// ============================================================================
// Outcometree (compiler/ml/outcometree.ml)
// ============================================================================

/// `Outcometree.out_ident`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum OutIdent {
    Oide_apply(Box<OutIdent>, Box<OutIdent>),
    Oide_dot(Box<OutIdent>, String),
    Oide_ident(String),
}

/// `Asttypes.Noloc.arg_label`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum OutArgLabel {
    Nolabel,
    Labelled(String),
    Optional(String),
}

/// `Outcometree.out_variant`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum OutVariant {
    Ovar_fields(Vec<(String, bool, Vec<OutType>)>),
    Ovar_typ(Box<OutType>),
}

/// A row of `Otyp_record`: name, runtime name given with `@as`, mutable,
/// optional, type.
pub(crate) type OutRecordField = (String, Option<String>, bool, bool, OutType);

/// `Outcometree.out_type`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum OutType {
    Otyp_abstract,
    Otyp_open,
    Otyp_alias(Box<OutType>, String),
    Otyp_arrow(Vec<(OutArgLabel, OutType)>, Box<OutType>),
    Otyp_constr(OutIdent, Vec<OutType>),
    Otyp_manifest(Box<OutType>, Box<OutType>),
    /// Fields are (name, mutable, type).
    Otyp_object(Vec<(String, bool, OutType)>, Option<bool>),
    /// Rows of name, runtime name given with `@as`, mutable, optional and
    /// type (outcometree.ml:40-41).
    Otyp_record(Vec<OutRecordField>),
    Otyp_stuff(String),
    Otyp_tuple(Vec<OutType>),
    Otyp_var(bool, String),
    Otyp_variant(bool, OutVariant, bool, Option<Vec<String>>),
    Otyp_poly(Vec<String>, Box<OutType>),
    Otyp_module(String, Vec<String>, Vec<OutType>),
    /// `(name, args, gadt result, @as representation)` constructors.
    Otyp_sum(Vec<OutConstructor>),
}

/// One `Otyp_sum` constructor.
pub(crate) type OutConstructor = (String, Vec<OutType>, Option<OutType>, Option<String>);

/// `Outcometree.out_rec_status`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum OutRecStatus {
    Orec_not,
    Orec_first,
    Orec_next,
}

/// `Outcometree.out_ext_status`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum OutExtStatus {
    Oext_first,
    Oext_next,
    Oext_exception,
}

/// `Outcometree.out_type_decl`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct OutTypeDecl {
    pub name: String,
    pub params: Vec<(String, (bool, bool))>,
    pub typ: OutType,
    pub private: bool,
    pub immediate: bool,
    pub unboxed: bool,
    pub cstrs: Vec<(OutType, OutType)>,
}

/// `Outcometree.out_extension_constructor`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct OutExtensionConstructor {
    pub name: String,
    pub type_name: String,
    pub type_params: Vec<String>,
    pub args: Vec<OutType>,
    pub ret_type: Option<OutType>,
    pub repr: Option<String>,
    pub private: bool,
}

/// `Outcometree.out_val_decl` (`oval_attributes` is always empty here).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct OutValDecl {
    pub name: String,
    pub typ: OutType,
    /// `oval_prim`: the primitive, rebuilt from the primitive description by
    /// `Primitive.print`.
    pub prim: Option<OutPrim>,
}

/// `Parsetree.primitive_repr` as `Primitive.print` rebuilds it for the
/// outcome tree.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum OutPrim {
    Name(String),
    Ffi {
        name: String,
        spec: crate::types::external_ffi_types::ExternalFfi,
    },
    InlineConst(crate::types::external_ffi_types::InlineConst),
}

/// `Outcometree.out_module_type`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum OutModuleType {
    Omty_abstract,
    Omty_functor(String, Option<Box<OutModuleType>>, Box<OutModuleType>),
    Omty_ident(OutIdent),
    Omty_signature(Vec<OutSigItem>),
    Omty_alias(OutIdent),
}

/// `Outcometree.out_sig_item` (class items print as nothing).
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum OutSigItem {
    Osig_typext(OutExtensionConstructor, OutExtStatus),
    Osig_modtype(String, OutModuleType),
    Osig_module(String, OutModuleType, OutRecStatus),
    Osig_type(OutTypeDecl, OutRecStatus),
    Osig_value(OutValDecl),
    Osig_ellipsis,
    Osig_class,
}

// ============================================================================
// Printtyp
// ============================================================================

/// The mutable naming state of OCaml `Printtyp`: `names`, `name_counter`,
/// `named_vars`, the weak-variable tables, and the loop marks
/// (`visited_objects`, `aliased`, `delayed`).
pub(crate) struct Printtyp<'a> {
    ctx: &'a TypeContext,
    names: Vec<(TypeExprRef, String)>,
    name_counter: usize,
    named_vars: Vec<String>,
    weak_counter: usize,
    weak_var_map: Vec<(TypeExprRef, String)>,
    named_weak_vars: Vec<String>,
    visited_objects: Vec<TypeExprRef>,
    aliased: Vec<TypeExprRef>,
    delayed: Vec<TypeExprRef>,
    /// `unique_names`: identifiers printed as `Ident.unique_toplevel_name`.
    unique_names: Vec<(crate::ident::Ident, String)>,
    /// `!printing_env`, set by `wrap_printing_env`; `None` stands for
    /// `Env.empty`.
    printing_env: Option<crate::types::env::Env>,
    /// Types added to the printing environment by `tree_of_signature_rec`
    /// (`Env.add_signature`), most recent last. Only the first
    /// `signature_types_visible` entries are in scope; later entries are
    /// members of the recursive type group being printed.
    signature_types: Vec<(String, Path)>,
    signature_types_visible: usize,
    /// `printing_context.inlined_types` while printing a type declaration.
    inlined_types: Option<Vec<crate::types::decl::TypeInlinedType>>,
    /// Qualified prefixes of the persistent-unit signatures being printed,
    /// innermost last. Rust stores a unit's signature with its paths
    /// qualified by the unit (the `prefix_idents` form of its components);
    /// OCaml prints the raw `ps_sig`, where they are local identifiers.
    unit_prefixes: Vec<Path>,
}

impl<'a> Printtyp<'a> {
    pub(crate) fn new(ctx: &'a TypeContext) -> Self {
        Self {
            ctx,
            names: Vec::new(),
            name_counter: 0,
            named_vars: Vec::new(),
            weak_counter: 1,
            weak_var_map: Vec::new(),
            named_weak_vars: Vec::new(),
            visited_objects: Vec::new(),
            aliased: Vec::new(),
            delayed: Vec::new(),
            unique_names: Vec::new(),
            printing_env: None,
            signature_types: Vec::new(),
            signature_types_visible: 0,
            inlined_types: None,
            unit_prefixes: Vec::new(),
        }
    }

    /// `set_printing_env env`.
    pub(crate) fn set_printing_env(&mut self, env: &crate::types::env::Env) {
        self.printing_env = Some(env.clone());
    }

    // ------------------------------------------------------------------
    // Paths
    // ------------------------------------------------------------------

    fn non_shadowed_pervasive_or_stdlib(&self, path: &Path) -> bool {
        let Path::Pdot(parent, s, _) = path else {
            return false;
        };
        let Path::Pident(id) = parent.as_ref() else {
            return false;
        };
        if !(id.is_persistent() && matches!(id.name(), "Pervasives" | "Stdlib")) {
            return false;
        }
        if let Some((_, found)) = self.signature_types[..self.signature_types_visible]
            .iter()
            .rev()
            .find(|(name, _)| name == s.as_str())
        {
            return path.same(found);
        }
        // `Env.lookup_type (Lident s) !printing_env`; every lookup fails in
        // `Env.empty`.
        match &self.printing_env {
            None => true,
            Some(env) => match env.find_type_with_path(s) {
                Ok((found, _)) => path.same(&found),
                Err(_) => true,
            },
        }
    }

    /// `ident_name`.
    fn ident_name(&self, id: &crate::ident::Ident) -> String {
        self.unique_names
            .iter()
            .find(|(i, _)| i.same(id))
            .map(|(_, n)| n.clone())
            .unwrap_or_else(|| id.name().to_string())
    }

    /// `add_unique`.
    fn add_unique(&mut self, id: &crate::ident::Ident) {
        if !self.unique_names.iter().any(|(i, _)| i.same(id)) {
            let unique = id.unique_toplevel_name();
            self.unique_names.push((*id, unique));
        }
    }

    /// `tree_of_path`.
    pub(crate) fn tree_of_path(&self, path: &Path) -> OutIdent {
        if let Some(relative) = self.unit_relative_path(path) {
            return relative;
        }
        match path {
            Path::Pident(id) => OutIdent::Oide_ident(self.ident_name(id)),
            Path::Pdot(_, s, _) if self.non_shadowed_pervasive_or_stdlib(path) => {
                OutIdent::Oide_ident(s.to_string())
            }
            Path::Pdot(p, s, _) if p.name().starts_with("Stdlib_") => {
                let path_name = p.name();
                OutIdent::Oide_dot(
                    Box::new(OutIdent::Oide_ident(path_name[7..].to_string())),
                    s.to_string(),
                )
            }
            Path::Pdot(p, s, _) => {
                OutIdent::Oide_dot(Box::new(self.tree_of_path(p)), s.to_string())
            }
            Path::Papply(p1, p2) => OutIdent::Oide_apply(
                Box::new(self.tree_of_path(p1)),
                Box::new(self.tree_of_path(p2)),
            ),
        }
    }

    /// `string_of_path` (printtyp.ml:89-96).
    pub(crate) fn string_of_path(&self, path: &Path) -> String {
        fn string_of_out_ident(ident: &OutIdent) -> String {
            match ident {
                OutIdent::Oide_ident(s) => s.clone(),
                OutIdent::Oide_dot(id, s) => format!("{}.{}", string_of_out_ident(id), s),
                OutIdent::Oide_apply(id1, id2) => {
                    format!("{}({})", string_of_out_ident(id1), string_of_out_ident(id2))
                }
            }
        }
        string_of_out_ident(&self.tree_of_path(path))
    }

    // ------------------------------------------------------------------
    // Names
    // ------------------------------------------------------------------

    fn reset_names(&mut self) {
        self.names.clear();
        self.name_counter = 0;
        self.named_vars.clear();
    }

    fn add_named_var(&mut self, ty: TypeExprRef) {
        if let TypeDesc::Tvar(Some(name), ..) | TypeDesc::Tunivar(Some(name), ..) =
            &*self.ctx.borrow_desc(ty)
            && !self.named_vars.contains(name)
        {
            self.named_vars.push(name.clone());
        }
    }

    fn name_is_already_used(&self, name: &str) -> bool {
        self.named_vars.iter().any(|n| n == name)
            || self.names.iter().any(|(_, n)| n == name)
            || self.named_weak_vars.iter().any(|n| n == name)
    }

    fn new_name(&mut self) -> String {
        loop {
            let letter = (b'a' + (self.name_counter % 26) as u8) as char;
            let name = if self.name_counter < 26 {
                letter.to_string()
            } else {
                format!("{letter}{}", self.name_counter / 26)
            };
            self.name_counter += 1;
            if !self.name_is_already_used(&name) {
                return name;
            }
        }
    }

    fn new_weak_name(&mut self, ty: TypeExprRef) -> String {
        loop {
            let name = format!("weak{}", self.weak_counter);
            self.weak_counter += 1;
            if !self.name_is_already_used(&name) {
                self.named_weak_vars.push(name.clone());
                self.weak_var_map.push((ty, name.clone()));
                return name;
            }
        }
    }

    /// `name_of_type`; `weak` selects `new_weak_name ty` over `new_name`.
    fn name_of_type(&mut self, weak: bool, t: TypeExprRef) -> String {
        if let Some((_, name)) = self.names.iter().find(|(ty, _)| *ty == t) {
            return name.clone();
        }
        if let Some((_, name)) = self.weak_var_map.iter().find(|(ty, _)| *ty == t) {
            return name.clone();
        }
        let given = match &*self.ctx.borrow_desc(t) {
            TypeDesc::Tvar(Some(name), ..) | TypeDesc::Tunivar(Some(name), ..) => {
                Some(name.clone())
            }
            _ => None,
        };
        let name = match given {
            Some(name) => {
                let mut current_name = name.clone();
                let mut i = 0;
                while self.names.iter().any(|(_, n)| *n == current_name) {
                    current_name = format!("{name}{i}");
                    i += 1;
                }
                current_name
            }
            None if weak => self.new_weak_name(t),
            None => self.new_name(),
        };
        if name != "_" {
            self.names.insert(0, (t, name.clone()));
        }
        name
    }

    fn check_name_of_type(&mut self, t: TypeExprRef) {
        self.name_of_type(false, t);
    }

    fn remove_names(&mut self, tyl: &[TypeExprRef]) {
        let tyl: Vec<TypeExprRef> = tyl.iter().map(|t| self.ctx.repr(*t)).collect();
        self.names.retain(|(ty, _)| !tyl.contains(ty));
    }

    // ------------------------------------------------------------------
    // Loop marks
    // ------------------------------------------------------------------

    fn add_delayed(&mut self, t: TypeExprRef) {
        if !self.delayed.contains(&t) {
            self.delayed.insert(0, t);
        }
    }

    fn proxy(&self, ty: TypeExprRef) -> TypeExprRef {
        btype::proxy(self.ctx, ty)
    }

    fn is_aliased(&self, ty: TypeExprRef) -> bool {
        self.aliased.contains(&self.proxy(ty))
    }

    fn add_alias(&mut self, ty: TypeExprRef) {
        let px = self.proxy(ty);
        if !self.is_aliased(px) {
            self.aliased.insert(0, px);
            self.add_named_var(px);
        }
    }

    /// `aliasable`; with `real_paths` every `Tconstr` path is `Id`.
    fn aliasable(&self, ty: TypeExprRef) -> bool {
        !matches!(
            &*self.ctx.borrow_desc(ty),
            TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tpoly { .. }
        )
    }

    fn namable_row(&self, row: &RowDesc) -> bool {
        row.row_name.is_some()
            && row
                .row_fields
                .iter()
                .all(|(_, f)| match btype::row_field_repr(self.ctx, f) {
                    RowField::Reither {
                        constant, types, ..
                    } => {
                        row.row_closed
                            && if constant {
                                types.is_empty()
                            } else {
                                types.len() == 1
                            }
                    }
                    _ => true,
                })
    }

    fn opened_object(&self, ty: TypeExprRef) -> bool {
        let mut current = match &*self.ctx.borrow_desc(self.ctx.repr(ty)) {
            TypeDesc::Tobject { fields, .. } => *fields,
            _ => return false,
        };
        loop {
            let repr = self.ctx.repr(current);
            match &*self.ctx.borrow_desc(repr) {
                TypeDesc::Tfield { rest, .. } => current = *rest,
                TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tconstr { .. } => {
                    return true;
                }
                _ => return false,
            }
        }
    }

    fn mark_loops_rec(&mut self, visited: &mut Vec<TypeExprRef>, ty: TypeExprRef) {
        let ty = self.ctx.repr(ty);
        let px = self.proxy(ty);
        if visited.contains(&px) && self.aliasable(ty) {
            self.add_alias(px);
            return;
        }
        let depth = visited.len();
        visited.push(px);
        let desc = (*self.ctx.get_desc(ty)).clone();
        match desc {
            TypeDesc::Tvar(..) => self.add_named_var(ty),
            TypeDesc::Tarrow { args, ret } => {
                for arg in &args {
                    self.mark_loops_rec(visited, arg.typ);
                }
                self.mark_loops_rec(visited, ret);
            }
            TypeDesc::Ttuple(tyl) => {
                for t in tyl {
                    self.mark_loops_rec(visited, t);
                }
            }
            TypeDesc::Tconstr { args, .. } => {
                for t in args {
                    self.mark_loops_rec(visited, t);
                }
            }
            TypeDesc::Tpackage { args, .. } => {
                for t in args {
                    self.mark_loops_rec(visited, t);
                }
            }
            TypeDesc::Tvariant(row) => {
                if self.visited_objects.contains(&px) {
                    self.add_alias(px);
                } else {
                    let row = btype::row_repr(self.ctx, &row);
                    if !btype::static_row(self.ctx, &row) {
                        self.visited_objects.insert(0, px);
                    }
                    match &row.row_name {
                        Some((_, tyl)) if self.namable_row(&row) => {
                            for t in tyl.clone() {
                                self.mark_loops_rec(visited, t);
                            }
                        }
                        _ => {
                            let mut children = Vec::new();
                            btype::iter_row(self.ctx, &row, |t| children.push(t));
                            for t in children {
                                self.mark_loops_rec(visited, t);
                            }
                        }
                    }
                }
            }
            TypeDesc::Tobject { fields } => {
                if self.visited_objects.contains(&px) {
                    self.add_alias(px);
                } else {
                    if self.opened_object(ty) {
                        self.visited_objects.insert(0, px);
                    }
                    let (fields, _) = flatten_fields(self.ctx, fields);
                    for field in fields {
                        self.mark_loops_rec(visited, field.typ);
                    }
                }
            }
            TypeDesc::Tfield { typ, rest, .. } => {
                self.mark_loops_rec(visited, typ);
                self.mark_loops_rec(visited, rest);
            }
            TypeDesc::Tnil => {}
            TypeDesc::Tsubst(t) => self.mark_loops_rec(visited, t),
            TypeDesc::Tlink(_) => unreachable!("Printtyp.mark_loops_rec (2)"),
            TypeDesc::Tpoly { body, vars } => {
                for t in vars {
                    self.add_alias(t);
                }
                self.mark_loops_rec(visited, body);
            }
            TypeDesc::Tunivar(..) => self.add_named_var(ty),
        }
        visited.truncate(depth);
    }

    /// `mark_loops`.
    pub(crate) fn mark_loops(&mut self, ty: TypeExprRef) {
        // printtyp.ml:520: `normalize_type Env.empty ty`.
        crate::types::ctype::normalize_type(self.ctx, &crate::types::env::Env::empty(), ty);
        self.mark_loops_rec(&mut Vec::new(), ty);
    }

    fn reset_loop_marks(&mut self) {
        self.visited_objects.clear();
        self.aliased.clear();
        self.delayed.clear();
    }

    /// `reset`.
    pub(crate) fn reset(&mut self) {
        self.reset_names();
        self.reset_loop_marks();
    }

    /// `reset_and_mark_loops`.
    pub(crate) fn reset_and_mark_loops(&mut self, ty: TypeExprRef) {
        self.reset();
        self.mark_loops(ty);
    }

    /// `reset_and_mark_loops_list`.
    pub(crate) fn reset_and_mark_loops_list(&mut self, tyl: &[TypeExprRef]) {
        self.reset();
        for ty in tyl {
            self.mark_loops(*ty);
        }
    }

    // ------------------------------------------------------------------
    // tree_of_typexp
    // ------------------------------------------------------------------

    fn is_non_gen(&self, sch: bool, ty: TypeExprRef) -> bool {
        sch && matches!(&*self.ctx.borrow_desc(ty), TypeDesc::Tvar(..))
            && self.ctx.get_level(ty) != GENERIC_LEVEL
    }

    /// `tree_of_typexp sch ty` (without a printing context).
    pub(crate) fn tree_of_typexp(&mut self, sch: bool, ty: TypeExprRef) -> OutType {
        let ty = self.ctx.repr(ty);
        let px = self.proxy(ty);
        if self.names.iter().any(|(t, _)| *t == px) && !self.delayed.contains(&px) {
            let mark = self.is_non_gen(sch, ty);
            let name = self.name_of_type(mark, px);
            return OutType::Otyp_var(mark, name);
        }
        let desc = (*self.ctx.get_desc(ty)).clone();
        let pr_typ = |this: &mut Self| -> OutType {
            match &desc {
                TypeDesc::Tvar(..) => {
                    let non_gen = this.is_non_gen(sch, ty);
                    let name = this.name_of_type(non_gen, ty);
                    OutType::Otyp_var(non_gen, name)
                }
                TypeDesc::Tarrow { args, ret } => {
                    let args = args
                        .iter()
                        .map(|arg| {
                            let label = arg.label();
                            let t1 = if matches!(label, ArgLabel::Optional(_)) {
                                let repr = this.ctx.repr(arg.typ);
                                let inner = match &*this.ctx.borrow_desc(repr) {
                                    TypeDesc::Tconstr { path, args, .. }
                                        if args.len() == 1
                                            && path.same(&crate::types::predef::path_option()) =>
                                    {
                                        Some(args[0])
                                    }
                                    _ => None,
                                };
                                match inner {
                                    Some(inner) => this.tree_of_typexp(sch, inner),
                                    None => OutType::Otyp_stuff("<hidden>".to_string()),
                                }
                            } else {
                                this.tree_of_typexp(sch, arg.typ)
                            };
                            let label = match label {
                                ArgLabel::Nolabel => OutArgLabel::Nolabel,
                                ArgLabel::Labelled(l) => OutArgLabel::Labelled(l.txt.clone()),
                                ArgLabel::Optional(l) => OutArgLabel::Optional(l.txt.clone()),
                            };
                            (label, t1)
                        })
                        .collect();
                    OutType::Otyp_arrow(args, Box::new(this.tree_of_typexp(sch, *ret)))
                }
                TypeDesc::Ttuple(tyl) => OutType::Otyp_tuple(this.tree_of_typlist(sch, tyl)),
                TypeDesc::Tconstr { path, .. }
                    if this.find_inlined_type(&path.name()).is_some() =>
                {
                    // Inlined records print as record structures (printtyp.ml:633-642).
                    let crate::types::decl::TypeInlinedType::Record { labels, .. } = this
                        .find_inlined_type(&path.name())
                        .cloned()
                        .expect("inlined type");
                    let labels = labels.iter().map(|l| this.tree_of_label(l)).collect();
                    OutType::Otyp_record(labels)
                }
                TypeDesc::Tconstr { path, args, .. } => {
                    OutType::Otyp_constr(this.tree_of_path(path), this.tree_of_typlist(sch, args))
                }
                TypeDesc::Tvariant(row) => this.tree_of_variant(sch, px, row),
                TypeDesc::Tobject { fields } => this.tree_of_typobject(sch, *fields),
                TypeDesc::Tnil | TypeDesc::Tfield { .. } => this.tree_of_typobject(sch, ty),
                TypeDesc::Tsubst(t) => this.tree_of_typexp(sch, *t),
                TypeDesc::Tlink(_) => unreachable!("Printtyp.tree_of_typexp"),
                TypeDesc::Tpoly { body, vars } => {
                    let tyl: Vec<TypeExprRef> = vars.iter().map(|t| this.ctx.repr(*t)).collect();
                    if tyl.is_empty() {
                        this.tree_of_typexp(sch, *body)
                    } else {
                        let old_delayed = this.delayed.clone();
                        for t in &tyl {
                            this.add_delayed(*t);
                        }
                        let tl: Vec<String> =
                            tyl.iter().map(|t| this.name_of_type(false, *t)).collect();
                        let tr = OutType::Otyp_poly(tl, Box::new(this.tree_of_typexp(sch, *body)));
                        this.remove_names(&tyl);
                        this.delayed = old_delayed;
                        tr
                    }
                }
                TypeDesc::Tunivar(..) => OutType::Otyp_var(false, this.name_of_type(false, ty)),
                TypeDesc::Tpackage { path, lids, args } => {
                    let n = lids
                        .iter()
                        .map(|li| flatten_longident(this.ctx, li).join("."))
                        .collect();
                    OutType::Otyp_module(path.name(), n, this.tree_of_typlist(sch, args))
                }
            }
        };
        let aliased = self.is_aliased(px) && self.aliasable(ty);
        if self.delayed.contains(&px) {
            self.delayed.retain(|t| *t != px);
        }
        if aliased {
            self.check_name_of_type(px);
            let inner = pr_typ(self);
            let name = self.name_of_type(false, px);
            OutType::Otyp_alias(Box::new(inner), name)
        } else {
            pr_typ(self)
        }
    }

    fn tree_of_variant(&mut self, sch: bool, px: TypeExprRef, row: &RowDesc) -> OutType {
        let row = btype::row_repr(self.ctx, row);
        let fields: Vec<(String, RowField)> = row
            .row_fields
            .iter()
            .filter(|(_, f)| {
                !row.row_closed || !matches!(btype::row_field_repr(self.ctx, f), RowField::Rabsent)
            })
            .map(|(l, f)| (l.to_string(), f.clone()))
            .collect();
        let present: Vec<String> = fields
            .iter()
            .filter(|(_, f)| matches!(btype::row_field_repr(self.ctx, f), RowField::Rpresent(_)))
            .map(|(l, _)| l.clone())
            .collect();
        let all_present = present.len() == fields.len();
        match &row.row_name {
            Some((p, tyl)) if self.namable_row(&row) => {
                let id = self.tree_of_path(p);
                let args = self.tree_of_typlist(sch, tyl);
                let out_variant = OutType::Otyp_constr(id, args);
                if row.row_closed && all_present {
                    out_variant
                } else {
                    let non_gen = self.is_non_gen(sch, px);
                    let tags = if all_present { None } else { Some(present) };
                    OutType::Otyp_variant(
                        non_gen,
                        OutVariant::Ovar_typ(Box::new(out_variant)),
                        row.row_closed,
                        tags,
                    )
                }
            }
            _ => {
                let non_gen = !(row.row_closed && all_present) && self.is_non_gen(sch, px);
                let fields = fields
                    .iter()
                    .map(|(l, f)| self.tree_of_row_field(sch, l, f))
                    .collect();
                let tags = if all_present { None } else { Some(present) };
                OutType::Otyp_variant(
                    non_gen,
                    OutVariant::Ovar_fields(fields),
                    row.row_closed,
                    tags,
                )
            }
        }
    }

    fn tree_of_row_field(
        &mut self,
        sch: bool,
        l: &str,
        f: &RowField,
    ) -> (String, bool, Vec<OutType>) {
        match btype::row_field_repr(self.ctx, f) {
            RowField::Rpresent(None) => (l.to_string(), false, Vec::new()),
            RowField::Reither {
                constant: true,
                ref types,
                ..
            } if types.is_empty() => (l.to_string(), false, Vec::new()),
            RowField::Rpresent(Some(ty)) => {
                (l.to_string(), false, vec![self.tree_of_typexp(sch, ty)])
            }
            RowField::Reither {
                constant, types, ..
            } => (l.to_string(), constant, self.tree_of_typlist(sch, &types)),
            RowField::Rabsent => (l.to_string(), false, Vec::new()),
        }
    }

    fn tree_of_typlist(&mut self, sch: bool, tyl: &[TypeExprRef]) -> Vec<OutType> {
        tyl.iter().map(|t| self.tree_of_typexp(sch, *t)).collect()
    }

    fn tree_of_typobject(&mut self, sch: bool, fi: TypeExprRef) -> OutType {
        let (fields, rest) = flatten_fields(self.ctx, fi);
        let mut present: Vec<(String, bool, TypeExprRef)> = fields
            .into_iter()
            .map(|f| {
                let mutable = matches!(
                    self.ctx.mutability_repr(f.mutability),
                    crate::types::asttypes::MutableFlag::Mutable
                );
                (f.name, mutable, f.typ)
            })
            .collect();
        present.sort_by(|(a, _, _), (b, _, _)| a.as_bytes().cmp(b.as_bytes()));
        let fields = present
            .into_iter()
            .map(|(s, mutable, t)| (s, mutable, self.tree_of_typexp(sch, t)))
            .collect();
        let rest = match &*self.ctx.borrow_desc(rest) {
            TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) => Some(self.is_non_gen(sch, rest)),
            TypeDesc::Tconstr { .. } => Some(false),
            TypeDesc::Tnil => None,
            _ => unreachable!("typfields (1)"),
        };
        OutType::Otyp_object(fields, rest)
    }

    /// `tree_of_label` (compiler/ml/printtyp.ml).
    fn tree_of_label(&mut self, l: &crate::types::decl::LabelDeclaration) -> OutRecordField {
        let opt = l.ld_optional;
        let typ = match &*self.ctx.borrow_desc(l.ld_type) {
            TypeDesc::Tconstr { path, args, .. }
                if opt && args.len() == 1 && path.same(&crate::types::predef::path_option()) =>
            {
                args[0]
            }
            _ => l.ld_type,
        };
        (
            l.ld_id.name().to_string(),
            l.ld_runtime_name.clone(),
            matches!(l.ld_mutable, crate::types::asttypes::MutableFlag::Mutable),
            opt,
            self.tree_of_typexp(false, typ),
        )
    }

    /// `tree_of_constructor_arguments` (compiler/ml/printtyp.ml).
    fn tree_of_constructor_arguments(
        &mut self,
        args: &crate::types::decl::ConstructorArguments,
    ) -> Vec<OutType> {
        match args {
            crate::types::decl::ConstructorArguments::CstrTuple(l) => {
                self.tree_of_typlist(false, l)
            }
            crate::types::decl::ConstructorArguments::CstrRecord(l) => {
                // `Cstr_record l -> [Otyp_record (List.map tree_of_label l)]`
                // drops the printing context.
                let saved = self.inlined_types.take();
                let labels = l.iter().map(|l| self.tree_of_label(l)).collect();
                self.inlined_types = saved;
                vec![OutType::Otyp_record(labels)]
            }
        }
    }

    /// `constructor_arguments ppf a`: the arguments printed as a tuple.
    pub(crate) fn constructor_arguments(
        &mut self,
        args: &crate::types::decl::ConstructorArguments,
    ) -> String {
        let tys = self.tree_of_constructor_arguments(args);
        print_out_type(&OutType::Otyp_tuple(tys))
    }

    /// `type_expr ppf ty`: print without resetting the naming state.
    pub(crate) fn type_expr(&mut self, ty: TypeExprRef) -> String {
        let tree = self.tree_of_typexp(false, ty);
        print_out_type(&tree)
    }

    /// `type_sch ppf ty`.
    pub(crate) fn type_sch(&mut self, ty: TypeExprRef) -> String {
        let tree = self.tree_of_typexp(true, ty);
        print_out_type(&tree)
    }
}

// ============================================================================
// Declarations and signatures (compiler/ml/printtyp.ml:571-1180)
// ============================================================================

impl<'a> Printtyp<'a> {
    fn find_inlined_type(&self, name: &str) -> Option<&crate::types::decl::TypeInlinedType> {
        self.inlined_types
            .as_ref()?
            .iter()
            .find(|inlined| match inlined {
                crate::types::decl::TypeInlinedType::Record { type_name, .. } => type_name == name,
            })
    }

    /// `filter_params` (printtyp.ml:573-582): repeated parameters become
    /// fresh `Tsubst` nodes.
    fn filter_params(&self, tyl: &[TypeExprRef]) -> Vec<TypeExprRef> {
        let mut params: Vec<TypeExprRef> = Vec::with_capacity(tyl.len());
        for ty in tyl {
            let ty = self.ctx.repr(*ty);
            if params.contains(&ty) {
                params.push(self.ctx.new_generic_type(TypeDesc::Tsubst(ty)));
            } else {
                params.push(ty);
            }
        }
        params
    }

    /// `Ctype.free_variables` without an environment (ctype.ml:370-409).
    fn free_variables(&self, ty: TypeExprRef) -> Vec<TypeExprRef> {
        fn go(
            ctx: &TypeContext,
            visited: &mut Vec<TypeExprRef>,
            vars: &mut Vec<TypeExprRef>,
            ty: TypeExprRef,
        ) {
            let ty = ctx.repr(ty);
            if visited.contains(&ty) {
                return;
            }
            visited.push(ty);
            let desc = (*ctx.get_desc(ty)).clone();
            match desc {
                TypeDesc::Tvar(..) => vars.push(ty),
                TypeDesc::Tobject { fields, .. } => go(ctx, visited, vars, fields),
                TypeDesc::Tfield { typ, rest, .. } => {
                    go(ctx, visited, vars, typ);
                    go(ctx, visited, vars, rest);
                }
                TypeDesc::Tvariant(row) => {
                    let row = btype::row_repr(ctx, &row);
                    let mut children = Vec::new();
                    btype::iter_row(ctx, &row, |t| children.push(t));
                    for t in children {
                        go(ctx, visited, vars, t);
                    }
                    if !btype::static_row(ctx, &row) {
                        go(ctx, visited, vars, row.row_more);
                    }
                }
                _ => {
                    let mut children = Vec::new();
                    btype::iter_type_expr(ctx, ty, |t| children.push(t));
                    for t in children {
                        go(ctx, visited, vars, t);
                    }
                }
            }
        }
        let mut vars = Vec::new();
        go(self.ctx, &mut Vec::new(), &mut vars, ty);
        vars
    }

    fn mark_loops_constructor_arguments(
        &mut self,
        args: &crate::types::decl::ConstructorArguments,
    ) {
        match args {
            crate::types::decl::ConstructorArguments::CstrTuple(l) => {
                for ty in l {
                    self.mark_loops(*ty);
                }
            }
            crate::types::decl::ConstructorArguments::CstrRecord(l) => {
                for label in l {
                    self.mark_loops(label.ld_type);
                }
            }
        }
    }

    /// `tree_of_type_decl` (printtyp.ml:789-930).
    pub(crate) fn tree_of_type_decl(
        &mut self,
        id: &crate::ident::Ident,
        decl: &crate::types::decl::TypeDeclaration,
    ) -> OutTypeDecl {
        use crate::types::PrivateFlag;
        use crate::types::decl::TypeKind;
        self.reset();
        let saved_inlined = self.inlined_types.replace(decl.type_inlined_types.clone());
        let params = self.filter_params(&decl.type_params);

        if let Some(ty) = decl.type_manifest {
            let vars = self.free_variables(ty);
            for param in &params {
                let is_underscore = matches!(&*self.ctx.borrow_desc(*param), TypeDesc::Tvar(Some(name), ..) if name == "_");
                if is_underscore && vars.contains(param) {
                    self.ctx.set_desc(
                        *param,
                        TypeDesc::Tvar(None, crate::types::type_expr::VarDescBlock::OWN),
                    );
                }
            }
        }

        for param in &params {
            self.add_alias(*param);
        }
        for param in &params {
            self.mark_loops(*param);
        }
        for param in &params {
            let px = self.proxy(*param);
            self.check_name_of_type(px);
        }
        let ty_manifest = decl.type_manifest.map(|ty| {
            // Special hack to hide variant name.
            let repr = self.ctx.repr(ty);
            let desc = (*self.ctx.get_desc(repr)).clone();
            let ty = match desc {
                TypeDesc::Tvariant(row) => {
                    let row = btype::row_repr(self.ctx, &row);
                    match &row.row_name {
                        Some((Path::Pident(id2), _)) if id2.same(id) => {
                            self.ctx
                                .new_generic_type(TypeDesc::Tvariant(Box::new(RowDesc {
                                    row_name: None,
                                    ..row
                                })))
                        }
                        _ => ty,
                    }
                }
                _ => ty,
            };
            self.mark_loops(ty);
            ty
        });
        match &decl.type_kind {
            TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
            TypeKind::TypeVariant(cstrs, _) => {
                for c in cstrs {
                    self.mark_loops_constructor_arguments(&c.cd_args);
                    if let Some(res) = c.cd_res {
                        self.mark_loops(res);
                    }
                }
            }
            TypeKind::TypeRecord(labels, _) => {
                for l in labels {
                    self.mark_loops(l.ld_type);
                }
            }
        }

        let abstr = match &decl.type_kind {
            TypeKind::TypeAbstract => {
                decl.type_manifest.is_none() || decl.type_private == PrivateFlag::Private
            }
            TypeKind::TypeRecord(..) => decl.type_private == PrivateFlag::Private,
            TypeKind::TypeVariant(cstrs, _) => {
                decl.type_private == PrivateFlag::Private
                    || cstrs.iter().any(|cd| cd.cd_res.is_some())
            }
            TypeKind::TypeOpen => decl.type_manifest.is_none(),
        };
        let vari: Vec<(bool, bool)> = decl
            .type_params
            .iter()
            .zip(decl.type_variance.iter())
            .map(|(ty, v)| {
                if abstr || !btype::is_tvar(self.ctx, *ty) {
                    v.get_upper()
                } else {
                    (true, true)
                }
            })
            .collect();
        let args: Vec<(String, (bool, bool))> = params
            .iter()
            .zip(vari)
            .map(|(ty, cocn)| {
                let name = match self.tree_of_typexp(false, *ty) {
                    OutType::Otyp_var(_, id) => id,
                    _ => "?".to_string(),
                };
                (name, cocn)
            })
            .collect();

        let constraints = self.tree_of_constraints(&params);
        let tree_of_manifest = |this: &mut Self, ty1: OutType| match ty_manifest {
            None => ty1,
            Some(ty) => {
                OutType::Otyp_manifest(Box::new(this.tree_of_typexp(false, ty)), Box::new(ty1))
            }
        };
        let boxed_unboxed = decl.type_representation == crate::types::TypeRepresentation::Unboxed;
        let (typ, private, unboxed) = match &decl.type_kind {
            TypeKind::TypeAbstract => match ty_manifest {
                None => (OutType::Otyp_abstract, false, boxed_unboxed),
                Some(ty) => (
                    self.tree_of_typexp(false, ty),
                    decl.type_private == PrivateFlag::Private,
                    boxed_unboxed,
                ),
            },
            TypeKind::TypeVariant(cstrs, layout_ref) => {
                let layout = self.ctx.variant_layout(*layout_ref);
                let unboxed = boxed_unboxed || layout.configuration().unboxed;
                let constructors = cstrs
                    .iter()
                    .enumerate()
                    .map(|(position, cd)| self.tree_of_constructor(cd, Some(&layout), position))
                    .collect();
                (
                    tree_of_manifest(self, OutType::Otyp_sum(constructors)),
                    decl.type_private == PrivateFlag::Private,
                    unboxed,
                )
            }
            TypeKind::TypeRecord(labels, _) => {
                let labels = labels.iter().map(|l| self.tree_of_label(l)).collect();
                (
                    tree_of_manifest(self, OutType::Otyp_record(labels)),
                    decl.type_private == PrivateFlag::Private,
                    boxed_unboxed,
                )
            }
            TypeKind::TypeOpen => (
                tree_of_manifest(self, OutType::Otyp_open),
                decl.type_private == PrivateFlag::Private,
                boxed_unboxed,
            ),
        };
        let immediate = decl
            .type_attributes
            .iter()
            .any(|attr| attr.attr_name.txt == "immediate");
        self.inlined_types = saved_inlined;
        OutTypeDecl {
            name: id.name().to_string(),
            params: args,
            typ,
            private,
            immediate,
            unboxed,
            cstrs: constraints,
        }
    }

    /// `tree_of_constructor` (printtyp.ml:936-964).
    fn tree_of_constructor(
        &mut self,
        cd: &crate::types::decl::ConstructorDeclaration,
        layout: Option<&crate::types::VariantLayout>,
        position: usize,
    ) -> OutConstructor {
        use crate::types::decl::ConstructorArguments;
        let name = cd.cd_id.name().to_string();
        // The `@as` of a nullary case or of a tagged case with a payload sets
        // its runtime tag; an untagged case is its payload.
        let tagged = matches!(&cd.cd_args, ConstructorArguments::CstrTuple(args) if args.is_empty())
            || matches!(
                layout.and_then(|layout| layout.constructors.get(position)),
                Some(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Tagged(_)
                ))
            );
        let repr = if !tagged {
            None
        } else {
            // printtyp.ml: the declared `@as`, `Option.map as_annotation
            // cd.cd_runtime_tag`.
            match cd.cd_runtime_tag.clone() {
                Some(crate::types::VariantLiteralTag::Null) => Some("@as(null)".to_string()),
                Some(crate::types::VariantLiteralTag::Undefined) => {
                    Some("@as(undefined)".to_string())
                }
                Some(crate::types::VariantLiteralTag::String(s)) => Some(format!(
                    "@as(\"{}\")",
                    crate::string_literal::ocaml_escaped(&s)
                )),
                Some(crate::types::VariantLiteralTag::Int(i)) => Some(format!("@as({i})")),
                Some(crate::types::VariantLiteralTag::Float(f)) => Some(format!("@as({f})")),
                Some(crate::types::VariantLiteralTag::Bool(b)) => Some(format!("@as({b})")),
                Some(crate::types::VariantLiteralTag::BigInt(s)) => Some(format!("@as({s}n)")),
                None => None,
            }
        };
        match cd.cd_res {
            None => {
                let args = self.tree_of_constructor_arguments(&cd.cd_args);
                (name, args, None, repr)
            }
            Some(res) => {
                let nm = std::mem::take(&mut self.names);
                let ret = self.tree_of_typexp(false, res);
                let args = self.tree_of_constructor_arguments(&cd.cd_args);
                self.names = nm;
                (name, args, Some(ret), repr)
            }
        }
    }

    /// `tree_of_constraints` (printtyp.ml:979-987).
    fn tree_of_constraints(&mut self, params: &[TypeExprRef]) -> Vec<(OutType, OutType)> {
        let mut list = Vec::new();
        for ty in params.iter().rev() {
            let ty2 = self.unalias(*ty);
            if self.proxy(*ty) != self.proxy(ty2) {
                let tr = self.tree_of_typexp(true, *ty);
                let tr2 = self.tree_of_typexp(true, ty2);
                list.insert(0, (tr, tr2));
            }
        }
        list
    }

    /// `tree_of_type_declaration id decl rs` (printtyp.ml:1007-1008).
    pub(crate) fn tree_of_type_declaration(
        &mut self,
        id: &crate::ident::Ident,
        decl: &crate::types::decl::TypeDeclaration,
        rs: crate::types::decl::RecStatus,
    ) -> OutSigItem {
        OutSigItem::Osig_type(self.tree_of_type_decl(id, decl), tree_of_rec(rs))
    }

    /// `tree_of_extension_constructor` (printtyp.ml:1019-1064).
    pub(crate) fn tree_of_extension_constructor(
        &mut self,
        id: &crate::ident::Ident,
        ext: &crate::types::decl::ExtensionConstructor,
        es: crate::types::decl::ExtStatus,
    ) -> OutSigItem {
        use crate::types::decl::ExtStatus;
        self.reset();
        let ty_name = ext.ext_type_path.name();
        let ty_params = self.filter_params(&ext.ext_type_params);
        for param in &ty_params {
            self.add_alias(*param);
        }
        for param in &ty_params {
            self.mark_loops(*param);
        }
        for param in &ty_params {
            let px = self.proxy(*param);
            self.check_name_of_type(px);
        }
        self.mark_loops_constructor_arguments(&ext.ext_args);
        if let Some(ret) = ext.ext_ret_type {
            self.mark_loops(ret);
        }
        let ty_params = ty_params
            .iter()
            .map(|ty| match self.tree_of_typexp(false, *ty) {
                OutType::Otyp_var(_, id) => id,
                _ => "?".to_string(),
            })
            .collect();
        let (args, ret) = match ext.ext_ret_type {
            None => (self.tree_of_constructor_arguments(&ext.ext_args), None),
            Some(res) => {
                let nm = std::mem::take(&mut self.names);
                let ret = self.tree_of_typexp(false, res);
                let args = self.tree_of_constructor_arguments(&ext.ext_args);
                self.names = nm;
                (args, Some(ret))
            }
        };
        let out = OutExtensionConstructor {
            name: id.name().to_string(),
            type_name: ty_name,
            type_params: ty_params,
            args,
            ret_type: ret,
            repr: None,
            private: ext.ext_private == crate::types::PrivateFlag::Private,
        };
        let es = match es {
            ExtStatus::TextFirst => OutExtStatus::Oext_first,
            ExtStatus::TextNext => OutExtStatus::Oext_next,
            ExtStatus::TextException => OutExtStatus::Oext_exception,
        };
        OutSigItem::Osig_typext(out, es)
    }

    /// `tree_of_value_description` (printtyp.ml:1071-1083) with `Primitive.print`.
    pub(crate) fn tree_of_value_description(
        &mut self,
        id: &crate::ident::Ident,
        decl: &crate::types::decl::ValueDescription,
    ) -> OutSigItem {
        self.reset_and_mark_loops(decl.val_type);
        let typ = self.tree_of_typexp(true, decl.val_type);
        // primitive.ml `print`.
        let prim = match &decl.val_kind {
            crate::types::decl::ValueKind::ValPrim(p) => Some(match &p.prim_kind {
                crate::types::decl::PrimKind::KindIntrinsic => OutPrim::Name(p.prim_name.clone()),
                crate::types::decl::PrimKind::KindExternal(spec) => OutPrim::Ffi {
                    name: p.prim_name.clone(),
                    spec: (**spec).clone(),
                },
                crate::types::decl::PrimKind::KindInlineConst(c) => {
                    OutPrim::InlineConst((**c).clone())
                }
            }),
            crate::types::decl::ValueKind::ValReg => None,
        };
        OutSigItem::Osig_value(OutValDecl {
            name: id.name().to_string(),
            typ,
            prim,
        })
    }

    /// `tree_of_modtype ~ellipsis` (printtyp.ml:1127-1143).
    pub(crate) fn tree_of_modtype(
        &mut self,
        mty: &crate::types::decl::ModuleType,
        ellipsis: bool,
    ) -> OutModuleType {
        use crate::types::decl::ModuleType;
        match mty {
            ModuleType::MtyIdent(p) => OutModuleType::Omty_ident(self.tree_of_path(p)),
            ModuleType::MtySignature(sg) => OutModuleType::Omty_signature(if ellipsis {
                vec![OutSigItem::Osig_ellipsis]
            } else {
                self.tree_of_signature(sg)
            }),
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                let res = self.tree_of_modtype(result, ellipsis);
                let arg = param_type
                    .as_ref()
                    .map(|mty| Box::new(self.tree_of_modtype(mty, false)));
                OutModuleType::Omty_functor(param.name().to_string(), arg, Box::new(res))
            }
            ModuleType::MtyAlias(_, p) => OutModuleType::Omty_alias(self.tree_of_path(p)),
        }
    }

    /// A path into one of the persistent-unit signatures being printed, as
    /// the path relative to the innermost enclosing one.
    fn unit_relative_path(&self, path: &Path) -> Option<OutIdent> {
        fn strip(path: &Path, prefix: &Path) -> Option<Vec<String>> {
            if path.same(prefix) {
                return Some(Vec::new());
            }
            match path {
                Path::Pdot(parent, name, _) => {
                    let mut rest = strip(parent, prefix)?;
                    rest.push(name.to_string());
                    Some(rest)
                }
                _ => None,
            }
        }
        self.unit_prefixes.iter().rev().find_map(|prefix| {
            let rest = strip(path, prefix)?;
            let mut parts = rest.into_iter();
            let first = parts.next()?;
            Some(parts.fold(OutIdent::Oide_ident(first), |acc, part| {
                OutIdent::Oide_dot(Box::new(acc), part)
            }))
        })
    }

    /// `tree_of_modtype` for a signature loaded from the persistent unit
    /// `origin`.
    pub(crate) fn tree_of_modtype_in_unit(
        &mut self,
        mty: &crate::types::decl::ModuleType,
        origin: &Path,
    ) -> OutModuleType {
        self.unit_prefixes.push(origin.clone());
        let tree = self.tree_of_modtype(mty, false);
        self.unit_prefixes.pop();
        tree
    }

    /// `tree_of_signature` (printtyp.ml:1145-1165): each item is printed in
    /// the environment extended with the items before it; the members of a
    /// recursive type group after the first see the environment of the
    /// group start.
    pub(crate) fn tree_of_signature(
        &mut self,
        sg: &[crate::types::decl::SignatureItem],
    ) -> Vec<OutSigItem> {
        use crate::types::decl::{RecStatus, SignatureItem};
        // `signature_types` is used as a stack: entries past the visible
        // prefix belong to an enclosing recursive group and are set aside
        // while this signature is printed.
        let saved_visible = self.signature_types_visible;
        let hidden = self.signature_types.split_off(saved_visible);
        let mut in_type_group = false;
        let mut trees = Vec::new();
        for item in sg {
            in_type_group = match (in_type_group, item) {
                (true, SignatureItem::SigType(_, _, RecStatus::TrecNext)) => true,
                (_, SignatureItem::SigType(_, _, RecStatus::TrecNot | RecStatus::TrecFirst)) => {
                    self.signature_types_visible = self.signature_types.len();
                    true
                }
                _ => {
                    self.signature_types_visible = self.signature_types.len();
                    false
                }
            };
            if let Some(tree) = self.tree_of_sigitem(item) {
                trees.push(tree);
            }
            if let SignatureItem::SigType(id, _, _) = item {
                self.signature_types
                    .push((id.name().to_string(), Path::Pident(*id)));
            }
        }
        self.signature_types.truncate(saved_visible);
        self.signature_types.extend(hidden);
        self.signature_types_visible = saved_visible;
        trees
    }

    /// `trees_of_sigitem` (printtyp.ml:1167-1182).
    fn tree_of_sigitem(&mut self, item: &crate::types::decl::SignatureItem) -> Option<OutSigItem> {
        use crate::types::decl::SignatureItem;
        match item {
            SignatureItem::SigValue(id, decl) => Some(self.tree_of_value_description(id, decl)),
            SignatureItem::SigType(id, _, _) if btype::is_row_name(id.name()) => None,
            SignatureItem::SigType(id, decl, rs) => {
                Some(self.tree_of_type_declaration(id, decl, *rs))
            }
            SignatureItem::SigTypext(id, ext, es) => {
                Some(self.tree_of_extension_constructor(id, ext, *es))
            }
            SignatureItem::SigModule(id, md, rs) => {
                let ellipsis = md.md_attributes.iter().any(|attr| {
                    attr.attr_name.txt == "..."
                        && matches!(
                            attr.attr_payload,
                            crate::types::decl::AttributePayload::Empty
                        )
                });
                Some(self.tree_of_module(id, &md.md_type, *rs, ellipsis))
            }
            SignatureItem::SigModtype(id, decl) => Some(self.tree_of_modtype_declaration(id, decl)),
            SignatureItem::SigClass | SignatureItem::SigClassType => Some(OutSigItem::Osig_class),
        }
    }

    /// `tree_of_modtype_declaration` (printtyp.ml:1184-1189).
    pub(crate) fn tree_of_modtype_declaration(
        &mut self,
        id: &crate::ident::Ident,
        decl: &crate::types::decl::ModtypeDeclaration,
    ) -> OutSigItem {
        let mty = match &decl.mtd_type {
            None => OutModuleType::Omty_abstract,
            Some(mty) => self.tree_of_modtype(mty, false),
        };
        OutSigItem::Osig_modtype(id.name().to_string(), mty)
    }

    /// `tree_of_module` (printtyp.ml:1191-1192).
    pub(crate) fn tree_of_module(
        &mut self,
        id: &crate::ident::Ident,
        mty: &crate::types::decl::ModuleType,
        rs: crate::types::decl::RecStatus,
        ellipsis: bool,
    ) -> OutSigItem {
        // A submodule of a persistent unit is qualified by the unit's path.
        let scoped = self
            .unit_prefixes
            .last()
            .map(|prefix| Path::pdot(prefix.clone(), id.name().to_string()));
        if let Some(prefix) = &scoped {
            self.unit_prefixes.push(prefix.clone());
        }
        let tree = self.tree_of_modtype(mty, ellipsis);
        if scoped.is_some() {
            self.unit_prefixes.pop();
        }
        OutSigItem::Osig_module(id.name().to_string(), tree, tree_of_rec(rs))
    }
}

/// `tree_of_rec` (printtyp.ml:100-103).
fn tree_of_rec(rs: crate::types::decl::RecStatus) -> OutRecStatus {
    match rs {
        crate::types::decl::RecStatus::TrecNot => OutRecStatus::Orec_not,
        crate::types::decl::RecStatus::TrecFirst => OutRecStatus::Orec_first,
        crate::types::decl::RecStatus::TrecNext => OutRecStatus::Orec_next,
    }
}

/// `Ctype.flatten_fields` (compiler/ml/ctype.ml): the chain is accumulated
/// in reverse and then stably sorted by name.
fn flatten_fields(
    ctx: &TypeContext,
    ty: TypeExprRef,
) -> (Vec<crate::types::ctype::FieldInfo>, TypeExprRef) {
    crate::types::ctype::flatten_fields(ctx, ty)
}

/// `Longident.flatten`.
fn flatten_longident(ctx: &TypeContext, lid: &Longident) -> Vec<String> {
    let component = |idx| {
        ctx.resolve_any_longident_component(idx)
            .unwrap_or_else(|| format!("#{}", idx.raw()))
    };
    match lid {
        Longident::Lident(name) => vec![component(*name)],
        Longident::Ldot(prefix, name) => {
            let mut parts = flatten_longident(ctx, prefix);
            parts.push(component(*name));
            parts
        }
        Longident::Lapply(..) => unreachable!("Longident.flat"),
    }
}

// ============================================================================
// Res_outcome_printer (compiler/syntax/src/res_outcome_printer.ml)
// ============================================================================

use crate::parser::printer::{print_ident_like, print_poly_var_ident};

/// `print_out_ident_doc`.
fn print_out_ident_doc(allow_uident: bool, ident: &OutIdent) -> Doc {
    match ident {
        OutIdent::Oide_ident(s) => print_ident_like(s, allow_uident, false),
        OutIdent::Oide_dot(ident, s) => Doc::concat(vec![
            print_out_ident_doc(true, ident),
            Doc::dot(),
            Doc::text(s.clone()),
        ]),
        OutIdent::Oide_apply(call, arg) => Doc::concat(vec![
            print_out_ident_doc(true, call),
            Doc::lparen(),
            print_out_ident_doc(true, arg),
            Doc::rparen(),
        ]),
    }
}

/// `print_out_type_doc`.
pub(crate) fn print_out_type_doc(out_type: &OutType) -> Doc {
    match out_type {
        OutType::Otyp_abstract | OutType::Otyp_open => Doc::nil(),
        OutType::Otyp_variant(non_gen, out_variant, closed, labels) => {
            let opening = match (closed, labels) {
                (true, None) => Doc::soft_line(),
                (false, None) => Doc::concat(vec![Doc::greater_than(), Doc::line()]),
                (true, Some(_)) => Doc::concat(vec![Doc::less_than(), Doc::line()]),
                (false, Some(_)) => Doc::concat(vec![Doc::text("?"), Doc::line()]),
            };
            Doc::group(Doc::concat(vec![
                if *non_gen { Doc::text("_") } else { Doc::nil() },
                Doc::lbracket(),
                Doc::indent(Doc::concat(vec![opening, print_out_variant(out_variant)])),
                Doc::soft_line(),
                Doc::rbracket(),
            ]))
        }
        OutType::Otyp_alias(typ, alias_txt) => Doc::concat(vec![
            Doc::lparen(),
            print_out_type_doc(typ),
            Doc::text(" as '"),
            Doc::text(alias_txt.clone()),
            Doc::rparen(),
        ]),
        OutType::Otyp_constr(out_ident, args) if args.is_empty() => {
            print_out_ident_doc(false, out_ident)
        }
        OutType::Otyp_manifest(typ1, typ2) => Doc::concat(vec![
            print_out_type_doc(typ1),
            Doc::text(" = "),
            print_out_type_doc(typ2),
        ]),
        OutType::Otyp_record(record) => print_record_declaration_doc(true, record),
        OutType::Otyp_stuff(txt) => Doc::text(txt.clone()),
        OutType::Otyp_var(ng, s) => Doc::concat(vec![
            Doc::text(if *ng { "'_" } else { "'" }),
            Doc::text(s.clone()),
        ]),
        OutType::Otyp_object(fields, rest) => print_object_fields(fields, rest),
        OutType::Otyp_constr(out_ident, args) => {
            let args_doc = Doc::concat(vec![
                Doc::less_than(),
                Doc::indent(Doc::concat(vec![
                    Doc::soft_line(),
                    Doc::join(
                        Doc::concat(vec![Doc::comma(), Doc::line()]),
                        args.iter().map(print_out_type_doc).collect(),
                    ),
                ])),
                Doc::trailing_comma(),
                Doc::soft_line(),
                Doc::greater_than(),
            ]);
            Doc::group(Doc::concat(vec![
                print_out_ident_doc(true, out_ident),
                args_doc,
            ]))
        }
        OutType::Otyp_tuple(tuple_args) => Doc::group(Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(
                    Doc::concat(vec![Doc::comma(), Doc::line()]),
                    tuple_args.iter().map(print_out_type_doc).collect(),
                ),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rparen(),
        ])),
        OutType::Otyp_poly(vars, out_type) => Doc::group(Doc::concat(vec![
            Doc::join(
                Doc::space(),
                vars.iter()
                    .map(|var| Doc::text(format!("'{var}")))
                    .collect(),
            ),
            Doc::dot(),
            Doc::space(),
            print_out_type_doc(out_type),
        ])),
        OutType::Otyp_arrow(..) => print_out_arrow_type(out_type),
        OutType::Otyp_sum(constructors) => print_out_constructors_doc(constructors),
        OutType::Otyp_module(mod_name, string_list, out_types) => {
            let package_type_doc = if string_list.is_empty() && out_types.is_empty() {
                Doc::nil()
            } else {
                let package = Doc::join(
                    Doc::line(),
                    string_list
                        .iter()
                        .zip(out_types.iter())
                        .enumerate()
                        .map(|(i, (lbl, typ))| {
                            Doc::concat(vec![
                                Doc::text(if i > 0 { "and type " } else { "with type " }),
                                Doc::text(lbl.clone()),
                                Doc::text(" = "),
                                print_out_type_doc(typ),
                            ])
                        })
                        .collect(),
                );
                Doc::indent(Doc::concat(vec![Doc::line(), package]))
            };
            Doc::concat(vec![
                Doc::text("module"),
                Doc::lparen(),
                Doc::text(mod_name.clone()),
                package_type_doc,
                Doc::rparen(),
            ])
        }
    }
}

fn print_out_arrow_type(typ: &OutType) -> Doc {
    let (typ_args, ret): (&[(OutArgLabel, OutType)], &OutType) = match typ {
        OutType::Otyp_arrow(args, ret) => (args, ret),
        _ => (&[], typ),
    };
    let print_labeled_arg = |label: &str, optional_indicator: Doc, typ: &OutType| {
        Doc::group(Doc::concat(vec![
            Doc::text(format!("~{label}: ")),
            print_out_type_doc(typ),
            optional_indicator,
        ]))
    };
    let args = Doc::join(
        Doc::concat(vec![Doc::comma(), Doc::line()]),
        typ_args
            .iter()
            .map(|(lbl, typ)| match lbl {
                OutArgLabel::Nolabel => print_out_type_doc(typ),
                OutArgLabel::Labelled(label) => print_labeled_arg(label, Doc::nil(), typ),
                OutArgLabel::Optional(label) => print_labeled_arg(label, Doc::text("=?"), typ),
            })
            .collect(),
    );
    let needs_parens = match typ_args {
        [(_, OutType::Otyp_tuple(_) | OutType::Otyp_arrow(..))] => true,
        [(OutArgLabel::Nolabel, _)] => false,
        _ => true,
    };
    let args_doc = if needs_parens {
        Doc::group(Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![Doc::soft_line(), args])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rparen(),
        ]))
    } else {
        args
    };
    Doc::concat(vec![args_doc, Doc::text(" => "), print_out_type_doc(ret)])
}

fn print_out_variant(variant: &OutVariant) -> Doc {
    match variant {
        OutVariant::Ovar_fields(fields) => Doc::join(
            Doc::line(),
            fields
                .iter()
                .enumerate()
                .map(|(i, (name, ampersand, types))| {
                    let needs_parens = !matches!(types.as_slice(), [OutType::Otyp_tuple(_)]);
                    Doc::concat(vec![
                        if i > 0 {
                            Doc::text("| ")
                        } else {
                            Doc::if_breaks(Doc::text("| "), Doc::nil())
                        },
                        Doc::group(Doc::concat(vec![
                            Doc::text("#"),
                            print_poly_var_ident(name),
                            if types.is_empty() {
                                Doc::nil()
                            } else {
                                Doc::concat(vec![
                                    if *ampersand {
                                        Doc::text(" & ")
                                    } else {
                                        Doc::nil()
                                    },
                                    Doc::indent(Doc::concat(vec![Doc::join(
                                        Doc::concat(vec![Doc::text(" &"), Doc::line()]),
                                        types
                                            .iter()
                                            .map(|typ| {
                                                let out_type_doc = print_out_type_doc(typ);
                                                if needs_parens {
                                                    Doc::concat(vec![
                                                        Doc::lparen(),
                                                        out_type_doc,
                                                        Doc::rparen(),
                                                    ])
                                                } else {
                                                    out_type_doc
                                                }
                                            })
                                            .collect(),
                                    )])),
                                ])
                            },
                        ])),
                    ])
                })
                .collect(),
        ),
        OutVariant::Ovar_typ(typ) => print_out_type_doc(typ),
    }
}

fn print_object_fields(fields: &[(String, bool, OutType)], rest: &Option<bool>) -> Doc {
    let dots = match rest {
        Some(non_gen) => Doc::text(if *non_gen { "_.." } else { ".." }),
        None => {
            if fields.is_empty() {
                Doc::dot()
            } else {
                Doc::nil()
            }
        }
    };
    Doc::group(Doc::concat(vec![
        Doc::lbrace(),
        dots,
        Doc::indent(Doc::concat(vec![
            Doc::soft_line(),
            Doc::join(
                Doc::concat(vec![Doc::comma(), Doc::line()]),
                fields
                    .iter()
                    .map(|(lbl, mutable, out_type)| {
                        Doc::group(Doc::concat(vec![
                            if *mutable {
                                Doc::text("@set ")
                            } else {
                                Doc::nil()
                            },
                            Doc::text(format!("\"{lbl}\": ")),
                            print_out_type_doc(out_type),
                        ]))
                    })
                    .collect(),
            ),
        ])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::rbrace(),
    ]))
}

/// `print_record_decl_row_doc` (res_outcome_printer.ml:395-409).
fn print_record_decl_row_doc((name, runtime_name, mutable, opt, arg): &OutRecordField) -> Doc {
    Doc::group(Doc::concat(vec![
        match runtime_name {
            // `"@as(\"" ^ String.escaped runtime_name ^ "\") "`
            Some(runtime_name) => Doc::text(format!(
                "@as({}) ",
                crate::types::external_ffi_types::debug::quote(runtime_name)
            )),
            None => Doc::nil(),
        },
        if *mutable {
            Doc::text("mutable ")
        } else {
            Doc::nil()
        },
        print_ident_like(name, false, false),
        if *opt { Doc::text("?") } else { Doc::nil() },
        Doc::text(": "),
        print_out_type_doc(arg),
    ]))
}

fn print_record_declaration_doc(inline: bool, rows: &[OutRecordField]) -> Doc {
    let content = Doc::concat(vec![
        Doc::lbrace(),
        Doc::indent(Doc::concat(vec![
            Doc::soft_line(),
            Doc::join(
                Doc::concat(vec![Doc::comma(), Doc::line()]),
                rows.iter().map(print_record_decl_row_doc).collect(),
            ),
        ])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::rbrace(),
    ]);
    if inline { content } else { Doc::group(content) }
}

/// `print_out_constructors_doc` (res_outcome_printer.ml:374-390).
fn print_out_constructors_doc(constructors: &[OutConstructor]) -> Doc {
    Doc::group(Doc::indent(Doc::concat(vec![
        Doc::soft_line(),
        Doc::join(
            Doc::line(),
            constructors
                .iter()
                .enumerate()
                .map(|(i, constructor)| {
                    Doc::concat(vec![
                        if i > 0 {
                            Doc::text("| ")
                        } else {
                            Doc::if_breaks(Doc::text("| "), Doc::nil())
                        },
                        print_out_constructor_doc(constructor),
                    ])
                })
                .collect(),
        ),
    ])))
}

/// `print_out_constructor_doc` (res_outcome_printer.ml:392-437).
fn print_out_constructor_doc((name, args, gadt, repr): &OutConstructor) -> Doc {
    let repr_doc = match repr {
        None => Doc::nil(),
        Some(s) => Doc::text(format!("{s} ")),
    };
    let gadt_doc = match gadt {
        Some(out_type) => Doc::concat(vec![Doc::text(": "), print_out_type_doc(out_type)]),
        None => Doc::nil(),
    };
    let args_doc = match args.as_slice() {
        [] => Doc::nil(),
        [OutType::Otyp_record(record)] => Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(print_record_declaration_doc(true, record)),
            Doc::rparen(),
        ]),
        _ => Doc::indent(Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(
                    Doc::concat(vec![Doc::comma(), Doc::line()]),
                    args.iter().map(print_out_type_doc).collect(),
                ),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rparen(),
        ])),
    };
    Doc::group(Doc::concat(vec![
        repr_doc,
        Doc::text(name.clone()),
        args_doc,
        gadt_doc,
    ]))
}

/// `print_type_parameter_doc` (res_outcome_printer.ml:474-479).
fn print_type_parameter_doc((typ, (co, cn)): &(String, (bool, bool))) -> Doc {
    Doc::concat(vec![
        if !cn {
            Doc::text("+")
        } else if !co {
            Doc::text("-")
        } else {
            Doc::nil()
        },
        if typ == "_" {
            Doc::text("_")
        } else {
            Doc::text(format!("'{typ}"))
        },
    ])
}

fn print_type_params_doc(params: Vec<Doc>, trailing_comma: bool) -> Doc {
    if params.is_empty() {
        return Doc::nil();
    }
    Doc::group(Doc::concat(vec![
        Doc::less_than(),
        Doc::indent(Doc::concat(vec![
            Doc::soft_line(),
            Doc::join(Doc::concat(vec![Doc::comma(), Doc::line()]), params),
        ])),
        if trailing_comma {
            Doc::trailing_comma()
        } else {
            Doc::nil()
        },
        Doc::soft_line(),
        Doc::greater_than(),
    ]))
}

// Print a digested FFI declaration as the surface attributes the user wrote;
// the stored form is the declaration itself (res_outcome_printer.ml:481-613).

fn print_string_literal_doc(s: &str) -> Doc {
    // `"\"" ^ String.escaped s ^ "\""`
    Doc::text(crate::types::external_ffi_types::debug::quote(s))
}

fn print_inline_const_doc(c: &crate::types::external_ffi_types::InlineConst) -> Doc {
    use crate::types::external_ffi_types::InlineConst;
    match c {
        InlineConst::ConstString(s) => print_string_literal_doc(s),
        InlineConst::ConstBool(b) => Doc::text(if *b { "true" } else { "false" }),
        InlineConst::ConstInt(i) => Doc::text(i.to_string()),
        // res_outcome_printer.ml: `Bigint_utils.to_string positive digits ^ "n"`.
        InlineConst::ConstBigint { positive, digits } => {
            Doc::text(format!("{}{}n", if *positive { "" } else { "-" }, digits))
        }
        InlineConst::ConstFloat(f) => Doc::text(f.clone()),
    }
}

fn print_external_module_doc(emn: &crate::types::external_ffi_types::ExternalModuleName) -> Doc {
    use crate::types::external_ffi_types::ModuleBindName;
    let payload = match (&emn.module_bind_name, &emn.import_attributes) {
        (ModuleBindName::PhintNothing, None) => print_string_literal_doc(&emn.bundle),
        (ModuleBindName::PhintName(hint), None) => Doc::concat(vec![
            Doc::text("("),
            print_string_literal_doc(&emn.bundle),
            Doc::text(", "),
            print_string_literal_doc(hint),
            Doc::text(")"),
        ]),
        (bind_name, Some(import_attributes)) => {
            // `@module({from: "x", with: {k: "v"}})` record payload
            let with_fields = import_attributes
                .iter()
                .map(|(k, v)| {
                    // digestion stores the source key `type_` as `type`; other
                    // keys print escaped again to be writable source
                    let key = if k == "type" {
                        Doc::text("type_")
                    } else {
                        crate::parser::printer::print_ident_like(k, false, false)
                    };
                    Doc::concat(vec![key, Doc::text(": "), print_string_literal_doc(v)])
                })
                .collect();
            Doc::concat(vec![
                Doc::text("{from: "),
                print_string_literal_doc(&emn.bundle),
                match bind_name {
                    ModuleBindName::PhintNothing => Doc::nil(),
                    ModuleBindName::PhintName(hint) => {
                        Doc::concat(vec![Doc::text(", as: "), print_string_literal_doc(hint)])
                    }
                },
                Doc::text(", with: {"),
                Doc::join(Doc::text(", "), with_fields),
                Doc::text("}}"),
            ])
        }
    };
    Doc::concat(vec![Doc::text("@module("), payload, Doc::text(") ")])
}

fn print_scopes_doc(scopes: &[String]) -> Doc {
    match scopes {
        [] => Doc::nil(),
        [s] => Doc::concat(vec![
            Doc::text("@scope("),
            print_string_literal_doc(s),
            Doc::text(") "),
        ]),
        _ => Doc::concat(vec![
            Doc::text("@scope(("),
            Doc::join(
                Doc::text(", "),
                scopes.iter().map(|s| print_string_literal_doc(s)).collect(),
            ),
            Doc::text(")) "),
        ]),
    }
}

fn print_return_wrapper_doc(w: crate::types::external_ffi_types::ReturnWrapper) -> Doc {
    use crate::types::external_ffi_types::ReturnWrapper;
    match w {
        ReturnWrapper::ReturnUnset => Doc::nil(),
        ReturnWrapper::ReturnIdentity => Doc::text("@return(identity) "),
        ReturnWrapper::ReturnNullToOpt => Doc::text("@return(null_to_opt) "),
        ReturnWrapper::ReturnNullUndefinedToOpt => Doc::text("@return(nullable) "),
    }
}

fn print_decl_kind_doc(
    kind: &crate::types::external_ffi_types::DeclKind,
    module_: &Option<crate::types::external_ffi_types::ModuleSource>,
    prim_name: &str,
) -> Doc {
    use crate::types::external_ffi_types::{DeclKind, ModuleSource};
    // the attribute payload names the JS entity when it differs from the
    // external's primitive string; print it back
    let with_payload = |attr: &str, name: &str| {
        if name == prim_name {
            Doc::text(format!("@{attr} "))
        } else {
            Doc::concat(vec![
                Doc::text(format!("@{attr}(")),
                print_string_literal_doc(name),
                Doc::text(") "),
            ])
        }
    };
    match kind {
        // `@val` conflicts with bare `@module`; elsewhere it is the default
        // and always legal to write
        DeclKind::DeclVal { name } => match module_ {
            Some(ModuleSource::ModuleItself) => Doc::nil(),
            _ => with_payload("val", name),
        },
        DeclKind::DeclSend { name } => with_payload("send", name),
        DeclKind::DeclNew { name } => with_payload("new", name),
        DeclKind::DeclGet { name } => with_payload("get", name),
        DeclKind::DeclSet { name } => with_payload("set", name),
        DeclKind::DeclGetIndex => Doc::text("@get_index "),
        DeclKind::DeclSetIndex => Doc::text("@set_index "),
    }
}

fn print_module_source_doc(
    module_: &Option<crate::types::external_ffi_types::ModuleSource>,
) -> Doc {
    use crate::types::external_ffi_types::ModuleSource;
    match module_ {
        None => Doc::nil(),
        Some(ModuleSource::ModuleItself) => Doc::text("@module "),
        Some(ModuleSource::ModuleNamed(emn)) => print_external_module_doc(emn),
    }
}

fn print_external_decl_attrs_doc(
    decl: &crate::types::external_ffi_types::ExternalDecl,
    return_wrapper: crate::types::external_ffi_types::ReturnWrapper,
    prim_name: &str,
) -> Doc {
    Doc::concat(vec![
        print_decl_kind_doc(&decl.kind, &decl.module_, prim_name),
        print_module_source_doc(&decl.module_),
        print_scopes_doc(&decl.scopes),
        if decl.variadic {
            Doc::text("@variadic ")
        } else {
            Doc::nil()
        },
        print_return_wrapper_doc(return_wrapper),
    ])
}

/// `print_out_sig_item_doc ~print_name_as_is:false` (res_outcome_printer.ml:481-655).
pub(crate) fn print_out_sig_item_doc(item: &OutSigItem) -> Doc {
    print_out_sig_item_doc_with(item, false)
}

/// `print_out_sig_item_doc ?print_name_as_is` (res_outcome_printer.ml:481-655).
pub(crate) fn print_out_sig_item_doc_with(item: &OutSigItem, print_name_as_is: bool) -> Doc {
    match item {
        OutSigItem::Osig_class => Doc::nil(),
        OutSigItem::Osig_ellipsis => Doc::dotdotdot(),
        OutSigItem::Osig_value(value_decl) => {
            let (ffi_attrs, keyword, prim_name) = match &value_decl.prim {
                None => (Doc::nil(), "let ", None),
                Some(OutPrim::Name(s)) => (Doc::nil(), "external ", Some(s.as_str())),
                // surface syntax: `@inline("hello") let f: string`
                Some(OutPrim::InlineConst(c)) => (
                    Doc::concat(vec![
                        Doc::text("@inline("),
                        print_inline_const_doc(c),
                        Doc::text(") "),
                    ]),
                    "let ",
                    None,
                ),
                Some(OutPrim::Ffi { name, spec }) => match spec {
                    crate::types::external_ffi_types::ExternalFfi::FfiObjCreate(_) => {
                        (Doc::text("@obj "), "external ", Some(name.as_str()))
                    }
                    crate::types::external_ffi_types::ExternalFfi::FfiBs(
                        _,
                        return_wrapper,
                        decl,
                    ) => (
                        print_external_decl_attrs_doc(decl, *return_wrapper, name),
                        "external ",
                        Some(name.as_str()),
                    ),
                },
            };
            let prim_doc = match prim_name {
                None => Doc::nil(),
                Some(prim) => Doc::indent(Doc::concat(vec![
                    Doc::text(" ="),
                    Doc::line(),
                    Doc::group(Doc::text(format!("\"{prim}\""))),
                ])),
            };
            Doc::group(Doc::concat(vec![
                ffi_attrs,
                Doc::text(keyword),
                Doc::text(value_decl.name.clone()),
                Doc::text(":"),
                Doc::space(),
                print_out_type_doc(&value_decl.typ),
                prim_doc,
            ]))
        }
        OutSigItem::Osig_typext(ext, _) => print_out_extension_constructor_doc(ext),
        OutSigItem::Osig_modtype(name, OutModuleType::Omty_signature(items))
            if items.is_empty() =>
        {
            Doc::concat(vec![Doc::text("module type "), Doc::text(name.clone())])
        }
        OutSigItem::Osig_modtype(name, mty) => Doc::group(Doc::concat(vec![
            Doc::text("module type "),
            Doc::text(name.clone()),
            Doc::text(" = "),
            print_out_module_type_doc(mty),
        ])),
        OutSigItem::Osig_module(name, OutModuleType::Omty_alias(ident), _) => {
            Doc::group(Doc::concat(vec![
                Doc::text("module "),
                Doc::text(name.clone()),
                Doc::text(" ="),
                Doc::line(),
                print_out_ident_doc(true, ident),
            ]))
        }
        OutSigItem::Osig_module(name, mty, rec_status) => Doc::group(Doc::concat(vec![
            Doc::text(match rec_status {
                OutRecStatus::Orec_not => "module ",
                OutRecStatus::Orec_first => "module rec ",
                OutRecStatus::Orec_next => "and ",
            }),
            Doc::text(name.clone()),
            Doc::text(": "),
            print_out_module_type_doc(mty),
        ])),
        OutSigItem::Osig_type(decl, rec_status) => {
            let attrs = match (decl.immediate, decl.unboxed) {
                (false, false) => Doc::nil(),
                (true, false) => Doc::concat(vec![Doc::text("@immediate"), Doc::line()]),
                (false, true) => Doc::concat(vec![Doc::text("@unboxed"), Doc::line()]),
                (true, true) => Doc::concat(vec![Doc::text("@immediate @unboxed"), Doc::line()]),
            };
            let kw = Doc::text(match rec_status {
                OutRecStatus::Orec_not => "type ",
                OutRecStatus::Orec_first => "type rec ",
                OutRecStatus::Orec_next => "and ",
            });
            let type_params = print_type_params_doc(
                decl.params.iter().map(print_type_parameter_doc).collect(),
                true,
            );
            let private_doc = if decl.private {
                Doc::text("private ")
            } else {
                Doc::nil()
            };
            let kind = match &decl.typ {
                OutType::Otyp_open => {
                    Doc::concat(vec![Doc::text(" = "), private_doc, Doc::text("..")])
                }
                OutType::Otyp_abstract => Doc::nil(),
                OutType::Otyp_record(record) => Doc::concat(vec![
                    Doc::text(" = "),
                    private_doc,
                    print_record_declaration_doc(false, record),
                ]),
                // res_outcome_printer.ml: a manifest prints `= manifest = private
                // kind`, and every other kind takes the private keyword too.
                OutType::Otyp_manifest(manifest, typ) => Doc::concat(vec![
                    Doc::text(" = "),
                    print_out_type_doc(manifest),
                    Doc::text(" = "),
                    private_doc,
                    print_out_type_doc(typ),
                ]),
                typ => Doc::concat(vec![Doc::text(" = "), private_doc, print_out_type_doc(typ)]),
            };
            let constraints = if decl.cstrs.is_empty() {
                Doc::nil()
            } else {
                Doc::group(Doc::indent(Doc::concat(vec![
                    Doc::hard_line(),
                    Doc::join(
                        Doc::line(),
                        decl.cstrs
                            .iter()
                            .map(|(typ1, typ2)| {
                                Doc::group(Doc::concat(vec![
                                    Doc::text("constraint "),
                                    print_out_type_doc(typ1),
                                    Doc::text(" ="),
                                    Doc::space(),
                                    print_out_type_doc(typ2),
                                ]))
                            })
                            .collect(),
                    ),
                ])))
            };
            Doc::group(Doc::concat(vec![
                attrs,
                Doc::group(Doc::concat(vec![
                    kw,
                    if print_name_as_is {
                        Doc::text(decl.name.clone())
                    } else {
                        print_ident_like(&decl.name, false, false)
                    },
                    type_params,
                    kind,
                ])),
                constraints,
            ]))
        }
    }
}

/// `print_out_module_type_doc` (res_outcome_printer.ml:657-713).
pub(crate) fn print_out_module_type_doc(mty: &OutModuleType) -> Doc {
    match mty {
        OutModuleType::Omty_abstract => Doc::nil(),
        OutModuleType::Omty_ident(ident) => print_out_ident_doc(true, ident),
        OutModuleType::Omty_functor(..) => {
            // `collect_functor_args` (res_outcome_printer.ml:88-94).
            let mut args: Vec<(&String, &Option<Box<OutModuleType>>)> = Vec::new();
            let mut current = mty;
            while let OutModuleType::Omty_functor(lbl, arg, result) = current {
                args.push((lbl, arg));
                current = result;
            }
            let args_doc = match args.as_slice() {
                [(_, None)] => Doc::text("()"),
                _ => Doc::group(Doc::concat(vec![
                    Doc::lparen(),
                    Doc::indent(Doc::concat(vec![
                        Doc::soft_line(),
                        Doc::join(
                            Doc::concat(vec![Doc::comma(), Doc::line()]),
                            args.iter()
                                .map(|(lbl, arg)| {
                                    Doc::group(Doc::concat(vec![
                                        Doc::text((*lbl).clone()),
                                        match arg {
                                            None => Doc::nil(),
                                            Some(arg) => Doc::concat(vec![
                                                Doc::text(": "),
                                                print_out_module_type_doc(arg),
                                            ]),
                                        },
                                    ]))
                                })
                                .collect(),
                        ),
                    ])),
                    Doc::trailing_comma(),
                    Doc::soft_line(),
                    Doc::rparen(),
                ])),
            };
            Doc::group(Doc::concat(vec![
                args_doc,
                Doc::text(" => "),
                print_out_module_type_doc(current),
            ]))
        }
        OutModuleType::Omty_signature(items) if items.is_empty() => Doc::nil(),
        OutModuleType::Omty_signature(items) => Doc::breakable_group(
            Doc::concat(vec![
                Doc::lbrace(),
                Doc::indent(Doc::concat(vec![
                    Doc::line(),
                    print_out_signature_doc(items),
                ])),
                Doc::soft_line(),
                Doc::rbrace(),
            ]),
            true,
        ),
        OutModuleType::Omty_alias(_) => Doc::nil(),
    }
}

/// `print_out_signature_doc` (res_outcome_printer.ml:715-751).
pub(crate) fn print_out_signature_doc(items: &[OutSigItem]) -> Doc {
    let mut docs = Vec::new();
    let mut index = 0;
    while index < items.len() {
        match &items[index] {
            OutSigItem::Osig_typext(ext, OutExtStatus::Oext_first) => {
                // Gather together the extension constructors.
                let mut constructors = vec![(
                    ext.name.clone(),
                    ext.args.clone(),
                    ext.ret_type.clone(),
                    ext.repr.clone(),
                )];
                index += 1;
                while let Some(OutSigItem::Osig_typext(next, OutExtStatus::Oext_next)) =
                    items.get(index)
                {
                    constructors.push((
                        next.name.clone(),
                        next.args.clone(),
                        next.ret_type.clone(),
                        next.repr.clone(),
                    ));
                    index += 1;
                }
                docs.push(print_out_type_extension_doc(
                    &ext.type_name,
                    &ext.type_params,
                    &constructors,
                    ext.private,
                ));
            }
            item => {
                docs.push(print_out_sig_item_doc(item));
                index += 1;
            }
        }
    }
    if docs.len() == 1 {
        docs.pop().expect("one doc")
    } else {
        Doc::breakable_group(Doc::join(Doc::line(), docs), true)
    }
}

fn print_extension_type_params_doc(params: &[String]) -> Doc {
    print_type_params_doc(
        params
            .iter()
            .map(|ty| {
                Doc::text(if ty == "_" {
                    ty.clone()
                } else {
                    format!("'{ty}")
                })
            })
            .collect(),
        false,
    )
}

/// `print_out_extension_constructor_doc` (res_outcome_printer.ml:753-794).
fn print_out_extension_constructor_doc(ext: &OutExtensionConstructor) -> Doc {
    Doc::group(Doc::concat(vec![
        Doc::text("type "),
        print_ident_like(&ext.type_name, false, false),
        print_extension_type_params_doc(&ext.type_params),
        Doc::text(" +="),
        Doc::line(),
        if ext.private {
            Doc::text("private ")
        } else {
            Doc::nil()
        },
        print_out_constructor_doc(&(
            ext.name.clone(),
            ext.args.clone(),
            ext.ret_type.clone(),
            ext.repr.clone(),
        )),
    ]))
}

/// `print_out_type_extension_doc` (res_outcome_printer.ml:796-833).
fn print_out_type_extension_doc(
    name: &str,
    params: &[String],
    constructors: &[OutConstructor],
    private: bool,
) -> Doc {
    Doc::group(Doc::concat(vec![
        Doc::text("type "),
        print_ident_like(name, false, false),
        print_extension_type_params_doc(params),
        Doc::text(" += "),
        if private {
            Doc::text("private ")
        } else {
            Doc::nil()
        },
        print_out_constructors_doc(constructors),
    ]))
}

/// `print_out_sig_item`: the doc rendered at width 80.
pub(crate) fn print_out_sig_item(item: &OutSigItem) -> String {
    print_out_sig_item_doc(item).to_string(80)
}

/// `print_out_module_type`: the doc rendered at width 80.
pub(crate) fn print_out_module_type(mty: &OutModuleType) -> String {
    print_out_module_type_doc(mty).to_string(80)
}

/// `print_out_type`: the doc rendered at width 80.
pub(crate) fn print_out_type(out_type: &OutType) -> String {
    print_out_type_doc(out_type).to_string(80)
}

/// `pp_doc` (res_outcome_printer.ml:426-440): print a doc rendered at width
/// 80 into a Format box. Each line break of a multi-line doc is a newline of
/// the enclosing box, so the following lines are indented with the box, and
/// the first line claims the whole margin, so the box breaks around the doc
/// instead of continuing on the doc's last line.
pub(crate) fn pp_doc<W: std::io::Write>(ppf: &mut Formatter<W>, rendered: &str) {
    if !rendered.contains('\n') {
        ppf.string_as(rendered.len(), rendered);
        return;
    }
    for (index, line) in rendered.split('\n').enumerate() {
        if index == 0 {
            let margin = ppf.margin();
            ppf.string_as(margin, line);
        } else {
            ppf.newline();
            ppf.string_as(line.len(), line);
        }
    }
}

// ============================================================================
// Unification errors (compiler/ml/printtyp.ml:1219-1567)
// ============================================================================

use crate::parser::formatter::{BoxKind, Formatter};

/// `Misc.Color` style escapes for the semantic tags used in reports.
pub(crate) const TAG_ERROR: &str = "\x1b[1;31m";
pub(crate) const TAG_INFO: &str = "\x1b[1;33m";
pub(crate) const TAG_DIM: &str = "\x1b[2m";
pub(crate) const TAG_RESET: &str = "\x1b[0m";

/// An expanded trace entry: a type and its `full_expand`.
pub(crate) type TracePair = (TypeExprRef, TypeExprRef);

/// `Ctype.expand_trace` (ctype.ml:1601-1605) over Rust's raw unification
/// trace: every `(t1, t2)` level becomes `(t1, full_expand t1)` and
/// `(t2, full_expand t2)`, using the expansions recorded when the
/// unification failed.
pub(crate) fn expand_trace(
    ctx: &TypeContext,
    trace: &[(TypeExprRef, TypeExprRef)],
) -> Vec<TracePair> {
    let mut out = Vec::with_capacity(trace.len() * 2);
    for &(t1, t2) in trace {
        for t in [t1, t2] {
            let t = ctx.repr(t);
            let expanded = ctx.trace_expansion(t).unwrap_or(t);
            out.push((t, expanded));
        }
    }
    out
}


fn open_tag<W: std::io::Write>(ppf: &mut Formatter<W>, tag: &str) {
    ppf.string_as(0, tag);
}

fn close_tag<W: std::io::Write>(ppf: &mut Formatter<W>) {
    ppf.string_as(0, TAG_RESET);
}

impl<'a> Printtyp<'a> {
    fn is_tvar(&self, t: TypeExprRef) -> bool {
        matches!(&*self.ctx.borrow_desc(self.ctx.repr(t)), TypeDesc::Tvar(..))
    }

    /// `same_path` (printtyp.ml:1187-1204); `best_type_path` is `(p, Id)`.
    /// A module alias names the same type as its target, so both paths are
    /// compared after `Env.normalize_path None !printing_env`.
    pub(crate) fn same_path(&self, t: TypeExprRef, t2: TypeExprRef) -> bool {
        let t = self.ctx.repr(t);
        let t2 = self.ctx.repr(t2);
        if t == t2 {
            return true;
        }
        match (&*self.ctx.borrow_desc(t), &*self.ctx.borrow_desc(t2)) {
            (
                TypeDesc::Tconstr {
                    path: p1,
                    args: tl1,
                    ..
                },
                TypeDesc::Tconstr {
                    path: p2,
                    args: tl2,
                    ..
                },
            ) => {
                self.normalized_paths_same(p1, p2)
                    && tl1.len() == tl2.len()
                    && tl1
                        .iter()
                        .zip(tl2.iter())
                        .all(|(a, b)| self.ctx.repr(*a) == self.ctx.repr(*b))
            }
            _ => false,
        }
    }

    /// `Path.same (Env.normalize_path None env p1) (Env.normalize_path None
    /// env p2)` with `env = !printing_env` (printtyp.ml:1196-1201). The
    /// normalization runs through Env's `find_module ~alias:true`, forcing
    /// what it reaches, as in OCaml.
    fn normalized_paths_same(&self, p1: &Path, p2: &Path) -> bool {
        let empty;
        let env = match &self.printing_env {
            Some(env) => env,
            None => {
                empty = crate::types::env::Env::empty();
                &empty
            }
        };
        // OCaml evaluates the arguments of `Path.same` right to left, so
        // `p2` is normalized, and what it reaches forced, before `p1`.
        let n2 = crate::types::ctype::force_normalize_path_full_side_effects(self.ctx, env, p2);
        let n1 = crate::types::ctype::force_normalize_path_full_side_effects(self.ctx, env, p1);
        n1.same(&n2)
    }

    fn path_same_name(&mut self, p1: &Path, p2: &Path) {
        match (p1, p2) {
            (Path::Pident(id1), Path::Pident(id2)) => {
                if id1.name() == id2.name() && !id1.same(id2) {
                    self.add_unique(id1);
                    self.add_unique(id2);
                }
            }
            (Path::Pdot(p1, s1, _), Path::Pdot(p2, s2, _)) if s1 == s2 => {
                self.path_same_name(p1, p2)
            }
            (Path::Papply(p1, p1b), Path::Papply(p2, p2b)) => {
                self.path_same_name(p1, p2);
                self.path_same_name(p1b, p2b);
            }
            _ => {}
        }
    }

    fn type_same_name(&mut self, t1: TypeExprRef, t2: TypeExprRef) {
        let paths = match (
            &*self.ctx.borrow_desc(self.ctx.repr(t1)),
            &*self.ctx.borrow_desc(self.ctx.repr(t2)),
        ) {
            (TypeDesc::Tconstr { path: p1, .. }, TypeDesc::Tconstr { path: p2, .. }) => {
                Some((p1.clone(), p2.clone()))
            }
            _ => None,
        };
        if let Some((p1, p2)) = paths {
            self.path_same_name(&p1, &p2);
        }
    }

    /// `trace_same_names`.
    fn trace_same_names(&mut self, tr: &[TracePair]) {
        for pair in tr.chunks(2) {
            if let [(t1, t1e), (t2, t2e)] = pair {
                self.type_same_name(*t1, *t2);
                self.type_same_name(*t1e, *t2e);
            }
        }
    }

    /// `hide_variant_name`: force printing the expanded row.
    fn hide_variant_name(&self, t: TypeExprRef) -> TypeExprRef {
        let t = self.ctx.repr(t);
        let row = match &*self.ctx.borrow_desc(t) {
            TypeDesc::Tvariant(row) => btype::row_repr(self.ctx, row),
            _ => return t,
        };
        if row.row_name.is_none() {
            return t;
        }
        let more_level = self.ctx.get_level(btype::row_more(self.ctx, &row));
        let row_more = self.ctx.alloc_type_at_level(
            TypeDesc::Tvar(None, crate::types::type_expr::VarDescBlock::OWN),
            more_level,
        );
        let level = self.ctx.get_level(t);
        self.ctx.alloc_type_at_level(
            TypeDesc::Tvariant(Box::new(RowDesc {
                row_name: None,
                row_more,
                ..row
            })),
            level,
        )
    }

    /// `Ctype.unalias` (ctype.ml:3941-3950).
    fn unalias(&self, ty: TypeExprRef) -> TypeExprRef {
        let ty = self.ctx.repr(ty);
        let level = self.ctx.get_level(ty);
        let desc = (*self.ctx.get_desc(ty)).clone();
        match desc {
            TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) => ty,
            TypeDesc::Tvariant(row) => {
                let row = btype::row_repr(self.ctx, &row);
                let more = self.ctx.repr(row.row_more);
                let more_desc = (*self.ctx.get_desc(more)).clone();
                let row_more = self
                    .ctx
                    .alloc_type_at_level(more_desc, self.ctx.get_level(more));
                self.ctx.alloc_type_at_level(
                    TypeDesc::Tvariant(Box::new(RowDesc { row_more, ..row })),
                    level,
                )
            }
            TypeDesc::Tobject { fields } => {
                // `newty2 ty.level` reads the shadowed `ty`: the fields' level.
                let fields = self.ctx.repr(fields);
                let fields_level = self.ctx.get_level(fields);
                let fields = self.unalias_object(fields);
                self.ctx
                    .alloc_type_at_level(TypeDesc::Tobject { fields }, fields_level)
            }
            desc => self.ctx.alloc_type_at_level(desc, level),
        }
    }

    fn unalias_object(&self, ty: TypeExprRef) -> TypeExprRef {
        let ty = self.ctx.repr(ty);
        let level = self.ctx.get_level(ty);
        let desc = (*self.ctx.get_desc(ty)).clone();
        match desc {
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                let rest = self.unalias_object(rest);
                self.ctx.alloc_type_at_level(
                    TypeDesc::Tfield {
                        name,
                        mutability,
                        typ,
                        rest,
                    },
                    level,
                )
            }
            desc @ (TypeDesc::Tvar(..) | TypeDesc::Tnil) => {
                self.ctx.alloc_type_at_level(desc, level)
            }
            TypeDesc::Tunivar(..) => ty,
            _ => self.ctx.alloc_type_at_level(
                TypeDesc::Tvar(None, crate::types::type_expr::VarDescBlock::OWN),
                level,
            ),
        }
    }

    /// `Btype.is_constr_row ~allow_ident`.
    fn is_constr_row(&self, allow_ident: bool, t: TypeExprRef) -> bool {
        let is_row_name = |s: &str| s.len() >= 4 && s.ends_with("#row");
        match &*self.ctx.borrow_desc(self.ctx.repr(t)) {
            TypeDesc::Tconstr {
                path: Path::Pident(id),
                ..
            } if allow_ident => is_row_name(id.name()),
            TypeDesc::Tconstr {
                path: Path::Pdot(_, s, _),
                ..
            } => is_row_name(s),
            _ => false,
        }
    }

    /// `filter_trace keep_last`.
    fn filter_trace(&self, keep_last: bool, tr: &[TracePair]) -> Vec<TracePair> {
        match tr {
            [(_, t1e), (_, t2e)] if self.is_tvar(*t1e) || self.is_tvar(*t2e) => Vec::new(),
            [(t1, t1e), (t2, t2e), rem @ ..] => {
                let rem2 = self.filter_trace(keep_last, rem);
                if self.is_constr_row(true, *t1e)
                    || self.is_constr_row(true, *t2e)
                    || (self.same_path(*t1, *t1e)
                        && self.same_path(*t2, *t2e)
                        && !(keep_last && rem2.is_empty()))
                {
                    rem2
                } else {
                    let mut out = vec![(*t1, *t1e), (*t2, *t2e)];
                    out.extend(rem2);
                    out
                }
            }
            _ => Vec::new(),
        }
    }

    /// `has_explanation`.
    fn has_explanation(&self, t3: TypeExprRef, t4: TypeExprRef) -> bool {
        let d3 = self.ctx.get_desc(self.ctx.repr(t3));
        let d4 = self.ctx.get_desc(self.ctx.repr(t4));
        match (&*d3, &*d4) {
            (TypeDesc::Tfield { .. }, TypeDesc::Tnil | TypeDesc::Tconstr { .. })
            | (TypeDesc::Tnil | TypeDesc::Tconstr { .. }, TypeDesc::Tfield { .. })
            | (TypeDesc::Tnil, TypeDesc::Tconstr { .. })
            | (TypeDesc::Tconstr { .. }, TypeDesc::Tnil)
            | (_, TypeDesc::Tvar(..))
            | (TypeDesc::Tvar(..), _)
            | (TypeDesc::Tvariant(_), TypeDesc::Tvariant(_)) => true,
            (
                TypeDesc::Tfield {
                    name: l, rest: r1, ..
                },
                TypeDesc::Tfield {
                    name: l2, rest: r2, ..
                },
            ) => {
                matches!(&*self.ctx.borrow_desc(self.ctx.repr(*r1)), TypeDesc::Tnil)
                    && matches!(&*self.ctx.borrow_desc(self.ctx.repr(*r2)), TypeDesc::Tnil)
                    && l == l2
            }
            _ => false,
        }
    }

    /// `mismatch`.
    fn mismatch(&self, tr: &[TracePair]) -> Option<(TypeExprRef, TypeExprRef)> {
        match tr {
            [(_, t), (_, t2), rem @ ..] => match self.mismatch(rem) {
                Some(m) => Some(m),
                None => self.has_explanation(*t, *t2).then_some((*t, *t2)),
            },
            _ => None,
        }
    }

    /// `prepare_expansion`.
    fn prepare_expansion(&mut self, (t, t2): TracePair) -> TracePair {
        let t2 = self.hide_variant_name(t2);
        self.mark_loops(t);
        if !self.same_path(t, t2) {
            self.mark_loops(t2);
        }
        (t, t2)
    }

    /// `may_prepare_expansion compact`.
    fn may_prepare_expansion(&mut self, compact: bool, (t, t2): TracePair) -> TracePair {
        let is_row_or_object = matches!(
            &*self.ctx.borrow_desc(self.ctx.repr(t2)),
            TypeDesc::Tvariant(_) | TypeDesc::Tobject { .. }
        );
        if is_row_or_object && compact {
            self.mark_loops(t);
            (t, t)
        } else {
            self.prepare_expansion((t, t2))
        }
    }

    /// `type_expr ppf ty` into a Format stream.
    pub(crate) fn pp_type_expr<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        ty: TypeExprRef,
    ) {
        // `print_out_type` (res_outcome_printer.ml:442).
        let text = self.type_expr(ty);
        pp_doc(ppf, &text);
    }

    /// `super_type_expansion ~tag t ppf t'`.
    fn super_type_expansion<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        tag: &str,
        t: TypeExprRef,
        t2: TypeExprRef,
    ) {
        if self.same_path(t, t2) {
            open_tag(ppf, tag);
            self.pp_type_expr(ppf, t);
            close_tag(ppf);
        } else {
            let t2 = if self.proxy(t) == self.proxy(t2) {
                self.unalias(t2)
            } else {
                t2
            };
            ppf.open_box(BoxKind::Box, 2);
            open_tag(ppf, tag);
            self.pp_type_expr(ppf, t);
            close_tag(ppf);
            ppf.space();
            open_tag(ppf, TAG_DIM);
            ppf.str("(defined as");
            close_tag(ppf);
            ppf.space();
            open_tag(ppf, tag);
            self.pp_type_expr(ppf, t2);
            close_tag(ppf);
            open_tag(ppf, TAG_DIM);
            ppf.str(")");
            close_tag(ppf);
            ppf.close_box();
        }
    }

    /// `super_trace`.
    fn super_trace<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        first: bool,
        tr: &[TracePair],
    ) {
        if let [(t1, t1e), (t2, t2e), rem @ ..] = tr {
            ppf.cut();
            ppf.cut();
            ppf.open_box(BoxKind::V, 2);
            if first {
                ppf.str("The incompatible parts:");
            } else {
                ppf.str("Further expanded:");
            }
            ppf.cut();
            ppf.open_box(BoxKind::HOV, 0);
            self.super_type_expansion(ppf, TAG_ERROR, *t1, *t1e);
            ppf.space();
            ppf.str("vs");
            ppf.space();
            self.super_type_expansion(ppf, TAG_INFO, *t2, *t2e);
            ppf.close_box();
            self.super_trace(ppf, false, rem);
            ppf.close_box();
        }
    }

    fn print_tags<W: std::io::Write>(&self, ppf: &mut Formatter<W>, fields: &[(String, RowField)]) {
        for (i, (t, _)) in fields.iter().enumerate() {
            if i > 0 {
                ppf.str(",");
                ppf.space();
            }
            ppf.str(&polyvar_ident_to_string(t));
        }
    }

    /// `explanation unif t3 t4` (printtyp.ml:1328-1437).
    fn explanation<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        unif: bool,
        t3: TypeExprRef,
        t4: TypeExprRef,
    ) {
        let t3 = self.ctx.repr(t3);
        let t4 = self.ctx.repr(t4);
        let d3 = (*self.ctx.get_desc(t3)).clone();
        let d4 = (*self.ctx.get_desc(t4)).clone();
        let binding_time = |p: &Path| p.binding_time();
        match (&d3, &d4) {
            (TypeDesc::Ttuple(l), TypeDesc::Tvar(..))
            | (TypeDesc::Tvar(..), TypeDesc::Ttuple(l))
                if l.is_empty() =>
            {
                ppf.cut();
                ppf.str("Self type cannot escape its class");
            }
            (TypeDesc::Tconstr { path: p, .. }, TypeDesc::Tvar(..))
                if unif && self.ctx.get_level(t4) < binding_time(p) =>
            {
                self.escape_scope(ppf, p);
            }
            (TypeDesc::Tvar(..), TypeDesc::Tconstr { path: p, .. })
                if unif && self.ctx.get_level(t3) < binding_time(p) =>
            {
                self.escape_scope(ppf, p);
            }
            (TypeDesc::Tvar(..), TypeDesc::Tunivar(..))
            | (TypeDesc::Tunivar(..), TypeDesc::Tvar(..)) => {
                ppf.cut();
                ppf.str("The universal variable ");
                let u = if matches!(d3, TypeDesc::Tunivar(..)) {
                    t3
                } else {
                    t4
                };
                self.pp_type_expr(ppf, u);
                ppf.str(" would escape its scope");
            }
            (TypeDesc::Tvar(..), _) | (_, TypeDesc::Tvar(..)) => {
                let (t, t2) = if matches!(d3, TypeDesc::Tvar(..)) {
                    (t3, t4)
                } else {
                    (t4, t3)
                };
                let occurs = crate::types::ctype::occur_check(
                    self.ctx,
                    None,
                    crate::types::ctype::UnifyMode::Expression,
                    t,
                    t2,
                )
                .is_err();
                ppf.cut();
                ppf.open_box(BoxKind::HOV, 0);
                if occurs {
                    ppf.str("The type variable ");
                    self.pp_type_expr(ppf, t);
                    ppf.str(" occurs inside");
                    ppf.space();
                    self.pp_type_expr(ppf, t2);
                } else {
                    ppf.str("This instance of ");
                    self.pp_type_expr(ppf, t2);
                    ppf.str(" is ambiguous:");
                    ppf.space();
                    ppf.str("it would escape the scope of its equation");
                }
                ppf.close_box();
            }
            (TypeDesc::Tfield { name, .. }, _) | (_, TypeDesc::Tfield { name, .. })
                if name == "*dummy method*" =>
            {
                ppf.cut();
                ppf.str("Self type cannot be unified with a closed object type");
            }
            (
                TypeDesc::Tfield {
                    name: l,
                    typ: f1,
                    rest: r1,
                    ..
                },
                TypeDesc::Tfield {
                    name: l2,
                    typ: f2,
                    rest: r2,
                    ..
                },
            ) if l == l2
                && matches!(&*self.ctx.borrow_desc(self.ctx.repr(*r1)), TypeDesc::Tnil)
                && matches!(&*self.ctx.borrow_desc(self.ctx.repr(*r2)), TypeDesc::Tnil) =>
            {
                ppf.cut();
                ppf.cut();
                ppf.str("Types for field ");
                open_tag(ppf, TAG_INFO);
                ppf.print(format_args!("\"{l}\""));
                close_tag(ppf);
                ppf.str(" are incompatible:");
                ppf.cut();
                ppf.str("Field ");
                open_tag(ppf, TAG_INFO);
                ppf.print(format_args!("\"{l}\""));
                close_tag(ppf);
                ppf.str(" in the passed object has type ");
                open_tag(ppf, TAG_ERROR);
                self.pp_type_expr(ppf, *f1);
                close_tag(ppf);
                ppf.str(", but is expected to have type ");
                open_tag(ppf, TAG_INFO);
                self.pp_type_expr(ppf, *f2);
                close_tag(ppf);
                ppf.str(".");
            }
            (
                TypeDesc::Tnil | TypeDesc::Tconstr { .. },
                TypeDesc::Tfield {
                    name: l, typ: f1, ..
                },
            ) => {
                ppf.cut();
                ppf.cut();
                ppf.open_box(BoxKind::Box, 0);
                ppf.str("The first object is expected to have a field ");
                open_tag(ppf, TAG_INFO);
                ppf.print(format_args!("\"{l}\""));
                close_tag(ppf);
                ppf.str(" of type ");
                open_tag(ppf, TAG_INFO);
                self.pp_type_expr(ppf, *f1);
                close_tag(ppf);
                ppf.str(", but it does not.");
                ppf.close_box();
            }
            (
                TypeDesc::Tfield {
                    name: l, typ: f1, ..
                },
                TypeDesc::Tnil | TypeDesc::Tconstr { .. },
            ) => {
                ppf.cut();
                ppf.cut();
                ppf.open_box(BoxKind::Box, 0);
                ppf.str("The second object is expected to have a field ");
                open_tag(ppf, TAG_INFO);
                ppf.print(format_args!("\"{l}\""));
                close_tag(ppf);
                ppf.str(" of type ");
                open_tag(ppf, TAG_INFO);
                self.pp_type_expr(ppf, *f1);
                close_tag(ppf);
                ppf.str(", but it does not.");
                ppf.close_box();
            }
            (TypeDesc::Tnil, TypeDesc::Tconstr { .. })
            | (TypeDesc::Tconstr { .. }, TypeDesc::Tnil) => {
                ppf.cut();
                ppf.open_box(BoxKind::Box, 0);
                ppf.print(format_args!(
                    "The {} object type has an abstract row, it cannot be closed",
                    if matches!(d4, TypeDesc::Tnil) {
                        "first"
                    } else {
                        "second"
                    }
                ));
                ppf.close_box();
            }
            (TypeDesc::Tvariant(row1), TypeDesc::Tvariant(row2)) => {
                let row1 = btype::row_repr(self.ctx, row1);
                let row2 = btype::row_repr(self.ctx, row2);
                let f1: Vec<(String, RowField)> = row1
                    .row_fields
                    .iter()
                    .map(|(l, f)| (l.to_string(), f.clone()))
                    .collect();
                let f2: Vec<(String, RowField)> = row2
                    .row_fields
                    .iter()
                    .map(|(l, f)| (l.to_string(), f.clone()))
                    .collect();
                match (
                    f1.as_slice(),
                    row1.row_closed,
                    f2.as_slice(),
                    row2.row_closed,
                ) {
                    ([], true, [], true) => {
                        ppf.cut();
                        ppf.cut();
                        ppf.str(
                            "These polymorphic variants are incompatible - they share no common constructors.",
                        );
                    }
                    ([], true, fields, _) if !fields.is_empty() => {
                        self.closed_variant_explanation(ppf, "first", fields);
                    }
                    (fields, _, [], true) if !fields.is_empty() => {
                        self.closed_variant_explanation(ppf, "second", fields);
                    }
                    ([(l1, _)], true, [(l2, _)], true) if l1 == l2 => {
                        let name = polyvar_ident_to_string(l1);
                        ppf.cut();
                        ppf.cut();
                        ppf.str("Both polymorphic variants have the constructor ");
                        open_tag(ppf, TAG_INFO);
                        ppf.str(&name);
                        close_tag(ppf);
                        ppf.str(", but their payload types are incompatible.");
                        ppf.cut();
                        ppf.str("Make sure the payload types for ");
                        open_tag(ppf, TAG_INFO);
                        ppf.str(&name);
                        close_tag(ppf);
                        ppf.str(" match exactly in both polymorphic variants.");
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn escape_scope<W: std::io::Write>(&mut self, ppf: &mut Formatter<W>, p: &Path) {
        ppf.cut();
        ppf.open_box(BoxKind::Box, 0);
        ppf.str("The type constructor");
        ppf.break_(1, 2);
        let text = self.path_text(p);
        ppf.str(&text);
        ppf.space();
        ppf.str("would escape its scope");
        ppf.close_box();
    }

    fn closed_variant_explanation<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        which: &str,
        fields: &[(String, RowField)],
    ) {
        let constructors_txt = if fields.len() == 1 {
            "constructor"
        } else {
            "constructors"
        };
        ppf.cut();
        ppf.cut();
        ppf.print(format_args!("The {which} polymorphic variant is "));
        open_tag(ppf, TAG_INFO);
        ppf.str("closed");
        close_tag(ppf);
        ppf.print(format_args!(
            " and doesn't include the {constructors_txt}: "
        ));
        open_tag(ppf, TAG_ERROR);
        self.print_tags(ppf, fields);
        close_tag(ppf);
        ppf.str(".");
        ppf.cut();
        ppf.cut();
        ppf.str("Possible solutions:\n");
        ppf.print(format_args!("  - Either make the {which} variant "));
        open_tag(ppf, TAG_INFO);
        ppf.str("open");
        close_tag(ppf);
        ppf.str(
            " so it can accept additional constructors. To do this, make sure the type starts with ",
        );
        open_tag(ppf, TAG_INFO);
        ppf.str("[>");
        close_tag(ppf);
        ppf.str(" instead of ");
        open_tag(ppf, TAG_INFO);
        ppf.str("[");
        close_tag(ppf);
        ppf.str("\n");
        ppf.print(format_args!(
            "  - Or add the missing {constructors_txt} to it."
        ));
    }

    /// `Printtyp.path ppf p`.
    pub(crate) fn path_text(&self, p: &Path) -> String {
        match p {
            Path::Pident(id) => self.ident_name(id),
            Path::Pdot(_, s, _) if self.non_shadowed_pervasive_or_stdlib(p) => s.to_string(),
            Path::Pdot(parent, s, _) => format!("{}.{}", self.path_text(parent), s),
            Path::Papply(p1, p2) => format!("{}({})", self.path_text(p1), self.path_text(p2)),
        }
    }

    /// `super_unification_error ?print_extra_info unif tr txt1 ppf txt2`
    /// (printtyp.ml:1542-1562) on an expanded trace.
    pub(crate) fn super_unification_error<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        unif: bool,
        tr: &[TracePair],
        txt1: &mut dyn FnMut(&mut Formatter<W>),
        txt2: &mut dyn FnMut(&mut Formatter<W>),
        print_extra_info: Option<
            &mut dyn FnMut(&mut Formatter<W>, &mut Self, TypeExprRef, TypeExprRef),
        >,
    ) {
        self.reset();
        self.trace_same_names(tr);
        let tr: Vec<TracePair> = tr
            .iter()
            .map(|&(t, t2)| (t, self.hide_variant_name(t2)))
            .collect();
        let mis = self.mismatch(&tr);
        let [first, second, rest @ ..] = tr.as_slice() else {
            return;
        };
        let rest = self.filter_trace(mis.is_none(), rest);
        let compact = rest.is_empty();
        let (t1, t1e) = self.may_prepare_expansion(compact, *first);
        let (t2, t2e) = self.may_prepare_expansion(compact, *second);
        let rest: Vec<TracePair> = rest
            .into_iter()
            .map(|p| self.prepare_expansion(p))
            .collect();
        ppf.open_box(BoxKind::V, 0);
        ppf.open_box(BoxKind::HOV, 2);
        txt1(ppf);
        ppf.space();
        self.super_type_expansion(ppf, TAG_ERROR, t1, t1e);
        ppf.close_box();
        ppf.cut();
        ppf.open_box(BoxKind::HOV, 2);
        txt2(ppf);
        ppf.space();
        self.super_type_expansion(ppf, TAG_INFO, t2, t2e);
        ppf.close_box();
        self.super_trace(ppf, true, &rest);
        if let Some((t3, t4)) = mis {
            self.explanation(ppf, unif, t3, t4);
        }
        if let Some(f) = print_extra_info {
            f(ppf, self, t1, t2);
        }
        ppf.close_box();
    }
}

/// `Res_printer.polyvar_ident_to_string` (`print_res_poly_identifier`).
fn polyvar_ident_to_string(txt: &str) -> String {
    Doc::concat(vec![Doc::text("#"), print_poly_var_ident(txt)]).to_string(80)
}

// ============================================================================
// Subtyping errors (printtyp.ml:1235-1252, 1569-1738)
// ============================================================================

impl<'a> Printtyp<'a> {
    /// `type_expansion t ppf t'` (printtyp.ml:1235-1241).
    fn type_expansion<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        t: TypeExprRef,
        t2: TypeExprRef,
    ) {
        if self.same_path(t, t2) {
            let proxy = self.proxy(t);
            self.add_delayed(proxy);
            self.pp_type_expr(ppf, t);
        } else {
            let t2 = if self.proxy(t) == self.proxy(t2) {
                self.unalias(t2)
            } else {
                t2
            };
            ppf.open_box(BoxKind::Box, 2);
            self.pp_type_expr(ppf, t);
            ppf.space();
            ppf.str("=");
            ppf.space();
            self.pp_type_expr(ppf, t2);
            ppf.close_box();
        }
    }

    /// The inner `trace fst txt ppf` (printtyp.ml:1247-1252).
    fn plain_trace<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        fst: bool,
        txt: &str,
        tr: &[TracePair],
    ) {
        if let [(t1, t1e), (t2, t2e), rem @ ..] = tr {
            if !fst {
                ppf.cut();
            }
            ppf.open_box(BoxKind::Box, 0);
            ppf.str("Type");
            ppf.break_(1, 2);
            self.type_expansion(ppf, *t1, *t1e);
            ppf.space();
            ppf.str(txt);
            ppf.break_(1, 2);
            self.type_expansion(ppf, *t2, *t2e);
            ppf.close_box();
            ppf.str(" ");
            self.plain_trace(ppf, false, txt, rem);
        }
    }

    /// `trace fst keep_last txt ppf tr` (printtyp.ml:1569-1577).
    fn keep_last_trace<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        fst: bool,
        keep_last: bool,
        txt: &str,
        tr: &[TracePair],
    ) {
        self.trace_same_names(tr);
        if let [t1, t2, rest @ ..] = tr {
            if fst {
                let mut kept = vec![*t1, *t2];
                kept.extend(self.filter_trace(keep_last, rest));
                self.plain_trace(ppf, fst, txt, &kept);
            } else {
                let kept = self.filter_trace(keep_last, tr);
                self.plain_trace(ppf, fst, txt, &kept);
            }
        }
    }

    /// `report_subtyping_error ppf env tr1 txt1 tr2 ctx`
    /// (printtyp.ml:1740-1813), after `wrap_printing_env env`.
    pub(crate) fn report_subtyping_error<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        tr1: &[TracePair],
        txt1: &str,
        tr2: &[TracePair],
        context: Option<&crate::types::SubtypeContext>,
    ) {
        self.reset();
        let tr1: Vec<TracePair> = tr1.iter().map(|&p| self.prepare_expansion(p)).collect();
        let tr2: Vec<TracePair> = tr2.iter().map(|&p| self.prepare_expansion(p)).collect();
        ppf.open_box(BoxKind::V, 0);
        self.keep_last_trace(ppf, true, tr2.is_empty(), txt1, &tr1);
        if tr2.is_empty() {
            ppf.close_box();
        } else {
            let mis = self.mismatch(&tr2);
            self.keep_last_trace(
                ppf,
                false,
                mis.is_none(),
                "is not compatible with type",
                &tr2,
            );
            if let Some((t3, t4)) = mis {
                self.explanation(ppf, true, t3, t4);
            }
            ppf.close_box();
        }
        if let Some(context) = context {
            ppf.cut();
            ppf.cut();
            ppf.open_box(BoxKind::V, 2);
            print_subtype_context(ppf, context);
        }
    }
}

fn info<W: std::io::Write>(ppf: &mut Formatter<W>, text: &str) {
    open_tag(ppf, TAG_INFO);
    ppf.str(text);
    close_tag(ppf);
}

fn error_tag<W: std::io::Write>(ppf: &mut Formatter<W>, text: &str) {
    open_tag(ppf, TAG_ERROR);
    ppf.str(text);
    close_tag(ppf);
}

/// `Ast_untagged_variants.tag_type_to_user_visible_string`.
fn as_payload_name(payload: crate::types::ctype::VariantConstructorAsPayload) -> &'static str {
    use crate::types::ctype::VariantConstructorAsPayload as P;
    match payload {
        P::String => "string",
        P::Int => "int",
        P::Float => "float",
        P::BigInt => "bigint",
        P::Bool => "bool",
        P::Null => "null",
        P::Undefined => "undefined",
    }
}

/// The `match ctx with Some ctx -> ...` part of `report_subtyping_error`.
fn print_subtype_context<W: std::io::Write>(
    ppf: &mut Formatter<W>,
    context: &crate::types::SubtypeContext,
) {
    use crate::types::SubtypeContext as C;
    use crate::types::ctype::SubtypeTypeKind as K;
    match context {
        C::Generic { error_code } => {
            ppf.str("Error: ");
            ppf.str(error_code);
        }
        C::CoercionTargetVariantNotUnboxed {
            variant_name,
            primitive,
        } => {
            ppf.space();
            ppf.str("The variant ");
            info(ppf, &variant_name.name());
            ppf.str(" is not unboxed, so it cannot be coerced to a ");
            info(ppf, &primitive.name());
            ppf.str(". ");
            ppf.space();
            ppf.str("Fix this by adding the ");
            info(ppf, "@unboxed");
            ppf.str(" attribute to the variant ");
            info(ppf, &variant_name.name());
            ppf.str(".");
        }
        C::CoercionTargetVariantDoesNotCoverType {
            variant_name,
            primitive,
        } => {
            let variant = variant_name.name();
            let primitive = primitive.name();
            let mut chars = primitive.chars();
            let capitalized = match chars.next() {
                Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            };
            ppf.space();
            ppf.str("The variant ");
            info(ppf, &variant);
            ppf.str(" is unboxed, but has no catch-all case for the primitive ");
            info(ppf, &primitive);
            ppf.str(", and therefore does not cover all values of type ");
            info(ppf, &primitive);
            ppf.str(". ");
            ppf.space();
            ppf.str("Fix this by adding a catch-all for ");
            info(ppf, &variant);
            ppf.str(" to ");
            info(ppf, &primitive);
            ppf.str(", like ");
            info(ppf, &format!("{capitalized}({primitive})"));
            ppf.str(".");
        }
        C::VariantConstructorRuntimeRepresentationMismatch {
            variant_name,
            issues,
        } => {
            for issue in issues {
                ppf.space();
                print_variant_runtime_representation_issue(ppf, variant_name, issue);
            }
        }
        C::VariantConfigurationsMismatch {
            left_variant_name,
            right_variant_name,
            issue,
        } => print_variant_configuration_issue(ppf, issue, left_variant_name, right_variant_name),
        C::DifferentTypeKinds {
            left_typename,
            right_typename,
            left_type_kind,
            right_type_kind,
        } => {
            let kind = |k: &K| match k {
                K::Abstract => "an abstract type",
                K::Record => "a record",
                K::Variant => "a variant",
                K::Open => "an open type",
            };
            ppf.space();
            ppf.str("The types of ");
            info(ppf, &left_typename.name());
            ppf.str(" and ");
            info(ppf, &right_typename.name());
            ppf.str(" are different:");
            ppf.space();
            ppf.str("- ");
            info(ppf, &left_typename.name());
            ppf.str(" is ");
            ppf.str(kind(left_type_kind));
            ppf.space();
            ppf.str("- ");
            info(ppf, &right_typename.name());
            ppf.str(" is ");
            ppf.str(kind(right_type_kind));
        }
        C::RecordFieldsMismatch {
            left_record_name,
            right_record_name,
            issues,
        } => {
            ppf.space();
            ppf.str("The record ");
            info(ppf, &left_record_name.name());
            ppf.str(" cannot be coerced to the record ");
            info(ppf, &right_record_name.name());
            ppf.str(" because:");
            for issue in issues {
                ppf.space();
                ppf.str("- ");
                print_record_field_subtype_violation(
                    ppf,
                    issue,
                    left_record_name,
                    right_record_name,
                );
            }
        }
        C::CoercionIntoPrivateType { typename } => {
            ppf.space();
            info(ppf, &typename.name());
            ppf.str(
                " is private: its values can only be built in the module that defines it, so another type cannot be coerced to it.",
            );
        }
    }
}

/// `print_variant_runtime_representation_issue` (printtyp.ml:1579-1628).
fn print_variant_runtime_representation_issue<W: std::io::Write>(
    ppf: &mut Formatter<W>,
    variant_name: &Path,
    issue: &crate::types::ctype::VariantRuntimeRepresentationIssue,
) {
    use crate::types::ctype::VariantRuntimeRepresentationIssue as I;
    let variant = variant_name.name();
    match issue {
        I::CannotCoerceNonUnboxedWithPayload {
            constructor_name,
            expected_typename,
        } => {
            ppf.str("The constructor ");
            info(ppf, constructor_name);
            ppf.str(" of variant ");
            info(ppf, &variant);
            ppf.str(" has a payload, but the variant itself is not unboxed. ");
            ppf.space();
            ppf.str("This means that the constructor ");
            info(ppf, constructor_name);
            ppf.str(" will be encoded as an object at runtime, which is not compatible with ");
            info(ppf, &expected_typename.name());
            ppf.str(".");
        }
        I::InlineRecordCannotBeCoerced { constructor_name } => {
            ppf.str("The constructor ");
            info(ppf, constructor_name);
            ppf.str(" of variant ");
            info(ppf, &variant);
            ppf.str(
                " has an inline record as payload. Currently, inline records cannot be coerced.",
            );
        }
        I::AsPayloadNotEligibleForCoercion {
            constructor_name,
            as_payload,
            expected_typename,
        } => {
            ppf.str("The constructor ");
            info(ppf, constructor_name);
            ppf.str(" of variant ");
            info(ppf, &variant);
            ppf.str(" has an ");
            info(ppf, "@as");
            ppf.str(" payload that has a runtime representation of ");
            info(ppf, as_payload_name(*as_payload));
            ppf.str(", which is not compatible with the expected ");
            info(ppf, &expected_typename.name());
            ppf.str(".");
        }
        I::MismatchedUnboxedPayload { .. } => {}
        I::MismatchedAsPayload {
            constructor_name,
            expected_typename,
            as_payload,
        } => {
            ppf.str("The constructor ");
            info(ppf, constructor_name);
            ppf.str(" of variant ");
            info(ppf, &variant);
            ppf.str(" has ");
            match as_payload {
                None => {
                    ppf.str("no ");
                    info(ppf, "@as");
                    ppf.str(" payload, which makes it a ");
                    info(ppf, "string");
                    ppf.str(" at runtime.");
                }
                Some(payload) => {
                    ppf.str("an ");
                    info(ppf, "@as");
                    ppf.str(" payload that gives it the runtime type of ");
                    info(ppf, as_payload_name(*payload));
                    ppf.str(".");
                }
            }
            ppf.space();
            ppf.str("That runtime representation is not compatible with the expected runtime representation of ");
            info(ppf, &expected_typename.name());
            ppf.str(".");
            ppf.cut();
            ppf.space();
            ppf.str("Fix this by making sure all constructors in variant ");
            info(ppf, &variant);
            ppf.str(" has a runtime representation of ");
            info(ppf, &expected_typename.name());
            ppf.str(".");
        }
    }
}

/// `print_variant_configuration_issue` (printtyp.ml:1630-1698).
fn print_variant_configuration_issue<W: std::io::Write>(
    ppf: &mut Formatter<W>,
    issue: &crate::types::ctype::VariantConfigurationIssue,
    left_variant_name: &Path,
    right_variant_name: &Path,
) {
    use crate::types::ctype::VariantConfigurationIssue as I;
    match issue {
        I::UnboxedConfigNotMatching {
            left_unboxed,
            right_unboxed,
        } => {
            ppf.space();
            ppf.str("The variants have different ");
            info(ppf, "@unboxed");
            ppf.str(" configurations.");
            for (unboxed, name) in [
                (*left_unboxed, left_variant_name),
                (*right_unboxed, right_variant_name),
            ] {
                ppf.space();
                ppf.str("- Variant ");
                info(ppf, &name.name());
                ppf.str(" is ");
                error_tag(ppf, if unboxed { "" } else { "not " });
                ppf.str("unboxed.");
            }
            ppf.cut();
            ppf.space();
            ppf.str("Fix this by making sure the variants either both have, or don't have, the ");
            info(ppf, "@unboxed");
            ppf.str(" attribute.");
        }
        I::TagNameNotMatching {
            left_tag,
            right_tag,
        } => {
            ppf.space();
            ppf.str("The variants have different ");
            info(ppf, "@tag");
            ppf.str(" configurations.");
            for (tag, name) in [
                (left_tag, left_variant_name),
                (right_tag, right_variant_name),
            ] {
                ppf.space();
                match tag {
                    Some(tag) => {
                        ppf.str("- ");
                        info(ppf, &name.name());
                        ppf.str(" has tag ");
                        info(ppf, tag);
                        ppf.str(".");
                    }
                    None => {
                        ppf.str("- ");
                        info(ppf, &name.name());
                        ppf.str(" has no explicit tag.");
                    }
                }
            }
            ppf.cut();
            ppf.space();
            ppf.str("Fix this by making sure the variants either have the exact same ");
            info(ppf, "@tag");
            ppf.str(" configuration, or no ");
            info(ppf, "@tag");
            ppf.str(" at all.");
        }
        I::IncompatibleConstructorCount { constructor_names } => {
            let total = constructor_names.len();
            let printed = &constructor_names[..total.min(3)];
            let not_printed = total - printed.len();
            ppf.space();
            info(ppf, &left_variant_name.name());
            ppf.str(&format!(
                " has {total} constructor{} that ",
                if total == 1 { "" } else { "s" }
            ));
            info(ppf, &right_variant_name.name());
            ppf.str(" does not have: ");
            for (index, name) in printed.iter().enumerate() {
                if index > 0 {
                    ppf.str(", ");
                }
                info(ppf, name);
            }
            if not_printed > 0 {
                ppf.str(&format!(" (+{not_printed} more)"));
            }
            ppf.space();
            ppf.str("Therefore, it is not possible for ");
            info(ppf, &right_variant_name.name());
            ppf.str(" to represent ");
            info(ppf, &left_variant_name.name());
            ppf.str(".");
        }
    }
}

/// `print_record_field_subtype_violation` (printtyp.ml:1666-1716).
fn print_record_field_subtype_violation<W: std::io::Write>(
    ppf: &mut Formatter<W>,
    issue: &crate::types::ctype::RecordFieldSubtypeViolation,
    left_record_name: &Path,
    right_record_name: &Path,
) {
    use crate::types::ctype::RecordFieldSubtypeViolation as V;
    match issue {
        V::OptionalMismatch {
            label,
            left_optional,
            right_optional,
        } => {
            ppf.str("The field ");
            info(ppf, label);
            ppf.str(" ");
            match (left_optional, right_optional) {
                (true, false) => {
                    ppf.str("is optional in record ");
                    info(ppf, &left_record_name.name());
                    ppf.str(", but is not optional in record ");
                    info(ppf, &right_record_name.name());
                }
                (false, true) => {
                    ppf.str("is not optional in record ");
                    info(ppf, &left_record_name.name());
                    ppf.str(", but is optional in record ");
                    info(ppf, &right_record_name.name());
                }
                _ => {}
            }
        }
        V::FieldRuntimeNameMismatch {
            label,
            left_as,
            right_as,
        } => {
            ppf.str("Field ");
            info(ppf, label);
            ppf.str(" runtime representation");
            match left_as {
                Some(as_name) => {
                    ppf.str(" is configured to be ");
                    info(ppf, &format!("\"{as_name}\""));
                    ppf.str(" (via the @as attribute)");
                }
                None => {
                    ppf.str(" is ");
                    info(ppf, &format!("\"{label}\""));
                }
            }
            ppf.str(" in record ");
            info(ppf, &right_record_name.name());
            ppf.str(", but in record ");
            info(ppf, &left_record_name.name());
            match right_as {
                Some(as_name) => {
                    ppf.str(" it is configured to be ");
                    info(ppf, &format!("\"{as_name}\""));
                    ppf.str(" (via the @as attribute).");
                }
                None => {
                    ppf.str(" it is ");
                    info(ppf, &format!("\"{label}\""));
                    ppf.str(".");
                }
            }
            ppf.str(" Runtime representations must match.");
        }
        V::FieldMissing { label } => {
            ppf.str("The field ");
            info(ppf, label);
            ppf.str(" is missing in record ");
            info(ppf, &right_record_name.name());
            ppf.str(", but present in record ");
            info(ppf, &left_record_name.name());
        }
        V::MutableMismatch { label } => {
            ppf.str("The field ");
            info(ppf, label);
            ppf.str(" is mutable in record ");
            info(ppf, &right_record_name.name());
            ppf.str(", but not in record ");
            info(ppf, &left_record_name.name());
            ppf.str(". A coercion can't make a field writable.");
        }
    }
}

impl<'a> Printtyp<'a> {
    /// `unification_error env unif tr txt1 ppf txt2` (printtyp.ml:1480-1500),
    /// the reporter of `Printtyp.report_unification_error`. The
    /// `warn_on_missing_def` hints are printed only for a non-empty env, which
    /// no Rust caller passes.
    pub(crate) fn report_unification_error<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        unif: bool,
        tr: &[TracePair],
        txt1: &mut dyn FnMut(&mut Formatter<W>),
        txt2: &mut dyn FnMut(&mut Formatter<W>),
    ) {
        self.reset();
        self.trace_same_names(tr);
        let tr: Vec<TracePair> = tr
            .iter()
            .map(|&(t, t2)| (t, self.hide_variant_name(t2)))
            .collect();
        let mis = self.mismatch(&tr);
        let [first, second, rest @ ..] = tr.as_slice() else {
            return;
        };
        let rest = self.filter_trace(mis.is_none(), rest);
        let compact = rest.is_empty();
        let (t1, t1e) = self.may_prepare_expansion(compact, *first);
        let (t2, t2e) = self.may_prepare_expansion(compact, *second);
        let rest: Vec<TracePair> = rest
            .into_iter()
            .map(|p| self.prepare_expansion(p))
            .collect();
        ppf.open_box(BoxKind::V, 0);
        ppf.open_box(BoxKind::Box, 0);
        txt1(ppf);
        ppf.break_(1, 2);
        self.type_expansion(ppf, t1, t1e);
        ppf.space();
        txt2(ppf);
        ppf.break_(1, 2);
        self.type_expansion(ppf, t2, t2e);
        ppf.close_box();
        self.plain_trace(ppf, false, "is not compatible with type", &rest);
        if let Some((t3, t4)) = mis {
            self.explanation(ppf, unif, t3, t4);
        }
        ppf.close_box();
    }
}

impl<'a> Printtyp<'a> {
    /// `type_path_expansion tp ppf tp'` (printtyp.ml:1243-1245).
    fn type_path_expansion<W: std::io::Write>(
        &self,
        ppf: &mut Formatter<W>,
        tp: &Path,
        tp2: &Path,
    ) {
        if tp.same(tp2) {
            ppf.str(&self.path_text(tp));
        } else {
            ppf.open_box(BoxKind::Box, 2);
            ppf.str(&self.path_text(tp));
            ppf.space();
            ppf.str("=");
            ppf.space();
            ppf.str(&self.path_text(tp2));
            ppf.close_box();
        }
    }

    /// `report_ambiguous_type_error ppf env (tp0, tp0') tpl txt1 txt2 txt3`
    /// (printtyp.ml:1805-1822), after `wrap_printing_env env`.
    pub(crate) fn report_ambiguous_type_error<W: std::io::Write>(
        &mut self,
        ppf: &mut Formatter<W>,
        tp0: &(Path, Path),
        tpl: &[(Path, Path)],
        txt1: &mut dyn FnMut(&mut Formatter<W>),
        txt2: &mut dyn FnMut(&mut Formatter<W>),
        txt3: &mut dyn FnMut(&mut Formatter<W>),
    ) {
        self.reset();
        for (tp, tp2) in tpl {
            self.path_same_name(&tp0.0, tp);
            self.path_same_name(&tp0.1, tp2);
        }
        ppf.open_box(BoxKind::Box, 0);
        match tpl {
            [] => {}
            [(tp, tp2)] => {
                txt1(ppf);
                ppf.break_(1, 2);
                self.type_path_expansion(ppf, tp, tp2);
            }
            _ => {
                txt2(ppf);
                ppf.break_(1, 2);
                ppf.open_box(BoxKind::HV, 0);
                for (index, (tp, tp2)) in tpl.iter().enumerate() {
                    if index > 0 {
                        ppf.break_(2, 0);
                    }
                    self.type_path_expansion(ppf, tp, tp2);
                }
                ppf.close_box();
            }
        }
        ppf.space();
        txt3(ppf);
        ppf.break_(1, 2);
        self.type_path_expansion(ppf, &tp0.0, &tp0.1);
        ppf.close_box();
    }
}

#[cfg(test)]
mod tests {
    use super::pp_doc;
    use crate::parser::formatter::Formatter;

    /// `@[<hv 2>Modules do not match:@ %a@;<1 -2>is not included in@ %a@]`
    /// (includemod.ml:566-569) at column 2, the sides printed by `pp_doc`.
    fn modules_do_not_match(actual: &str, expected: &str) -> String {
        let mut buf = Vec::new();
        {
            let mut ppf = Formatter::new(&mut buf);
            ppf.string_as(2, "");
            ppf.open_hvbox(2);
            ppf.str("Modules do not match:");
            ppf.space();
            pp_doc(&mut ppf, actual);
            ppf.break_(1, -2);
            ppf.str("is not included in");
            ppf.space();
            pp_doc(&mut ppf, expected);
            ppf.close_box();
            ppf.flush();
        }
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn pp_doc_indents_every_line_of_a_multi_line_doc_with_its_box() {
        // The upstream example of bf272baf34.
        assert_eq!(
            modules_do_not_match("{\n  type t = int\n}", "{\n  type t = X.t\n}"),
            "Modules do not match:\n    {\n      type t = int\n    }\n  is not included in\n    {\n      type t = X.t\n    }"
        );
    }

    #[test]
    fn pp_doc_breaks_the_box_around_a_short_multi_line_doc() {
        // A multi-line doc claims the whole margin, so the box breaks even
        // though every line is short, and a single-line doc after it starts
        // on its own line.
        assert_eq!(
            modules_do_not_match("{\n  let unrelated: string\n}", "HasFoo"),
            "Modules do not match:\n    {\n      let unrelated: string\n    }\n  is not included in\n    HasFoo"
        );
    }

    #[test]
    fn record_rows_print_their_runtime_name_as_an_as_attribute() {
        use super::{OutType, print_out_type};
        // The upstream example of 52ae045512, and `String.escaped`.
        let row = |name: &str, runtime_name: Option<&str>, mutable| {
            (
                name.to_string(),
                runtime_name.map(str::to_string),
                mutable,
                false,
                OutType::Otyp_stuff("int".to_string()),
            )
        };
        assert_eq!(
            print_out_type(&OutType::Otyp_record(vec![row(
                "field",
                Some("wire"),
                false
            )])),
            "{@as(\"wire\") field: int}"
        );
        assert_eq!(
            print_out_type(&OutType::Otyp_record(vec![
                row("a", Some("x\"y\\"), true),
                row("b", None, false),
            ])),
            "{@as(\"x\\\"y\\\\\") mutable a: int, b: int}"
        );
    }

    #[test]
    fn pp_doc_prints_a_single_line_doc_as_one_string() {
        assert_eq!(
            modules_do_not_match("S", "T"),
            "Modules do not match: S is not included in T"
        );
    }
}
