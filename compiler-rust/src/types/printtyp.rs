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
use crate::types::btype;
use crate::types::context::TypeContext;
use crate::types::path::Path;
use crate::parser::longident::Longident;
use crate::types::asttypes::ArgLabel;
use crate::types::type_expr::{FieldKind, GENERIC_LEVEL, RowDesc, RowField, TypeDesc, TypeExprRef};

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

/// `Outcometree.out_type`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum OutType {
    Otyp_abstract,
    Otyp_open,
    Otyp_alias(Box<OutType>, String),
    Otyp_arrow(Vec<(OutArgLabel, OutType)>, Box<OutType>),
    Otyp_class(bool, OutIdent, Vec<OutType>),
    Otyp_constr(OutIdent, Vec<OutType>),
    Otyp_manifest(Box<OutType>, Box<OutType>),
    Otyp_object(Vec<(String, OutType)>, Option<bool>),
    /// `(name, mutable, optional, type)` rows.
    Otyp_record(Vec<(String, bool, bool, OutType)>),
    Otyp_stuff(String),
    Otyp_tuple(Vec<OutType>),
    Otyp_var(bool, String),
    Otyp_variant(bool, OutVariant, bool, Option<Vec<String>>),
    Otyp_poly(Vec<String>, Box<OutType>),
    Otyp_module(String, Vec<String>, Vec<OutType>),
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
    /// `Env.lookup_type (Lident s) !printing_env` for
    /// `non_shadowed_pervasive_or_stdlib`; `None` stands for `Env.empty`,
    /// where every lookup fails.
    printing_env_lookup_type: Option<Box<dyn Fn(&str) -> Option<Path> + 'a>>,
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
            printing_env_lookup_type: None,
        }
    }

    /// `set_printing_env`: resolve unqualified type names in `lookup`.
    pub(crate) fn set_printing_env(&mut self, lookup: Box<dyn Fn(&str) -> Option<Path> + 'a>) {
        self.printing_env_lookup_type = Some(lookup);
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
        match &self.printing_env_lookup_type {
            None => true,
            Some(lookup) => match lookup(s) {
                Some(found) => path.same(&found),
                None => true,
            },
        }
    }

    /// `tree_of_path`.
    pub(crate) fn tree_of_path(&self, path: &Path) -> OutIdent {
        match path {
            Path::Pident(id) => OutIdent::Oide_ident(id.name().to_string()),
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
            Path::Pdot(p, s, _) => OutIdent::Oide_dot(Box::new(self.tree_of_path(p)), s.to_string()),
            Path::Papply(p1, p2) => OutIdent::Oide_apply(
                Box::new(self.tree_of_path(p1)),
                Box::new(self.tree_of_path(p2)),
            ),
        }
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
        if let TypeDesc::Tvar(Some(name)) | TypeDesc::Tunivar(Some(name)) =
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
            TypeDesc::Tvar(Some(name)) | TypeDesc::Tunivar(Some(name)) => Some(name.clone()),
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
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tpoly { .. }
        )
    }

    fn namable_row(&self, row: &RowDesc) -> bool {
        row.row_name.is_some()
            && row.row_fields.iter().all(|(_, f)| {
                match btype::row_field_repr(self.ctx, f) {
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
                }
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
                TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tconstr { .. } => {
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
            TypeDesc::Tvar(_) => self.add_named_var(ty),
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
            TypeDesc::Tobject { fields, name } => {
                if self.visited_objects.contains(&px) {
                    self.add_alias(px);
                } else {
                    if self.opened_object(ty) {
                        self.visited_objects.insert(0, px);
                    }
                    match name {
                        None => {
                            let (fields, _) = flatten_fields(self.ctx, fields);
                            for (_, kind, t) in fields {
                                if matches!(kind, FieldKind::Fpresent) {
                                    self.mark_loops_rec(visited, t);
                                }
                            }
                        }
                        Some((_, l)) => {
                            for t in l.into_iter().skip(1) {
                                self.mark_loops_rec(visited, t);
                            }
                        }
                    }
                }
            }
            TypeDesc::Tfield {
                kind, typ, rest, ..
            } => {
                if matches!(kind, FieldKind::Fpresent) {
                    self.mark_loops_rec(visited, typ);
                }
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
            TypeDesc::Tunivar(_) => self.add_named_var(ty),
        }
        visited.truncate(depth);
    }

    /// `mark_loops`.
    pub(crate) fn mark_loops(&mut self, ty: TypeExprRef) {
        crate::types::ctype::normalize_type(self.ctx, ty);
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
        sch && matches!(&*self.ctx.borrow_desc(ty), TypeDesc::Tvar(_))
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
                TypeDesc::Tvar(_) => {
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
                TypeDesc::Tconstr { path, args, .. } => {
                    OutType::Otyp_constr(this.tree_of_path(path), this.tree_of_typlist(sch, args))
                }
                TypeDesc::Tvariant(row) => this.tree_of_variant(sch, px, row),
                TypeDesc::Tobject { fields, name } => {
                    this.tree_of_typobject(sch, *fields, name.clone())
                }
                TypeDesc::Tnil | TypeDesc::Tfield { .. } => this.tree_of_typobject(sch, ty, None),
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
                TypeDesc::Tunivar(_) => OutType::Otyp_var(false, this.name_of_type(false, ty)),
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
                OutType::Otyp_variant(non_gen, OutVariant::Ovar_fields(fields), row.row_closed, tags)
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
            RowField::Rpresent(Some(ty)) => (l.to_string(), false, vec![self.tree_of_typexp(sch, ty)]),
            RowField::Reither {
                constant, types, ..
            } => (l.to_string(), constant, self.tree_of_typlist(sch, &types)),
            RowField::Rabsent => (l.to_string(), false, Vec::new()),
        }
    }

    fn tree_of_typlist(&mut self, sch: bool, tyl: &[TypeExprRef]) -> Vec<OutType> {
        tyl.iter().map(|t| self.tree_of_typexp(sch, *t)).collect()
    }

    fn tree_of_typobject(
        &mut self,
        sch: bool,
        fi: TypeExprRef,
        nm: Option<(Path, Vec<TypeExprRef>)>,
    ) -> OutType {
        match nm {
            None => {
                let (fields, rest) = flatten_fields(self.ctx, fi);
                let mut present: Vec<(String, TypeExprRef)> = fields
                    .into_iter()
                    .filter(|(_, k, _)| matches!(k, FieldKind::Fpresent))
                    .map(|(n, _, t)| (n, t))
                    .collect();
                present.sort_by(|(a, _), (b, _)| a.as_bytes().cmp(b.as_bytes()));
                let fields = present
                    .into_iter()
                    .map(|(s, t)| (s, self.tree_of_typexp(sch, t)))
                    .collect();
                let rest = match &*self.ctx.borrow_desc(rest) {
                    TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => Some(self.is_non_gen(sch, rest)),
                    TypeDesc::Tconstr { .. } => Some(false),
                    TypeDesc::Tnil => None,
                    _ => unreachable!("typfields (1)"),
                };
                OutType::Otyp_object(fields, rest)
            }
            Some((p, tyl)) if !tyl.is_empty() => {
                let non_gen = self.is_non_gen(sch, self.ctx.repr(tyl[0]));
                let args = self.tree_of_typlist(sch, &tyl[1..]);
                OutType::Otyp_class(non_gen, self.tree_of_path(&p), args)
            }
            Some(_) => unreachable!("Printtyp.tree_of_typobject"),
        }
    }

    /// `tree_of_label` (compiler/ml/printtyp.ml).
    fn tree_of_label(
        &mut self,
        l: &crate::types::decl::LabelDeclaration,
    ) -> (String, bool, bool, OutType) {
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
            crate::types::decl::ConstructorArguments::CstrTuple(l) => self.tree_of_typlist(false, l),
            crate::types::decl::ConstructorArguments::CstrRecord(l) => {
                let labels = l.iter().map(|l| self.tree_of_label(l)).collect();
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

    /// `type_scheme ppf ty`.
    pub(crate) fn type_scheme(&mut self, ty: TypeExprRef) -> String {
        self.reset_and_mark_loops(ty);
        self.type_sch(ty)
    }
}

/// `Ctype.flatten_fields` (compiler/ml/ctype.ml): the chain is accumulated
/// in reverse and then stably sorted by name.
fn flatten_fields(
    ctx: &TypeContext,
    ty: TypeExprRef,
) -> (Vec<(String, FieldKind, TypeExprRef)>, TypeExprRef) {
    let mut fields = Vec::new();
    let mut current = ctx.repr(ty);
    loop {
        let next = match &*ctx.borrow_desc(current) {
            TypeDesc::Tfield {
                name,
                kind,
                typ,
                rest,
            } => {
                fields.push((name.clone(), kind.clone(), *typ));
                *rest
            }
            _ => break,
        };
        current = ctx.repr(next);
    }
    fields.reverse();
    fields.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    (fields, current)
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
        OutIdent::Oide_dot(ident, s) => {
            Doc::concat(vec![print_out_ident_doc(true, ident), Doc::dot(), Doc::text(s.clone())])
        }
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
        OutType::Otyp_class(..) => Doc::nil(),
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
            Doc::group(Doc::concat(vec![print_out_ident_doc(true, out_ident), args_doc]))
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
                vars.iter().map(|var| Doc::text(format!("'{var}"))).collect(),
            ),
            Doc::dot(),
            Doc::space(),
            print_out_type_doc(out_type),
        ])),
        OutType::Otyp_arrow(..) => print_out_arrow_type(out_type),
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

fn print_object_fields(fields: &[(String, OutType)], rest: &Option<bool>) -> Doc {
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
                    .map(|(lbl, out_type)| {
                        Doc::group(Doc::concat(vec![
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

fn print_record_decl_row_doc((name, mutable, opt, arg): &(String, bool, bool, OutType)) -> Doc {
    Doc::group(Doc::concat(vec![
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

fn print_record_declaration_doc(inline: bool, rows: &[(String, bool, bool, OutType)]) -> Doc {
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

/// `print_out_type`: the doc rendered at width 80.
pub(crate) fn print_out_type(out_type: &OutType) -> String {
    print_out_type_doc(out_type).to_string(80)
}
