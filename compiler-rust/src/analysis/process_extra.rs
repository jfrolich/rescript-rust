//! References and located items of a module: a port of
//! analysis/src/process_extra.ml.

use super::process_attributes::{self as attrs, Attrs};
use super::process_cmt::{Annots, Ctx, dig};
use super::resolve_path::{self, Resolution};
use super::shared_types::*;
use crate::ident::{Ident, IdentFlags};
use crate::parse_arena::{LidentIdx, LocIdx};
use crate::parser::longident::Longident;
use crate::types::decl::ConstructorDescription;
use crate::types::path::PathView;
use crate::types::tast_iterator::{self as ti, TastIterator};
use crate::types::typedtree as tt;
use crate::types::{Path, TypeDesc, TypeExprRef};

/// `add_loc_item`.
fn add_loc_item(extra: &mut Extra, loc: Loc, loc_type: LocType) {
    if !loc.ghost {
        extra.loc_items.push(LocItem { loc, loc_type });
    }
}

/// `add_reference`. The locations are kept oldest first (the reverse of
/// OCaml's consed list); readers iterate them reversed. `Hashtbl.replace` on
/// a missing key is `Hashtbl.add`, so the bucket order is unchanged.
fn add_reference(extra: &mut Extra, stamp: i32, loc: Loc) {
    match extra.internal_references.find_mut(&stamp) {
        Some(locs) => locs.push(loc),
        None => extra.internal_references.add(stamp, vec![loc]),
    }
}

/// `extra_for_file`.
fn extra_for_file(file: &File, types: &crate::types::TypeContext) -> Extra {
    let mut extra = Extra::default();
    for (stamp, kind) in file.stamps.iter() {
        if let StampKind::Module(d) = kind {
            add_loc_item(
                &mut extra,
                d.name.loc,
                LocType::LModule(LocKind::Definition(*stamp, Tip::Module)),
            );
            add_reference(&mut extra, *stamp, d.name.loc);
        }
    }
    for (stamp, kind) in file.stamps.iter() {
        if let StampKind::Value(d) = kind {
            add_loc_item(
                &mut extra,
                d.name.loc,
                LocType::Typed(
                    d.name.txt.clone(),
                    d.item,
                    LocKind::Definition(*stamp, Tip::Value),
                ),
            );
            add_reference(&mut extra, *stamp, d.name.loc);
        }
    }
    for (stamp, kind) in file.stamps.iter() {
        let StampKind::Type(d) = kind else {
            continue;
        };
        add_loc_item(
            &mut extra,
            d.name.loc,
            LocType::TypeDefinition(d.name.txt.clone(), d.item.decl.clone(), *stamp),
        );
        add_reference(&mut extra, *stamp, d.name.loc);
        match &d.item.kind {
            TypeKind::Record(labels) => {
                for label in labels {
                    add_reference(&mut extra, label.stamp, label.fname.loc);
                    add_loc_item(
                        &mut extra,
                        label.fname.loc,
                        LocType::Typed(
                            d.name.txt.clone(),
                            label.typ,
                            LocKind::Definition(d.stamp, Tip::Field(label.fname.txt.clone())),
                        ),
                    );
                }
            }
            TypeKind::Variant(constructors) => {
                for c in constructors {
                    add_reference(&mut extra, c.stamp, c.cname.loc);
                    let path = Path::pident(Ident::new(
                        d.name.txt.as_str(),
                        c.stamp,
                        IdentFlags::from_bits_truncate(0),
                    ));
                    let t = types.new_type(TypeDesc::Tconstr {
                        path,
                        args: Default::default(),
                        abbrev: types.alloc_abbrev_nil(),
                    });
                    add_loc_item(
                        &mut extra,
                        c.cname.loc,
                        LocType::Typed(
                            d.name.txt.clone(),
                            t,
                            LocKind::Definition(d.stamp, Tip::Constructor(c.cname.txt.clone())),
                        ),
                    );
                }
            }
            _ => {}
        }
    }
    extra
}

/// `add_external_reference`.
fn add_external_reference(
    extra: &mut Extra,
    module_name: &str,
    path: ModulePathList,
    tip: Tip,
    loc: Loc,
) {
    // Oldest first, like `add_reference`.
    match extra.external_references.find_mut(module_name) {
        Some(refs) => refs.push((path, tip, loc)),
        None => extra
            .external_references
            .add(module_name.to_string(), vec![(path, tip, loc)]),
    }
}

/// `add_file_reference`.
fn add_file_reference(extra: &mut Extra, module_name: &str, loc: Loc) {
    match extra.file_references.find_mut(module_name) {
        Some(locs) => {
            locs.insert(std::cmp::Reverse(loc));
        }
        None => extra.file_references.add(
            module_name.to_string(),
            LocationSet::from([std::cmp::Reverse(loc)]),
        ),
    }
}

/// `Longident.flatten`; `None` for a functor application, where OCaml
/// raises.
fn flatten(ctx: &Ctx<'_>, lid: &Longident) -> Option<Vec<String>> {
    match lid {
        Longident::Lident(s) => Some(vec![ctx.arena.get_string(*s).to_string()]),
        Longident::Ldot(lid, s) => {
            let mut path = flatten(ctx, lid)?;
            path.push(ctx.arena.get_string(*s).to_string());
            Some(path)
        }
        Longident::Lapply(..) => None,
    }
}

fn last(ctx: &Ctx<'_>, lid: &Longident) -> String {
    ctx.arena.get_string(lid.last_idx()).to_string()
}

/// `get_type_at_path`.
enum TypeAtPath {
    NotFound,
    Global(String, ModulePathList),
    /// The key of a type in the file's stamps.
    Local(i32),
}

/// The fields of a `Texp_record` that `add_for_record` reads.
struct RecordItem {
    lid: LidentIdx,
    loc: LocIdx,
}

/// The `Tast_iterator` of `get_extra`.
struct ExtraIterator<'a, 'f> {
    ctx: Ctx<'a>,
    file: &'f mut File,
    env: QueryEnv,
    extra: Extra,
}

impl ExtraIterator<'_, '_> {
    fn loc(&self, idx: LocIdx) -> Loc {
        Loc::of_idx(self.ctx.arena, idx)
    }

    fn resolve(&self, path: &Path) -> Resolution {
        resolve_path::from_compiler_path(self.file, &self.env, path)
    }

    /// `add_for_path`.
    fn add_for_path(
        &mut self,
        path: &Path,
        lident: &Longident,
        loc: Loc,
        typ: TypeExprRef,
        tip: Tip,
    ) {
        let ident_name = last(&self.ctx, lident);
        let ident_loc = loc.end_of_location(ident_name.len() as i32);
        let loc_type = match self.resolve(path) {
            Resolution::Stamp(stamp) => {
                add_reference(&mut self.extra, stamp, ident_loc);
                LocKind::LocalReference(stamp, tip)
            }
            Resolution::NotFound | Resolution::GlobalMod(_) => LocKind::NotFound,
            Resolution::Global(module_name, path) => {
                add_external_reference(
                    &mut self.extra,
                    &module_name,
                    path.clone(),
                    tip.clone(),
                    ident_loc,
                );
                LocKind::GlobalReference(module_name, path, tip)
            }
            Resolution::Exported(env, name) => {
                let kind = match tip {
                    Tip::Type => ExportedKind::Type,
                    _ => ExportedKind::Value,
                };
                match env.exported.find(kind, &name) {
                    Some(stamp) => {
                        add_reference(&mut self.extra, stamp, ident_loc);
                        LocKind::LocalReference(stamp, tip)
                    }
                    None => LocKind::NotFound,
                }
            }
        };
        add_loc_item(
            &mut self.extra,
            loc,
            LocType::Typed(ident_name, typ, loc_type),
        );
    }

    /// `add_for_path_parent`.
    fn add_for_path_parent(&mut self, path: &Path, loc: Loc) {
        let loc_type = match self.resolve(path) {
            Resolution::GlobalMod(module_name) => {
                add_file_reference(&mut self.extra, &module_name, loc);
                LocType::TopLevelModule(module_name)
            }
            Resolution::Stamp(stamp) => {
                add_reference(&mut self.extra, stamp, loc);
                LocType::LModule(LocKind::LocalReference(stamp, Tip::Module))
            }
            Resolution::NotFound => LocType::LModule(LocKind::NotFound),
            Resolution::Global(module_name, path) => {
                add_external_reference(
                    &mut self.extra,
                    &module_name,
                    path.clone(),
                    Tip::Module,
                    loc,
                );
                LocType::LModule(LocKind::GlobalReference(module_name, path, Tip::Module))
            }
            Resolution::Exported(env, name) => match env.exported.find(ExportedKind::Module, &name)
            {
                Some(stamp) => {
                    add_reference(&mut self.extra, stamp, loc);
                    LocType::LModule(LocKind::LocalReference(stamp, Tip::Module))
                }
                None => LocType::LModule(LocKind::NotFound),
            },
        };
        add_loc_item(&mut self.extra, loc, loc_type);
    }

    /// `get_type_at_path`.
    fn get_type_at_path(&self, path: &Path) -> TypeAtPath {
        let find = |stamp: i32| match self.file.stamps.find_type(stamp) {
            Some(_) => TypeAtPath::Local(stamp),
            None => TypeAtPath::NotFound,
        };
        match self.resolve(path) {
            Resolution::GlobalMod(_) | Resolution::NotFound => TypeAtPath::NotFound,
            Resolution::Global(module_name, path) => TypeAtPath::Global(module_name, path),
            Resolution::Exported(env, name) => match env.exported.find(ExportedKind::Type, &name) {
                None => TypeAtPath::NotFound,
                Some(stamp) => find(stamp),
            },
            Resolution::Stamp(stamp) => find(stamp),
        }
    }

    fn constr_path(&self, t: TypeExprRef) -> Option<Path> {
        super::shared::dig_constructor(self.ctx.types, t)
    }

    /// The field named `name` of a record type, as a reference.
    fn field_reference(&mut self, t: &TypeAtPath, name: &str, name_loc: Loc) -> LocKind {
        match t {
            TypeAtPath::Local(key) => match self.file.stamps.find_type(*key) {
                Some(Declared {
                    stamp,
                    item:
                        Type {
                            kind: TypeKind::Record(fields),
                            ..
                        },
                    ..
                }) => match fields.iter().find(|f| f.fname.txt == name) {
                    Some(field) => {
                        add_reference(&mut self.extra, field.stamp, name_loc);
                        LocKind::LocalReference(*stamp, Tip::Field(name.to_string()))
                    }
                    None => LocKind::NotFound,
                },
                _ => LocKind::NotFound,
            },
            TypeAtPath::Global(module_name, path) => {
                let tip = Tip::Field(name.to_string());
                add_external_reference(
                    &mut self.extra,
                    module_name,
                    path.clone(),
                    tip.clone(),
                    name_loc,
                );
                LocKind::GlobalReference(module_name.clone(), path.clone(), tip)
            }
            _ => LocKind::NotFound,
        }
    }

    /// `add_for_field`.
    fn add_for_field(
        &mut self,
        record_type: TypeExprRef,
        field_type: TypeExprRef,
        lid: &tt::Loc<LidentIdx>,
    ) {
        let Some(path) = self.constr_path(record_type) else {
            return;
        };
        let t = self.get_type_at_path(&path);
        let name = last(&self.ctx, self.ctx.arena.get_longident(lid.txt));
        let name_loc = self.loc(lid.loc).end_of_location(name.len() as i32);
        let loc_type = self.field_reference(&t, &name, name_loc);
        add_loc_item(
            &mut self.extra,
            name_loc,
            LocType::Typed(name, field_type, loc_type),
        );
    }

    /// `add_for_record`.
    fn add_for_record(&mut self, record_type: TypeExprRef, items: &[RecordItem]) {
        let Some(path) = self.constr_path(record_type) else {
            return;
        };
        let t = self.get_type_at_path(&path);
        for item in items {
            let name = last(&self.ctx, self.ctx.arena.get_longident(item.lid));
            let name_loc = self.loc(item.loc).end_of_location(name.len() as i32);
            let loc_type = self.field_reference(&t, &name, name_loc);
            add_loc_item(
                &mut self.extra,
                name_loc,
                LocType::Typed(name, record_type, loc_type),
            );
        }
    }

    /// `add_for_constructor`.
    fn add_for_constructor(
        &mut self,
        constructor_type: TypeExprRef,
        lid: &tt::Loc<LidentIdx>,
        constructor: &ConstructorDescription,
    ) {
        let Some(path) = self.constr_path(constructor_type) else {
            return;
        };
        let name = last(&self.ctx, self.ctx.arena.get_longident(lid.txt));
        let name_loc = self.loc(lid.loc).end_of_location(name.len() as i32);
        let t = self.get_type_at_path(&path);
        let loc_type = match &t {
            TypeAtPath::Local(key) => match self.file.stamps.find_type(*key) {
                Some(Declared {
                    stamp,
                    item:
                        Type {
                            kind: TypeKind::Variant(constructors),
                            ..
                        },
                    ..
                }) => match constructors
                    .iter()
                    .find(|c| c.cname.txt == constructor.cstr_name)
                {
                    Some(c) => {
                        add_reference(&mut self.extra, c.stamp, name_loc);
                        LocKind::LocalReference(*stamp, Tip::Constructor(name.clone()))
                    }
                    None => LocKind::NotFound,
                },
                _ => LocKind::NotFound,
            },
            TypeAtPath::Global(module_name, path) => {
                let tip = Tip::Constructor(name.clone());
                add_external_reference(
                    &mut self.extra,
                    module_name,
                    path.clone(),
                    tip.clone(),
                    name_loc,
                );
                LocKind::GlobalReference(module_name.clone(), path.clone(), tip)
            }
            _ => LocKind::NotFound,
        };
        add_loc_item(
            &mut self.extra,
            name_loc,
            LocType::Typed(name, constructor_type, loc_type),
        );
    }

    /// `add_for_longident`.
    fn add_for_longident(
        &mut self,
        top: Option<(TypeExprRef, Tip)>,
        path: &Path,
        txt: &Longident,
        loc: Loc,
    ) {
        // `lid_is_complex` is false for every longident.
        if loc.ghost {
            return;
        }
        let Some(flat) = flatten(&self.ctx, txt) else {
            return;
        };
        // The length of `String.concat "." flat`.
        let id_length = (flat.iter().map(String::len).sum::<usize>() + flat.len() - 1) as i32;
        let reported_length = loc.end.cnum - loc.start.cnum;
        let is_ppx = id_length != reported_length;
        if is_ppx {
            match top {
                Some((t, tip)) => self.add_for_path(path, txt, loc, t, tip),
                None => self.add_for_path_parent(path, loc),
            }
        } else {
            let l = loc.end_of_location(last(&self.ctx, txt).len() as i32);
            match top {
                Some((t, tip)) => self.add_for_path(path, txt, l, t, tip),
                None => self.add_for_path_parent(path, l),
            }
            if let (PathView::Pdot(pinner, _, _), Longident::Ldot(inner, name)) = (path.view(), txt)
            {
                let name_len = self.ctx.arena.get_string(*name).len() as i32;
                self.add_for_longident(None, pinner, inner, loc.chop_location_end(name_len + 1));
            }
        }
    }

    fn add_for_lident(
        &mut self,
        top: Option<(TypeExprRef, Tip)>,
        path: &Path,
        lid: &tt::Loc<LidentIdx>,
    ) {
        let arena = self.ctx.arena;
        let txt = arena.get_longident(lid.txt);
        let loc = self.loc(lid.loc);
        self.add_for_longident(top, path, txt, loc);
    }

    /// `handle_module_expr`.
    fn handle_module_expr(&mut self, expr: &tt::ModuleExprDesc) {
        match expr {
            tt::ModuleExprDesc::Tmod_constraint(expr, _, _, _) => {
                self.handle_module_expr(&self.ctx.ta.module_expr(*expr).mod_desc)
            }
            tt::ModuleExprDesc::Tmod_ident(path, lid) => self.add_for_lident(None, path, lid),
            tt::ModuleExprDesc::Tmod_functor(_, _, _, result) => {
                self.handle_module_expr(&self.ctx.ta.module_expr(*result).mod_desc)
            }
            tt::ModuleExprDesc::Tmod_apply(obj, arg, _) => {
                self.handle_module_expr(&self.ctx.ta.module_expr(*obj).mod_desc);
                self.handle_module_expr(&self.ctx.ta.module_expr(*arg).mod_desc);
            }
            _ => {}
        }
    }

    /// `add_for_declared_pattern` of `pat`.
    fn add_for_declared_pattern(
        &mut self,
        stamp: i32,
        name: Located<String>,
        extent: Loc,
        item: TypeExprRef,
        attributes: Attrs<'_>,
    ) {
        if self.file.stamps.find_value(stamp).is_none() {
            let declared = attrs::new_declared(
                item,
                extent,
                name.clone(),
                stamp,
                ModulePath::NotVisible,
                false,
                self.ctx.raised.declared_attributes(attributes),
            );
            self.file.stamps.add_value(stamp, declared);
            add_reference(&mut self.extra, stamp, name.loc);
            add_loc_item(
                &mut self.extra,
                name.loc,
                LocType::Typed(name.txt, item, LocKind::Definition(stamp, Tip::Value)),
            );
        }
    }

    /// A `Tpat_var`/`Tpat_alias` binding.
    fn add_for_pattern_binding(
        &mut self,
        pattern: &tt::Pattern,
        ident: &Ident,
        name: &tt::Loc<String>,
    ) {
        let stamp = ident.binding_time();
        let name = Located {
            txt: name.txt.clone(),
            loc: self.loc(name.loc),
        };
        let has_unpack = self
            .ctx
            .ta
            .pat_extra(pattern)
            .iter()
            .any(|(extra, _, _)| matches!(extra, tt::PatExtra::Tpat_unpack));
        let unpacked = if has_unpack {
            match &*self
                .ctx
                .types
                .get_desc(dig(self.ctx.types, pattern.pat_type))
            {
                TypeDesc::Tpackage { path, .. } => Some(*path),
                _ => None,
            }
        } else {
            None
        };
        let attributes = Attrs::Parsed(
            self.ctx.ta.pat_attributes(pattern).as_slice(),
            self.ctx.arena,
        );
        match unpacked {
            Some(path) => {
                let extent = name.loc;
                let declared = attrs::new_declared(
                    Module::Ident(path),
                    extent,
                    name,
                    stamp,
                    ModulePath::NotVisible,
                    false,
                    self.ctx.raised.declared_attributes(attributes),
                );
                self.file.stamps.add_module(stamp, declared);
            }
            None => {
                let extent = self.loc(pattern.pat_loc);
                self.add_for_declared_pattern(stamp, name, extent, pattern.pat_type, attributes);
            }
        }
    }
}

impl<'a> TastIterator<'a> for ExtraIterator<'a, '_> {
    fn arena(&self) -> &'a tt::TypedArena {
        self.ctx.ta
    }

    fn structure_item(&mut self, item: &tt::StructureItem) {
        match &item.str_desc {
            tt::StructureItemDesc::Tstr_include(incl) => {
                self.handle_module_expr(&self.ctx.ta.module_expr(incl.incl_mod).mod_desc)
            }
            tt::StructureItemDesc::Tstr_module(mb) => {
                self.handle_module_expr(&self.ctx.ta.module_expr(mb.mb_expr).mod_desc)
            }
            tt::StructureItemDesc::Tstr_open(open) => {
                let lid = tt::Loc {
                    txt: open.open_txt.txt,
                    loc: open.open_txt.loc,
                };
                self.add_for_lident(None, &open.open_path, &lid);
            }
            _ => {}
        }
        ti::walk_structure_item(self, item)
    }

    fn signature_item(&mut self, item: &tt::TypedSignatureItem) {
        if let tt::TypedSignatureItemDesc::Tsig_value(vd) = &item.sig_desc {
            let stamp = self.ctx.ta.value_description(*vd).val_id.binding_time();
            if self.file.stamps.find_value(stamp).is_none() {
                let name = Located {
                    txt: self.ctx.ta.value_description(*vd).val_name.txt.clone(),
                    loc: self.loc(self.ctx.ta.value_description(*vd).val_name.loc),
                };
                let declared = attrs::new_declared(
                    self.ctx
                        .ta
                        .core_type(self.ctx.ta.value_description(*vd).val_desc)
                        .ctyp_type,
                    self.loc(self.ctx.ta.value_description(*vd).val_loc),
                    name.clone(),
                    stamp,
                    ModulePath::NotVisible,
                    false,
                    self.ctx.raised.declared_attributes(Attrs::Parsed(
                        self.ctx.ta.value_description(*vd).val_attributes.as_slice(),
                        self.ctx.arena,
                    )),
                );
                self.file.stamps.add_value(stamp, declared);
                add_reference(&mut self.extra, stamp, name.loc);
                add_loc_item(
                    &mut self.extra,
                    name.loc,
                    LocType::Typed(
                        name.txt,
                        self.ctx
                            .ta
                            .core_type(self.ctx.ta.value_description(*vd).val_desc)
                            .ctyp_type,
                        LocKind::Definition(stamp, Tip::Value),
                    ),
                );
            }
        }
        ti::walk_signature_item(self, item)
    }

    fn typ(&mut self, item: &tt::TypedCoreType) {
        if let tt::TypedCoreTypeDesc::Ttyp_constr(path, lid, _) = &item.ctyp_desc {
            self.add_for_lident(Some((item.ctyp_type, Tip::Type)), path, lid);
        }
        ti::walk_typ(self, item)
    }

    fn pat(&mut self, pattern: &tt::Pattern) {
        match &pattern.pat_desc {
            tt::PatternDesc::Tpat_record(items, _, rest) => {
                let record_items: Vec<RecordItem> = items
                    .iter()
                    .map(|(lid, _, _, _)| RecordItem {
                        lid: lid.txt,
                        loc: lid.loc,
                    })
                    .collect();
                self.add_for_record(pattern.pat_type, &record_items);
                if let Some(rest) = rest {
                    let name = Located {
                        txt: rest.rest_name.txt.clone(),
                        loc: self.loc(rest.rest_name.loc),
                    };
                    let extent = name.loc;
                    let attributes = Attrs::Parsed(
                        self.ctx.ta.pat_attributes(pattern).as_slice(),
                        self.ctx.arena,
                    );
                    self.add_for_declared_pattern(
                        rest.rest_ident.binding_time(),
                        name,
                        extent,
                        rest.rest_type,
                        attributes,
                    );
                }
            }
            tt::PatternDesc::Tpat_construct(lid, constructor, _) => {
                self.add_for_constructor(pattern.pat_type, lid, constructor)
            }
            tt::PatternDesc::Tpat_alias(_, ident, name)
            | tt::PatternDesc::Tpat_var(ident, name) => {
                self.add_for_pattern_binding(pattern, ident, name)
            }
            _ => {}
        }
        ti::walk_pat(self, pattern)
    }

    fn expr(&mut self, expression: &tt::Expression) {
        match &expression.exp_desc {
            tt::ExpressionDesc::Texp_ident(path, lid, _) => {
                self.add_for_lident(Some((expression.exp_type, Tip::Value)), path, lid)
            }
            tt::ExpressionDesc::Texp_record { fields, .. } => {
                // process_extra.ml:434-438: every written field.
                let items: Vec<RecordItem> = self
                    .ctx
                    .ta
                    .record_fields(*fields)
                    .iter()
                    .map(|(_, lid, _)| RecordItem {
                        lid: lid.txt,
                        loc: lid.loc,
                    })
                    .collect();
                self.add_for_record(expression.exp_type, &items);
            }
            tt::ExpressionDesc::Texp_constant(constant) => {
                let loc = self.loc(expression.exp_loc);
                add_loc_item(&mut self.extra, loc, LocType::Constant(constant.clone()));
            }
            tt::ExpressionDesc::Texp_construct(lid, constructor, _) => {
                // Skip unit and list literals.
                let skip = match self.ctx.arena.get_longident(lid.txt) {
                    Longident::Lident(name) => {
                        let loc = self.loc(lid.loc);
                        matches!(self.ctx.arena.get_string(*name), "()" | "::")
                            && loc.end.cnum - loc.start.cnum != 2
                    }
                    _ => false,
                };
                if !skip {
                    self.add_for_constructor(expression.exp_type, lid, constructor);
                }
            }
            tt::ExpressionDesc::Texp_field(inner, lid, _) => {
                self.add_for_field(self.ctx.ta.expr(*inner).exp_type, expression.exp_type, lid)
            }
            _ => {}
        }
        ti::walk_expr(self, expression)
    }
}

/// `get_extra`. Values and modules the walk finds (local bindings) are
/// added to the file's stamps, as OCaml's shared stamp table is updated.
pub fn get_extra(ctx: Ctx<'_>, file: &mut File, annots: Annots<'_>) -> Extra {
    let extra = extra_for_file(file, ctx.types);
    let env = QueryEnv::from_file(file);
    let mut iterator = ExtraIterator {
        ctx,
        file,
        env,
        extra,
    };
    match annots {
        Annots::Implementation(items) => {
            for item in items {
                iterator.structure_item(item);
            }
        }
        Annots::Interface(items) => {
            for item in items {
                iterator.signature_item(item);
            }
        }
    }
    iterator.extra
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::parser::{Parser, module};
    use crate::types::{TypeCheckContext, TypeContext, initial_env};

    /// The field references `get_extra` records for `source`, as
    /// `(field, one-based line)` in insertion order.
    fn field_references(source: &str) -> Vec<(String, i32)> {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let _ = id_gen.next_stamp();
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut parser = Parser::new("Test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let arena = parser.arena();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = crate::types::typemod::type_structure(&mut tctx, &env, arena, &structure)
            .expect("typecheck");
        let raised = crate::analysis::process_attributes::Raised::default();
        let ctx = Ctx {
            ta: &tctx.typed,
            arena,
            types: &type_ctx,
            raised: &raised,
        };
        let annots = crate::analysis::process_cmt::Annots::Implementation(tctx.typed.structure_items(typed.str_items));
        let mut file = crate::analysis::process_cmt::file_for_annots(
            ctx,
            0,
            "Test",
            "Test.res".to_string(),
            annots,
        );
        let extra = get_extra(ctx, &mut file, annots);
        extra
            .loc_items
            .iter()
            .filter_map(|item| match &item.loc_type {
                LocType::Typed(name, _, LocKind::LocalReference(_, Tip::Field(_))) => {
                    Some((name.clone(), item.loc.start.line))
                }
                _ => None,
            })
            .collect()
    }

    #[test]
    fn record_literals_reference_only_their_written_fields() {
        // process_extra.ml:434-438: `Texp_record` adds a reference for each
        // written field. An omitted optional field and a field taken from the
        // spread are not written, so they get none.
        let refs = field_references(
            r#"type r = {a: int, b?: int, c?: string}
let base: r = {a: 1}
let x: r = {a: 2, b: 3}
let y = {...base, c: "s"}
"#,
        );
        assert_eq!(
            refs,
            [
                ("a".to_string(), 2),
                ("a".to_string(), 3),
                ("b".to_string(), 3),
                ("c".to_string(), 4),
            ]
        );
    }
}
