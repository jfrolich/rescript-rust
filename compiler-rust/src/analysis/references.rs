//! A port of analysis/src/references.ml.

use super::process_cmt::dig;
use super::resolve_path::{self, Resolution, Session};
use super::session::{Loaded, ProjectSession};
use super::shared_types::*;
use super::uri;
use crate::types::{Path, TypeDesc};

/// `check_pos`: whether the 1-based line and column lie within `loc`.
fn check_pos((line, char): (i32, i32), loc: &Loc) -> bool {
    if line < loc.start.line || (line == loc.start.line && char < loc.start.cnum - loc.start.bol) {
        false
    } else {
        !(line > loc.end.line || (line == loc.end.line && char > loc.end.cnum - loc.end.bol))
    }
}

/// `loc_items_for_pos`, in OCaml's list order (most recently added first).
pub fn loc_items_for_pos(extra: &Extra, pos: (i32, i32)) -> Vec<&LocItem> {
    extra
        .loc_items
        .iter()
        .rev()
        .filter(|item| check_pos(pos, &item.loc))
        .collect()
}

/// `normalize_external_reference_key`.
fn normalize_external_reference_key(
    namespace: Option<&str>,
    module_name: &str,
    path: ModulePathList,
) -> (String, ModulePathList) {
    match namespace {
        Some(namespace) if module_name.ends_with(&format!("-{namespace}")) => {
            let source_module = &module_name[..module_name.len() - namespace.len() - 1];
            let mut path = path;
            path.insert(0, source_module.to_string());
            (namespace.to_string(), path)
        }
        _ => (module_name.to_string(), path),
    }
}

/// `get_loc_item`. `pos` is 0-based.
pub fn get_loc_item(
    full: &Loaded,
    pos: (i32, i32),
    debug: bool,
    out: &mut super::Output,
) -> Option<LocItem> {
    let log = |out: &mut super::Output, n: i32, msg: &str| {
        if debug {
            out.print(&format!("getLocItem #{n}: {msg}\n"));
        }
    };
    let pos = (pos.0 + 1, pos.1);
    let loc_items = loc_items_for_pos(&full.extra, pos);
    let name_of = |li: &LocItem| match &li.loc_type {
        LocType::Typed(n, _, _) => n.clone(),
        _ => "NotFound".to_string(),
    };
    fn typed_name(li: &LocItem) -> Option<&str> {
        match &li.loc_type {
            LocType::Typed(n, _, _) => Some(n),
            _ => None,
        }
    }
    fn kind(li: &LocItem) -> Option<&LocKind> {
        match &li.loc_type {
            LocType::Typed(_, _, kind) => Some(kind),
            _ => None,
        }
    }
    let item = match loc_items.as_slice() {
        [li1, li2, li3, li4, ..]
            if typed_name(li4) == Some("makeProps") && uri::is_interface(&full.file.uri) =>
        {
            log(out, 1, "heuristic for makeProps in interface files");
            if debug {
                out.print(&format!(
                    "n1:{} n2:{} n3:{}\n",
                    name_of(li1),
                    name_of(li2),
                    name_of(li3)
                ));
            }
            Some(*li4)
        }
        [li1, li2]
            if matches!(li1.loc_type, LocType::Constant(_))
                && typed_name(li2) == Some("createDOMElementVariadic") =>
        {
            log(out, 3, "heuristic for <div>");
            Some(*li2)
        }
        [li1, li2, ..]
            if typed_name(li1) == Some("makeProps") && typed_name(li2) == Some("make") =>
        {
            log(
                out,
                4,
                "heuristic for </Comp> within fragments: take make as makeProps does not work\nthe type is not great but jump to definition works",
            );
            Some(*li2)
        }
        [li1, li2]
            if matches!(kind(li1), Some(LocKind::LocalReference(..)))
                && kind(li2).is_some()
                && li1.loc == li2.loc =>
        {
            log(
                out,
                5,
                "heuristic for JSX and compiler combined:\n~x becomes Props#x\nheuristic for: [Props, x], give loc of `x`",
            );
            if debug {
                out.print(&format!("n1:{} n2:{}\n", name_of(li1), name_of(li2)));
            }
            Some(*li2)
        }
        [li1, li2, li3]
            if matches!(kind(li1), Some(LocKind::LocalReference(..)))
                && matches!(
                    kind(li2),
                    Some(LocKind::GlobalReference(m, p, _)) if m == "Js_OO" && *p == ["unsafe_downgrade"]
                )
                && li1.loc == li2.loc
                && li2.loc == li3.loc =>
        {
            log(
                out,
                6,
                "heuristic for JSX and compiler combined:\n~x becomes Js_OO.unsafe_downgrade(Props)#x\nheuristic for: [Props, unsafe_downgrade, x], give loc of `x`",
            );
            Some(*li3)
        }
        [li1, li2]
            if matches!(kind(li1), Some(LocKind::LocalReference(_, Tip::Value)))
                && matches!(kind(li2), Some(LocKind::Definition(_, Tip::Value))) =>
        {
            log(
                out,
                7,
                "heuristic for JSX on type-annotated labeled (~arg:t):\n(~arg:t) becomes Props#arg\nProps has the location range of arg:t\narg has the location range of arg\nheuristic for: [Props, arg], give loc of `arg`",
            );
            if debug {
                out.print(&format!("n1:{} n2:{}\n", name_of(li1), name_of(li2)));
            }
            Some(*li2)
        }
        [li1, li2, li3] if li1.loc == li2.loc && li2.loc == li3.loc => {
            log(
                out,
                8,
                "heuristic for JSX with at most one child\nheuristic for: [makeProps, make, createElement], give the loc of `make` ",
            );
            Some(*li2)
        }
        [li1, li2, li3, li4] if li1.loc == li2.loc && li2.loc == li3.loc && li3.loc == li4.loc => {
            log(
                out,
                9,
                "heuristic for JSX variadic, e.g. <C> {x} {y} </C>\nheuristic for: [React.null, makeProps, make, createElementVariadic], give the loc of `make`",
            );
            if debug {
                out.print(&format!(
                    "n1:{} n2:{} n3:{} n4:{}\n",
                    name_of(li1),
                    name_of(li2),
                    name_of(li3),
                    name_of(li4)
                ));
            }
            Some(*li3)
        }
        [li1, li, ..]
            if match &li1.loc_type {
                LocType::Typed(_, t, _) => match &*full.source.typed.type_ctx.get_desc(*t) {
                    TypeDesc::Tconstr { path, .. } => super::shared::is_uncurried_internal(path),
                    _ => false,
                },
                _ => false,
            } =>
        {
            Some(*li)
        }
        [li, ..] => Some(*li),
        [] => None,
    };
    item.cloned()
}

/// `declared_for_tip`, with the item dropped.
pub fn declared_for_tip(stamps: &Stamps, stamp: i32, tip: &Tip) -> Option<Declared<()>> {
    fn erase<T>(d: &Declared<T>) -> Declared<()> {
        Declared {
            name: d.name.clone(),
            extent_loc: d.extent_loc,
            stamp: d.stamp,
            module_path: d.module_path.clone(),
            is_exported: d.is_exported,
            deprecated: d.deprecated.clone(),
            docstring: d.docstring.clone(),
            item: (),
        }
    }
    match tip {
        Tip::Value => stamps.find_value(stamp).map(erase),
        Tip::Field(_) | Tip::Constructor(_) | Tip::Type => stamps.find_type(stamp).map(erase),
        Tip::Module => stamps.find_module(stamp).map(erase),
    }
}

/// `get_field`.
pub fn get_field<'a>(file: &'a File, stamp: i32, name: &str) -> Option<&'a Field> {
    match &file.stamps.find_type(stamp)?.item.kind {
        TypeKind::Record(fields) => fields.iter().find(|f| f.fname.txt == name),
        _ => None,
    }
}

/// `get_constructor`.
pub fn get_constructor<'a>(file: &'a File, stamp: i32, name: &str) -> Option<&'a Constructor> {
    match &file.stamps.find_type(stamp)?.item.kind {
        TypeKind::Variant(constructors) => constructors.iter().find(|c| c.cname.txt == name),
        _ => None,
    }
}

/// `exported_for_tip`.
pub fn exported_for_tip(
    session: &ProjectSession<'_>,
    env: &QueryEnv,
    path: &[String],
    tip: &Tip,
) -> Option<(QueryEnv, String, i32)> {
    let (env, name) = resolve_path::resolve_path(session, env, path)?;
    let kind = match tip {
        Tip::Value => ExportedKind::Value,
        Tip::Field(_) | Tip::Constructor(_) | Tip::Type => ExportedKind::Type,
        Tip::Module => ExportedKind::Module,
    };
    let stamp = env.exported.find(kind, &name)?;
    Some((env, name, stamp))
}

/// What `defined_for_loc` found (OCaml's polymorphic variants). A
/// constructor comes with the module its types belong to.
pub enum Defined {
    Constructor(Constructor, ModuleId),
    Field,
    Declared,
}

/// `defined_for_loc`.
pub fn defined_for_loc(
    session: &ProjectSession<'_>,
    file: &File,
    loc_kind: &LocKind,
) -> Option<(Vec<String>, Defined)> {
    let inner = |file: &File, stamp: i32, tip: &Tip| match tip {
        Tip::Constructor(name) => {
            let constructor = get_constructor(file, stamp, name)?;
            Some((
                constructor.docstring.clone(),
                Defined::Constructor(constructor.clone(), file.module),
            ))
        }
        Tip::Field(name) => Some((
            get_field(file, stamp, name)
                .map(|f| f.docstring.clone())
                .unwrap_or_default(),
            Defined::Field,
        )),
        _ => {
            let declared = declared_for_tip(&file.stamps, stamp, tip)?;
            Some((declared.docstring, Defined::Declared))
        }
    };
    match loc_kind {
        LocKind::NotFound => None,
        LocKind::LocalReference(stamp, tip) | LocKind::Definition(stamp, tip) => {
            inner(file, *stamp, tip)
        }
        LocKind::GlobalReference(module_name, path, tip) => {
            let file = session.file_for_module(module_name)?;
            let env = QueryEnv::from_file(file);
            let (env, _, stamp) = exported_for_tip(session, &env, path, tip)?;
            inner(session.file(env.file), stamp, tip)
        }
    }
}

/// `alternate_declared`: the declaration in the implementation for one in
/// an interface, or the other way around.
pub fn alternate_declared<'s>(
    session: &'s ProjectSession<'_>,
    file: &File,
    declared: &Declared<()>,
    tip: &Tip,
) -> Option<(&'s Loaded, Declared<()>)> {
    let paths = session.project().paths_for_module(&file.module_name)?;
    let (Some(res), Some(resi)) = (paths.implementation, paths.interface) else {
        return None;
    };
    let alternate = if uri::is_interface(&file.uri) {
        res
    } else {
        resi
    };
    let full = session.full_from_path(&alternate)?;
    let env = QueryEnv::from_file(&full.file);
    let path = declared.module_path.to_path(&declared.name.txt);
    let (_, _, stamp) = exported_for_tip(session, &env, &path, tip)?;
    let declared = declared_for_tip(&full.file.stamps, stamp, tip)?;
    Some((full, declared))
}

/// `resolve_module_reference`.
pub fn resolve_module_reference<'s>(
    session: &'s ProjectSession<'_>,
    file: &'s File,
    declared: &Declared<Module>,
    paths_seen: &[Path],
) -> Option<(&'s File, Option<Declared<Module>>)> {
    match &declared.item {
        Module::Structure(_) => Some((file, Some(declared.clone()))),
        Module::Constraint(_, module_type_item) => {
            let declared = Declared {
                item: (**module_type_item).clone(),
                ..declared.clone()
            };
            resolve_module_reference(session, file, &declared, paths_seen)
        }
        Module::Ident(path) => {
            let env = QueryEnv::from_file(file);
            let find = |env: QueryEnv, name: &str| {
                let stamp = env.exported.find(ExportedKind::Module, name)?;
                let file = session.file(env.file);
                let md = file.stamps.find_module(stamp)?.clone();
                Some((file, Some(md)))
            };
            match resolve_path::from_compiler_path(file, &env, path) {
                Resolution::NotFound => None,
                Resolution::Exported(env, name) => find(env, &name),
                Resolution::Global(module_name, path) => {
                    let file = session.file_for_module(&module_name)?;
                    let (env, name) =
                        resolve_path::resolve_path(session, &QueryEnv::from_file(file), &path)?;
                    find(env, &name)
                }
                Resolution::Stamp(stamp) => {
                    let md = file.stamps.find_module(stamp)?;
                    match &md.item {
                        // Avoid possible infinite loops.
                        Module::Ident(path) if !paths_seen.contains(path) => {
                            let mut seen = vec![path.clone()];
                            seen.extend(paths_seen.iter().cloned());
                            resolve_module_reference(session, file, &md.clone(), &seen)
                        }
                        _ => Some((file, Some(md.clone()))),
                    }
                }
                Resolution::GlobalMod(name) => {
                    let file = session.file_for_module(&name)?;
                    Some((file, None))
                }
            }
        }
    }
}

/// `validate_loc`.
pub fn validate_loc(loc: Loc, backup: Loc) -> Loc {
    if loc.start.cnum == -1 {
        if backup.start.cnum == -1 {
            Loc {
                ghost: true,
                ..top_level_loc()
            }
        } else {
            backup
        }
    } else {
        loc
    }
}

/// `Uri.to_top_level_loc`.
pub fn top_level_loc() -> Loc {
    let pos = Pos {
        line: 1,
        bol: 0,
        cnum: 0,
    };
    Loc {
        start: pos,
        end: pos,
        ghost: false,
    }
}

/// `resolve_module_definition`.
fn resolve_module_definition(
    session: &ProjectSession<'_>,
    file: &File,
    stamp: i32,
) -> Option<(String, Loc)> {
    let md = file.stamps.find_module(stamp)?;
    // `file` may be the command's own module, which the session also holds.
    let file = session.file(file.module);
    let (file, declared) = resolve_module_reference(session, file, md, &[])?;
    let loc = match declared {
        None => top_level_loc(),
        Some(declared) => validate_loc(declared.name.loc, declared.extent_loc),
    };
    Some((file.uri.clone(), loc))
}

/// `definition`.
fn definition(
    session: &ProjectSession<'_>,
    file: &File,
    stamp: i32,
    tip: &Tip,
) -> Option<(String, Loc)> {
    match tip {
        Tip::Constructor(name) => Some((
            file.uri.clone(),
            get_constructor(file, stamp, name)?.cname.loc,
        )),
        Tip::Field(name) => Some((file.uri.clone(), get_field(file, stamp, name)?.fname.loc)),
        Tip::Module => resolve_module_definition(session, file, stamp),
        _ => {
            let declared = declared_for_tip(&file.stamps, stamp, tip)?;
            let (file_impl, declared_impl) = match alternate_declared(session, file, &declared, tip)
            {
                Some((full, declared_impl)) if uri::is_interface(&file.uri) => {
                    (&full.file, declared_impl)
                }
                _ => (file, declared),
            };
            let loc = validate_loc(declared_impl.name.loc, declared_impl.extent_loc);
            let env = QueryEnv::from_file(file_impl);
            let uri = resolve_path::get_source_uri(session, &env, &declared_impl.module_path);
            Some((uri, loc))
        }
    }
}

/// `definition_for_loc_item`.
pub fn definition_for_loc_item(
    session: &ProjectSession<'_>,
    full: &Loaded,
    loc_item: &LocItem,
) -> Option<(String, Loc)> {
    let file = &full.file;
    match &loc_item.loc_type {
        LocType::Typed(_, _, LocKind::Definition(stamp, tip)) => {
            let declared = declared_for_tip(&file.stamps, *stamp, tip)?;
            if declared.is_exported {
                let (full, declared) = alternate_declared(session, file, &declared, tip)?;
                let loc = validate_loc(declared.name.loc, declared.extent_loc);
                Some((full.file.uri.clone(), loc))
            } else {
                None
            }
        }
        LocType::Typed(_, _, LocKind::NotFound)
        | LocType::LModule(LocKind::NotFound | LocKind::Definition(..))
        | LocType::TypeDefinition(..)
        | LocType::Constant(_) => None,
        LocType::TopLevelModule(name) => {
            let paths = session.project().paths_for_module(name)?;
            let uri = paths.interface.or(paths.implementation)?;
            Some((uri.to_string_lossy().into_owned(), top_level_loc()))
        }
        LocType::LModule(LocKind::LocalReference(stamp, tip))
        | LocType::Typed(_, _, LocKind::LocalReference(stamp, tip)) => {
            definition(session, file, *stamp, tip)
        }
        LocType::LModule(LocKind::GlobalReference(module_name, path, tip))
        | LocType::Typed(_, _, LocKind::GlobalReference(module_name, path, tip)) => {
            let file = session.file_for_module(module_name)?;
            let env = QueryEnv::from_file(file);
            let (env, _, stamp) = exported_for_tip(session, &env, path, tip)?;
            definition(session, session.file(env.file), stamp, tip)
        }
    }
}

/// `dig_constructor`.
pub fn dig_constructor<'s>(
    session: &'s ProjectSession<'_>,
    env: &QueryEnv,
    path: &Path,
) -> Option<(QueryEnv, &'s Declared<Type>)> {
    match resolve_path::resolve_from_compiler_path(session, env, path) {
        Resolution::Stamp(stamp) => {
            let t = session.file(env.file).stamps.find_type(stamp)?;
            Some((env.clone(), t))
        }
        Resolution::Exported(env, name) => {
            let stamp = env.exported.find(ExportedKind::Type, &name)?;
            let t = session.file(env.file).stamps.find_type(stamp)?;
            Some((env, t))
        }
        _ => None,
    }
}

/// `type_definition_for_loc_item`.
pub fn type_definition_for_loc_item(
    session: &ProjectSession<'_>,
    full: &Loaded,
    loc_item: &LocItem,
) -> Option<(String, Loc)> {
    match &loc_item.loc_type {
        LocType::Constant(_) | LocType::TopLevelModule(_) | LocType::LModule(_) => None,
        LocType::TypeDefinition(..) => Some((full.file.uri.clone(), loc_item.loc)),
        LocType::Typed(_, typ, _) => {
            let env = QueryEnv::from_file(&full.file);
            let types = &full.source.typed.type_ctx;
            let path = match &*types.get_desc(dig(types, *typ)) {
                TypeDesc::Tconstr { path, .. } => path.clone(),
                _ => return None,
            };
            let (env, declared) = dig_constructor(session, &env, &path)?;
            Some((
                session.file(env.file).uri.clone(),
                Loc::of_location(
                    &session
                        .types(env.file)
                        .resolve_loc(declared.item.decl.type_loc),
                ),
            ))
        }
    }
}

/// `is_visible`.
fn is_visible(declared: &Declared<()>) -> bool {
    declared.is_exported && {
        let mut v = &declared.module_path;
        loop {
            match v {
                ModulePath::File { .. } => break true,
                ModulePath::NotVisible => break false,
                ModulePath::IncludedModule(_, inner) => v = inner,
                ModulePath::ExportedModule { module_path, .. } => v = module_path,
            }
        }
    }
}

/// `references`: a reference's file and location; `None` is the whole of a
/// toplevel module.
pub struct Reference {
    pub uri: String,
    pub loc: Option<Loc>,
}

fn local_stamp(file: &File, stamp: i32, tip: &Tip) -> Option<i32> {
    match tip {
        Tip::Constructor(name) => get_constructor(file, stamp, name).map(|c| c.stamp),
        Tip::Field(name) => get_field(file, stamp, name).map(|f| f.stamp),
        _ => Some(stamp),
    }
}

/// `for_local_stamp`.
fn for_local_stamp(
    session: &ProjectSession<'_>,
    full: &Loaded,
    stamp: i32,
    tip: &Tip,
) -> Vec<Reference> {
    let file = &full.file;
    let Some(local) = local_stamp(file, stamp, tip) else {
        return Vec::new();
    };
    let Some(locs) = full.extra.internal_references.find(&local) else {
        return Vec::new();
    };
    let externals = match declared_for_tip(&file.stamps, stamp, tip) {
        Some(declared) if is_visible(&declared) => {
            let mut alternative_references = Vec::new();
            if let Some((alt, alt_declared)) = alternate_declared(session, file, &declared, tip)
                && let Some(local) = local_stamp(&alt.file, alt_declared.stamp, tip)
                && let Some(locs) = alt.extra.internal_references.find(&local)
            {
                alternative_references.extend(locs.iter().rev().map(|loc| Reference {
                    uri: alt.file.uri.clone(),
                    loc: Some(*loc),
                }));
            }
            let path = declared.module_path.to_path(&declared.name.txt);
            let namespace = session.project().namespace();
            let (normalized_module_name, normalized_path) =
                normalize_external_reference_key(namespace.as_deref(), &file.module_name, path);
            let mut externals = Vec::new();
            for module_name in session.project().project_files() {
                if module_name == file.module_name {
                    continue;
                }
                for other in session.fulls_from_module(&module_name) {
                    if let Some(refs) = other
                        .extra
                        .external_references
                        .find(&normalized_module_name)
                    {
                        for (p, t, loc) in refs.iter().rev() {
                            if *p == normalized_path && t == tip {
                                externals.push(Reference {
                                    uri: other.file.uri.clone(),
                                    loc: Some(*loc),
                                });
                            }
                        }
                    }
                }
            }
            alternative_references.extend(externals);
            alternative_references
        }
        _ => Vec::new(),
    };
    let mut references: Vec<Reference> = locs
        .iter()
        .rev()
        .map(|loc| Reference {
            uri: file.uri.clone(),
            loc: Some(*loc),
        })
        .collect();
    references.extend(externals);
    references
}

/// `all_references_for_loc_item`.
pub fn all_references_for_loc_item(
    session: &ProjectSession<'_>,
    full: &Loaded,
    loc_item: &LocItem,
) -> Vec<Reference> {
    match &loc_item.loc_type {
        LocType::TopLevelModule(module_name) => {
            let mut other_modules_references = Vec::new();
            for name in session.project().project_files() {
                let Some(other) = session.full_from_module(&name) else {
                    continue;
                };
                if let Some(locs) = other.extra.file_references.find(module_name) {
                    for loc in locs {
                        other_modules_references.push(Reference {
                            uri: other.file.uri.clone(),
                            loc: Some(loc.0),
                        });
                    }
                }
            }
            let mut references: Vec<Reference> =
                match session.project().paths_for_module(module_name) {
                    None => Vec::new(),
                    Some(paths) => paths
                        .interface
                        .into_iter()
                        .chain(paths.implementation)
                        .map(|src| Reference {
                            uri: src.to_string_lossy().into_owned(),
                            loc: None,
                        })
                        .collect(),
                };
            references.extend(other_modules_references);
            references
        }
        LocType::Typed(_, _, LocKind::NotFound)
        | LocType::LModule(LocKind::NotFound)
        | LocType::Constant(_) => Vec::new(),
        LocType::TypeDefinition(_, _, stamp) => for_local_stamp(session, full, *stamp, &Tip::Type),
        LocType::Typed(
            _,
            _,
            LocKind::LocalReference(stamp, tip) | LocKind::Definition(stamp, tip),
        )
        | LocType::LModule(LocKind::LocalReference(stamp, tip) | LocKind::Definition(stamp, tip)) => {
            for_local_stamp(session, full, *stamp, tip)
        }
        LocType::LModule(LocKind::GlobalReference(module_name, path, tip))
        | LocType::Typed(_, _, LocKind::GlobalReference(module_name, path, tip)) => {
            let Some(file) = session.file_for_module(module_name) else {
                return Vec::new();
            };
            let env = QueryEnv::from_file(file);
            let Some((env, _, stamp)) = exported_for_tip(session, &env, path, tip) else {
                return Vec::new();
            };
            let module_name = session.file(env.file).module_name.clone();
            match session.full_from_module(&module_name) {
                None => Vec::new(),
                Some(full) => for_local_stamp(session, full, stamp, tip),
            }
        }
    }
}
