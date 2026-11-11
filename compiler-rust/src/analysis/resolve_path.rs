//! A port of analysis/src/resolve_path.ml.

use super::shared_types::*;
use crate::types::Path;
use crate::types::path::PathView;

/// The modules a command can reach: OCaml's `state` plus `package`. Files
/// load lazily and stay put once loaded, so `&File`s stay valid across
/// further loads.
pub trait Session {
    /// The file loaded as session module `id`.
    fn file(&self, id: ModuleId) -> &File;
    /// `Process_cmt.file_for_module`.
    fn file_for_module(&self, module_name: &str) -> Option<&File>;
}

/// `resolution`.
#[derive(Debug, Clone)]
pub enum Resolution {
    /// A name exported by the module `env` describes.
    Exported(QueryEnv, String),
    /// A path into another module: that module's name and the path within it.
    Global(String, ModulePathList),
    /// A whole other module, by name.
    GlobalMod(String),
    /// The path could not be resolved.
    NotFound,
    /// A declaration in this file, by stamp.
    Stamp(i32),
}

/// What a path inside a module resolves to (OCaml's polymorphic variants).
#[derive(Debug, Clone)]
pub enum Found {
    /// The last name of the path, exported by the module `env` describes.
    Local(QueryEnv, String),
    /// A path into another module: that module's name and the full path within it.
    Global(String, ModulePathList),
}

/// `join_paths`.
fn join_paths(module_path: &Path, mut path: ModulePathList) -> (i32, String, ModulePathList) {
    match module_path.view() {
        PathView::Pident(ident) => (ident.stamp(), ident.name().to_string(), path),
        PathView::Papply(fn_path, _) => join_paths(fn_path, path),
        PathView::Pdot(inner, name, _) => {
            path.insert(0, name.to_string());
            join_paths(inner, path)
        }
    }
}

/// `make_path`. `file` is `env.file`.
fn make_path(file: &File, env: &QueryEnv, module_path: &Path) -> Resolution {
    match module_path.view() {
        PathView::Pident(ident) if ident.stamp() == 0 => {
            Resolution::GlobalMod(ident.name().to_string())
        }
        PathView::Pident(ident) => Resolution::Stamp(ident.stamp()),
        PathView::Papply(fn_path, _) => make_path(file, env, fn_path),
        PathView::Pdot(inner, name, _) => match join_paths(inner, vec![name.to_string()]) {
            (0, module_name, path) => Resolution::Global(module_name, path),
            (stamp, _, path) => {
                let res = file
                    .stamps
                    .find_module(stamp)
                    .and_then(|declared| find_in_module(file, env, &declared.item, path));
                match res {
                    None => Resolution::NotFound,
                    Some(Found::Local(env, name)) => Resolution::Exported(env, name),
                    Some(Found::Global(module_name, full_path)) => {
                        Resolution::Global(module_name, full_path)
                    }
                }
            }
        },
    }
}

/// `resolve_path_inner`. `file` is `env.file`.
pub fn resolve_path_inner(file: &File, env: &QueryEnv, path: &[String]) -> Option<Found> {
    match path {
        [] => None,
        [name] => Some(Found::Local(env.clone(), name.clone())),
        [sub_name, sub_path @ ..] => {
            let stamp = env.exported.find(ExportedKind::Module, sub_name)?;
            let declared = file.stamps.find_module(stamp)?;
            find_in_module(file, env, &declared.item, sub_path.to_vec())
        }
    }
}

/// `find_in_module`. `file` is `env.file`.
pub fn find_in_module(
    file: &File,
    env: &QueryEnv,
    module: &Module,
    path: ModulePathList,
) -> Option<Found> {
    match module {
        Module::Structure(structure) => {
            resolve_path_inner(file, &env.enter_structure(structure), &path)
        }
        Module::Constraint(_, module1) => find_in_module(file, env, module1, path),
        Module::Ident(module_path) => {
            let (stamp, module_name, full_path) = join_paths(module_path, path);
            if stamp == 0 {
                Some(Found::Global(module_name, full_path))
            } else {
                let declared = file.stamps.find_module(stamp)?;
                find_in_module(file, env, &declared.item, full_path)
            }
        }
    }
}

/// `resolve_path`.
pub fn resolve_path<S: Session + ?Sized>(
    session: &S,
    env: &QueryEnv,
    path: &[String],
) -> Option<(QueryEnv, String)> {
    match resolve_path_inner(session.file(env.file), env, path)? {
        Found::Local(env, name) => Some((env, name)),
        Found::Global(module_name, full_path) => {
            let file = session.file_for_module(&module_name)?;
            resolve_path(session, &QueryEnv::from_file(file), &full_path)
        }
    }
}

/// `from_compiler_path`. `file` is `env.file`.
pub fn from_compiler_path(file: &File, env: &QueryEnv, path: &Path) -> Resolution {
    make_path(file, env, path)
}

/// `resolve_module_from_compiler_path`.
pub fn resolve_module_from_compiler_path<S: Session + ?Sized>(
    session: &S,
    env: &QueryEnv,
    path: &Path,
) -> Option<(QueryEnv, Option<Declared<Module>>)> {
    let find = |env: QueryEnv, name: &str| {
        let stamp = env.exported.find(ExportedKind::Module, name)?;
        let declared = session.file(env.file).stamps.find_module(stamp)?.clone();
        Some((env, Some(declared)))
    };
    match from_compiler_path(session.file(env.file), env, path) {
        Resolution::Global(module_name, path) => {
            let file = session.file_for_module(&module_name)?;
            let (env, name) = resolve_path(session, &QueryEnv::from_file(file), &path)?;
            find(env, &name)
        }
        Resolution::Stamp(stamp) => {
            let declared = session.file(env.file).stamps.find_module(stamp)?.clone();
            Some((env.clone(), Some(declared)))
        }
        Resolution::GlobalMod(module_name) => {
            let file = session.file_for_module(&module_name)?;
            Some((QueryEnv::from_file(file), None))
        }
        Resolution::NotFound => None,
        Resolution::Exported(env, name) => find(env, &name),
    }
}

/// `resolve_from_compiler_path`.
pub fn resolve_from_compiler_path<S: Session + ?Sized>(
    session: &S,
    env: &QueryEnv,
    path: &Path,
) -> Resolution {
    match from_compiler_path(session.file(env.file), env, path) {
        Resolution::Global(module_name, path) => {
            let res = session
                .file_for_module(&module_name)
                .and_then(|file| resolve_path(session, &QueryEnv::from_file(file), &path));
            match res {
                None => Resolution::NotFound,
                Some((env, name)) => Resolution::Exported(env, name),
            }
        }
        Resolution::Stamp(stamp) => Resolution::Stamp(stamp),
        Resolution::GlobalMod(_) | Resolution::NotFound => Resolution::NotFound,
        Resolution::Exported(env, name) => Resolution::Exported(env, name),
    }
}

/// `get_source_uri`.
pub fn get_source_uri<S: Session + ?Sized>(
    session: &S,
    env: &QueryEnv,
    path: &ModulePath,
) -> String {
    match path {
        ModulePath::File { uri, .. } => uri.clone(),
        ModulePath::NotVisible => session.file(env.file).uri.clone(),
        ModulePath::IncludedModule(path, inner) => {
            match resolve_module_from_compiler_path(session, env, path) {
                None => get_source_uri(session, env, inner),
                Some((env, _)) => session.file(env.file).uri.clone(),
            }
        }
        ModulePath::ExportedModule { module_path, .. } => get_source_uri(session, env, module_path),
    }
}
