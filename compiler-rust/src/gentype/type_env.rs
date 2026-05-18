// Port of compiler/gentype/TypeEnv.ml:1-204 and TypeEnv.mli:1-23.
// This Stage 3 GenType port is intentionally not wired into the crate yet.

use std::cell::RefCell;
use std::rc::Rc;

use crate::gentype::gen_type_common::{Dep, StringMap, Type, dep_to_resolved_name, dep_to_string};
use crate::types::path::Path;
use crate::types::typedtree::TypedSignature;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleEquation {
    pub internal: bool,
    pub dep: Dep,
}

#[derive(Debug, Clone)]
pub struct TypeEnv {
    pub map: StringMap<Entry>,
    pub map_module_types: StringMap<(TypedSignature, crate::types::decl::Signature, T)>,
    pub module_equation: Option<ModuleEquation>,
    pub module_item: crate::gentype::runtime::ModuleItem,
    pub name: String,
    pub parent: Option<T>,
    pub type_equations: StringMap<Type>,
}

#[derive(Debug, Clone)]
pub enum Entry {
    Module(T),
    Type(String),
}

pub type T = Rc<RefCell<TypeEnv>>;

pub fn create_type_env(name: &str, parent: Option<T>) -> T {
    // Mirrors compiler/gentype/TypeEnv.ml:17-27.
    let module_item = crate::gentype::runtime::new_module_item(name);
    Rc::new(RefCell::new(TypeEnv {
        map: StringMap::new(),
        map_module_types: StringMap::new(),
        module_equation: None,
        module_item,
        name: name.to_string(),
        parent,
        type_equations: StringMap::new(),
    }))
}

pub fn root() -> T {
    // Mirrors compiler/gentype/TypeEnv.ml:29.
    create_type_env("__root__", None)
}

pub fn to_string(type_env: &T) -> String {
    // Mirrors compiler/gentype/TypeEnv.ml:30.
    type_env.borrow().name.clone()
}

pub fn new_module(name: &str, type_env: &T) -> T {
    // Mirrors compiler/gentype/TypeEnv.ml:32-37.
    if crate::gentype::debug::type_env.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "TypeEnv.newModule {} {}\n",
            to_string(type_env),
            name
        ));
    }
    let new_type_env = create_type_env(name, Some(type_env.clone()));
    type_env
        .borrow_mut()
        .map
        .insert(name.to_string(), Entry::Module(new_type_env.clone()));
    new_type_env
}

pub fn new_module_type(
    name: &str,
    signature: TypedSignature,
    signature_type: crate::types::decl::Signature,
    type_env: &T,
) -> T {
    // Mirrors compiler/gentype/TypeEnv.ml:39-45.
    // OCaml Typedtree.signature carries `sig_type`; Rust stores the typed
    // items and decl signature separately while preserving the same lookup
    // boundary for TranslateTypeExprFromTypes.ml:639-670.
    if crate::gentype::debug::type_env.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "TypeEnv.newModuleType {} {}\n",
            to_string(type_env),
            name
        ));
    }
    let new_type_env = create_type_env(name, Some(type_env.clone()));
    type_env.borrow_mut().map_module_types.insert(
        name.to_string(),
        (signature, signature_type, new_type_env.clone()),
    );
    new_type_env
}

pub fn new_type(name: &str, type_env: &T) {
    // Mirrors compiler/gentype/TypeEnv.ml:47-50.
    if crate::gentype::debug::type_env.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "TypeEnv.newType {} {}\n",
            to_string(type_env),
            name
        ));
    }
    type_env
        .borrow_mut()
        .map
        .insert(name.to_string(), Entry::Type(name.to_string()));
}

pub fn get_module(name: &str, type_env: &T) -> Option<T> {
    // Mirrors compiler/gentype/TypeEnv.ml:52-56.
    match type_env.borrow().map.get(name) {
        Some(Entry::Module(type_env1)) => Some(type_env1.clone()),
        Some(Entry::Type(_)) | None => None,
    }
}

pub fn expand_alias_to_external_module(name: &str, type_env: &T) -> Option<Dep> {
    // Mirrors compiler/gentype/TypeEnv.ml:58-65.
    match get_module(name, type_env) {
        Some(type_env1) => match &type_env1.borrow().module_equation {
            Some(ModuleEquation {
                internal: false,
                dep,
            }) => {
                if crate::gentype::debug::type_env.load(std::sync::atomic::Ordering::Relaxed) {
                    crate::gentype::log_::item(&format!(
                        "TypeEnv.expandAliasToExternalModule {} {} aliased to {}\n",
                        to_string(type_env),
                        name,
                        dep_to_string(dep)
                    ));
                }
                Some(dep.clone())
            }
            _ => None,
        },
        None => None,
    }
}

pub fn add_module_equation(dep: Dep, internal: bool, type_env: &T) {
    // Mirrors compiler/gentype/TypeEnv.ml:67-74.
    if crate::gentype::debug::type_env.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Typenv.addModuleEquation {} {} dep:{}\n",
            to_string(type_env),
            match internal {
                true => "Internal",
                false => "External",
            },
            dep_to_string(&dep)
        ));
    }
    type_env.borrow_mut().module_equation = Some(ModuleEquation { internal, dep });
}

pub fn add_type_equation(flattened: &[String], type_: Type, type_env: &T) -> T {
    // Mirrors compiler/gentype/TypeEnv.ml:76-94. OCaml uses record-copy here
    // rather than mutating type_env in place.
    match flattened {
        [name] => {
            let mut type_equations = type_env.borrow().type_equations.clone();
            type_equations.insert(name.clone(), type_);
            clone_with_type_equations(type_env, type_equations)
        }
        [module_name, rest @ ..] => match get_module(module_name, type_env) {
            Some(type_env1) => {
                let updated_type_env = add_type_equation(rest, type_, &type_env1);
                let mut map = type_env.borrow().map.clone();
                map.insert(module_name.clone(), Entry::Module(updated_type_env));
                clone_with_map(type_env, map)
            }
            None => type_env.clone(),
        },
        [] => type_env.clone(),
    }
}

pub fn add_type_equations(type_equations: &[(Vec<String>, Type)], type_env: &T) -> T {
    // Mirrors compiler/gentype/TypeEnv.ml:96-104. The OCaml input is
    // (Longident.t * type_) and calls Longident.flatten; the Rust integration
    // layer should pass the already-arena-resolved flattened path here.
    type_equations
        .iter()
        .fold(type_env.clone(), |te, (long_ident, type_)| {
            add_type_equation(long_ident, type_.clone(), &te)
        })
}

pub fn apply_type_equations(
    config: &crate::gentype::config::T,
    path: &Path,
    type_env: &T,
) -> Option<Type> {
    // Mirrors compiler/gentype/TypeEnv.ml:106-119.
    match path {
        Path::Pident(id) => match type_env.borrow().type_equations.get(id.name()) {
            Some(type_) => {
                if crate::gentype::debug::type_resolution.load(std::sync::atomic::Ordering::Relaxed)
                {
                    crate::gentype::log_::item(&format!(
                        "Typenv.applyTypeEquations {} name:{} type_:{}\n",
                        to_string(type_env),
                        id.name(),
                        crate::gentype::emit_type::type_to_string(config, &|_| false, type_)
                    ));
                }
                Some(type_.clone())
            }
            None => None,
        },
        _ => None,
    }
}

pub fn lookup(name: &str, type_env: &T) -> Option<T> {
    // Mirrors compiler/gentype/TypeEnv.ml:121-127.
    let has_name = type_env.borrow().map.contains_key(name);
    if has_name {
        Some(type_env.clone())
    } else {
        let parent = type_env.borrow().parent.clone();
        match parent {
            None => None,
            Some(parent) => lookup(name, &parent),
        }
    }
}

fn lookup_module_type(
    path: &[String],
    type_env: &T,
) -> Option<(TypedSignature, crate::types::decl::Signature, T)> {
    // Mirrors compiler/gentype/TypeEnv.ml:129-152.
    match path {
        [module_type_name] => {
            if crate::gentype::debug::type_env.load(std::sync::atomic::Ordering::Relaxed) {
                crate::gentype::log_::item(&format!(
                    "Typenv.lookupModuleType {} moduleTypeName:{}\n",
                    to_string(type_env),
                    module_type_name
                ));
            }
            let found = type_env
                .borrow()
                .map_module_types
                .get(module_type_name)
                .cloned();
            match found {
                Some(x) => Some(x),
                None => match type_env.borrow().parent.clone() {
                    None => None,
                    Some(parent) => lookup_module_type(path, &parent),
                },
            }
        }
        [module_name, path1 @ ..] => {
            if crate::gentype::debug::type_env.load(std::sync::atomic::Ordering::Relaxed) {
                crate::gentype::log_::item(&format!(
                    "Typenv.lookupModuleType {} moduleName:{}\n",
                    to_string(type_env),
                    module_name
                ));
            }
            let found = type_env.borrow().map.get(module_name).cloned();
            match found {
                Some(Entry::Module(type_env1)) => lookup_module_type(path1, &type_env1),
                Some(Entry::Type(_)) => None,
                None => match type_env.borrow().parent.clone() {
                    None => None,
                    Some(parent) => lookup_module_type(path, &parent),
                },
            }
        }
        [] => None,
    }
}

pub fn path_to_list(path: &Path) -> Vec<String> {
    // Mirrors compiler/gentype/TypeEnv.ml:154-158.
    match path {
        Path::Pident(id) => vec![id.name().to_string()],
        Path::Pdot(p, s, _) => {
            let mut out = vec![s.clone()];
            out.extend(path_to_list(p));
            out
        }
        Path::Papply(_, _) => vec![],
    }
}

pub fn lookup_module_type_signature(
    path: &Path,
    type_env: &T,
) -> Option<(TypedSignature, crate::types::decl::Signature, T)> {
    // Mirrors compiler/gentype/TypeEnv.ml:160-164.
    if crate::gentype::debug::type_env.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "TypeEnv.lookupModuleTypeSignature {} {}\n",
            to_string(type_env),
            path.name()
        ));
    }
    let mut path = path_to_list(path);
    path.reverse();
    lookup_module_type(&path, type_env)
}

pub fn update_module_item(module_item: crate::gentype::runtime::ModuleItem, type_env: &T) {
    // Mirrors compiler/gentype/TypeEnv.ml:166-167.
    type_env.borrow_mut().module_item = module_item;
}

pub fn add_module_path(type_env: &T, name: &str) -> crate::gentype::resolved_name::T {
    // Mirrors compiler/gentype/TypeEnv.ml:169-173.
    match &type_env.borrow().parent {
        None => crate::gentype::resolved_name::from_string(name),
        Some(parent) => {
            let parent_path = add_module_path(parent, &type_env.borrow().name);
            crate::gentype::resolved_name::dot(name, &parent_path)
        }
    }
}

pub fn get_module_equations(type_env: &T) -> Vec<crate::gentype::resolved_name::Eq> {
    // Mirrors compiler/gentype/TypeEnv.ml:175-190.
    let sub_equations = type_env
        .borrow()
        .map
        .values()
        .flat_map(|entry| match entry {
            Entry::Module(te) => get_module_equations(te),
            Entry::Type(_) => Vec::new(),
        })
        .collect::<Vec<_>>();

    match (
        type_env.borrow().module_equation.clone(),
        type_env.borrow().parent.clone(),
    ) {
        (Some(ModuleEquation { dep, .. }), Some(parent)) => vec![(
            dep_to_resolved_name(&dep),
            add_module_path(&parent, &type_env.borrow().name),
        )],
        _ => sub_equations,
    }
}

pub fn get_module_access_path(
    name: &str,
    type_env: &T,
) -> crate::gentype::runtime::ModuleAccessPath {
    // Mirrors compiler/gentype/TypeEnv.ml:192-204.
    fn access_path(type_env: &T, name: &str) -> crate::gentype::runtime::ModuleAccessPath {
        match &type_env.borrow().parent {
            None => crate::gentype::runtime::ModuleAccessPath::Root(name.to_string()),
            Some(parent) => {
                let parent_access_path = match parent.borrow().parent.is_none() {
                    true => crate::gentype::runtime::ModuleAccessPath::Root(
                        type_env.borrow().name.clone(),
                    ),
                    false => access_path(parent, name),
                };
                crate::gentype::runtime::ModuleAccessPath::Dot(
                    Box::new(parent_access_path),
                    type_env.borrow().module_item.clone(),
                )
            }
        }
    }

    access_path(type_env, name)
}

fn clone_with_type_equations(type_env: &T, type_equations: StringMap<Type>) -> T {
    let mut cloned = type_env.borrow().clone();
    cloned.type_equations = type_equations;
    Rc::new(RefCell::new(cloned))
}

fn clone_with_map(type_env: &T, map: StringMap<Entry>) -> T {
    let mut cloned = type_env.borrow().clone();
    cloned.map = map;
    Rc::new(RefCell::new(cloned))
}
