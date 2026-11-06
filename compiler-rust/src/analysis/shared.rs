//! Type printing and type walking: a port of analysis/src/shared.ml,
//! print_type.ml and the type helpers of utils.ml.

use crate::ident::Ident;
use crate::types::decl::{RecStatus, TypeDeclaration};
use crate::types::path::PathView;
use crate::types::printtyp::{Printtyp, print_out_sig_item_doc_with, print_out_type_doc};
use crate::types::{Path, TypeContext, TypeDesc, TypeExprRef};

/// `Shared.dig`.
pub use super::process_cmt::dig;

/// `Shared.dig_constructor`.
pub fn dig_constructor(types: &TypeContext, t: TypeExprRef) -> Option<Path> {
    match &*types.get_desc(dig(types, t)) {
        TypeDesc::Tconstr { path, .. } => Some(path.clone()),
        _ => None,
    }
}

/// `Print_type.print_expr` (`Shared.type_to_string`).
pub fn type_to_string(types: &TypeContext, t: TypeExprRef, line_width: i32) -> String {
    let mut printtyp = Printtyp::new(types);
    printtyp.reset_and_mark_loops(t);
    let tree = printtyp.tree_of_typexp(false, t);
    print_out_type_doc(&tree).to_string(line_width)
}

/// `Print_type.print_decl` (`Shared.decl_to_string`).
pub fn decl_to_string(
    types: &TypeContext,
    name: &str,
    decl: &TypeDeclaration,
    rec_status: RecStatus,
    print_name_as_is: bool,
) -> String {
    let mut printtyp = Printtyp::new(types);
    let item = printtyp.tree_of_type_declaration(&Ident::create_local(name), decl, rec_status);
    print_out_sig_item_doc_with(&item, print_name_as_is).to_string(60)
}

/// `Shared.find_type_constructors` for types of one context, adding to
/// `paths` (in first-seen order, which is OCaml's `List.rev` of its consed
/// list).
pub fn find_type_constructors_in(types: &TypeContext, tel: &[TypeExprRef], paths: &mut Vec<Path>) {
    fn add_path(paths: &mut Vec<Path>, path: &Path) {
        if !paths.iter().any(|p| p.same(path)) {
            paths.push(path.clone());
        }
    }
    fn walk(types: &TypeContext, te: TypeExprRef, paths: &mut Vec<Path>) {
        match &*types.get_desc(te) {
            TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) | TypeDesc::Tpoly { body: t, .. } => {
                walk(types, *t, paths)
            }
            TypeDesc::Tconstr { path, args, .. } => {
                add_path(paths, path);
                for arg in args.iter() {
                    walk(types, *arg, paths);
                }
            }
            TypeDesc::Tarrow { args, ret } => {
                for arg in args.iter() {
                    walk(types, arg.typ, paths);
                }
                walk(types, *ret, paths);
            }
            TypeDesc::Ttuple(tel) => {
                for t in tel.iter() {
                    walk(types, *t, paths);
                }
            }
            _ => {}
        }
    }
    for t in tel {
        walk(types, *t, paths);
    }
}

/// `Utils.unwrap_if_option`.
pub fn unwrap_if_option(types: &TypeContext, t: TypeExprRef) -> TypeExprRef {
    match &*types.get_desc(t) {
        TypeDesc::Tlink(t1) | TypeDesc::Tsubst(t1) => unwrap_if_option(types, *t1),
        TypeDesc::Tpoly { body, vars } if vars.is_empty() => unwrap_if_option(types, *body),
        TypeDesc::Tconstr { path, args, .. }
            if path.as_pident().is_some_and(|id| id.name() == "option") && args.len() == 1 =>
        {
            args[0]
        }
        _ => t,
    }
}

/// `Shared_types.path_ident_to_string`.
pub fn path_ident_to_string(p: &Path) -> String {
    match p.view() {
        PathView::Pident(id) => id.name().to_string(),
        PathView::Pdot(next, id, _) => format!("{}.{}", path_ident_to_string(next), id),
        PathView::Papply(..) => String::new(),
    }
}

/// `Utils.is_uncurried_internal`.
pub fn is_uncurried_internal(path: &Path) -> bool {
    path.name().starts_with("Js.Fn.arity")
}

/// `Utils.cut_after_dash`.
pub fn cut_after_dash(s: &str) -> &str {
    match s.find('-') {
        Some(n) => &s[..n],
        None => s,
    }
}
