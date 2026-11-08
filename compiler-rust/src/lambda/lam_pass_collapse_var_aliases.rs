//! Port of `compiler/core/lam_pass_collapse_var_aliases.ml`: drop each
//! `let x = y` alias binding and use its target in its place.

use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_compat::LetKind;

fn resolve(tbl: &HashMap<Ident, Ident>, id: &Ident) -> Ident {
    let mut id = id;
    while let Some(next) = tbl.get(id) {
        id = next;
    }
    *id
}

/// `Lam_pass_collapse_var_aliases.collapse ~exports lam`.
pub fn collapse(a: &mut LamArena, lam: Lam, exports: &HashSet<Ident>) -> Lam {
    let mut tbl = HashMap::new();
    go(a, lam, exports, &mut tbl)
}

fn go(
    a: &mut LamArena,
    lam: Lam,
    exports: &HashSet<Ident>,
    tbl: &mut HashMap<Ident, Ident>,
) -> Lam {
    match a.node(lam) {
        Node::Var(x) => {
            let x = a.ident(x);
            let resolved = resolve(tbl, &x);
            if resolved == x { lam } else { a.var(resolved) }
        }
        Node::Let {
            kind: LetKind::Alias,
            id,
            value,
            body,
        } if matches!(a.node(value), Node::Var(_)) => {
            let id = a.ident(id);
            let u = resolve(tbl, &a.as_var(value).expect("checked variable"));
            tbl.insert(id, u);
            // The binding is dropped unless the name is exported, in which
            // case it has to survive under its own name.
            let body = go(a, body, exports, tbl);
            if exports.contains(&id) {
                let v = a.var(u);
                a.let_(LetKind::Alias, id, v, body)
            } else {
                body
            }
        }
        _ => a.shallow_map(lam, &mut |a, child| go(a, child, exports, tbl)),
    }
}
