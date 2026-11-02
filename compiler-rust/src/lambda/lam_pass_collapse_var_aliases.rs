//! Port of `compiler/core/lam_pass_collapse_var_aliases.ml`: drop each
//! `let x = y` alias binding and use its target in its place.

use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::ident::Ident;
use crate::lambda::Lambda;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lambda_traverse::{Mapped, shallow_map_sharing};

fn resolve(tbl: &HashMap<Ident, Ident>, id: &Ident) -> Ident {
    let mut id = id;
    while let Some(next) = tbl.get(id) {
        id = next;
    }
    id.clone()
}

/// `Lam_pass_collapse_var_aliases.collapse ~exports lam`.
pub fn collapse(lam: Lambda, exports: &HashSet<Ident>) -> Lambda {
    let mut tbl = HashMap::new();
    go(lam, exports, &mut tbl).0
}

fn go(lam: Lambda, exports: &HashSet<Ident>, tbl: &mut HashMap<Ident, Ident>) -> Mapped {
    match lam {
        Lambda::Lvar(x) => {
            let resolved = resolve(tbl, &x);
            if resolved == x {
                (Lambda::Lvar(x), false)
            } else {
                (Lambda::var(resolved), true)
            }
        }
        Lambda::Llet(LetKind::Alias, id, value, body) if matches!(*value, Lambda::Lvar(_)) => {
            let Lambda::Lvar(u) = *value else {
                unreachable!()
            };
            let u = resolve(tbl, &u);
            tbl.insert(id.clone(), u.clone());
            // The binding is dropped unless the name is exported, in which
            // case it has to survive under its own name.
            if exports.contains(&id) {
                let body = go(*body, exports, tbl).0;
                (Lambda::let_(LetKind::Alias, id, Lambda::var(u), body), true)
            } else {
                (go(*body, exports, tbl).0, true)
            }
        }
        lam => shallow_map_sharing(lam, &mut |child| go(child, exports, tbl)),
    }
}
