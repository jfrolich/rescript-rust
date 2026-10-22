// Port of compiler/gentype/ResolvedName.ml:1-59 and ResolvedName.mli:1-8.

use std::collections::BTreeSet;

pub type T = Vec<String>;
pub type Eq = (T, T);

pub fn dot(s: &str, x: &T) -> T {
    let mut out = x.clone();
    out.push(s.to_string());
    out
}

pub fn from_string(x: &str) -> T {
    vec![x.to_string()]
}

pub fn to_list(x: &T) -> Vec<String> {
    x.clone()
}

pub fn to_string(x: &T) -> String {
    x.join("_")
}

pub fn apply_equation(el: &[String], eq: &Eq) -> Vec<T> {
    fn go(el: &[String], lhs: &[String], rhs: &T) -> Vec<T> {
        match (lhs.split_first(), el.split_first()) {
            (None, _) => {
                let mut out = rhs.clone();
                out.extend(el.iter().cloned());
                vec![out]
            }
            (Some((s1, rest1)), Some((s2, rest2))) => match s1 == s2 {
                true => go(rest2, rest1, rhs),
                false => vec![],
            },
            (Some(_), None) => vec![],
        }
    }
    go(el, &eq.0, &eq.1)
}

pub fn apply_equations_to_elements(eqs: &[Eq], mut seen: BTreeSet<T>, elements: &[T]) -> Vec<Eq> {
    let apply_eqs = |el: &T| {
        let fresh_elements = eqs
            .iter()
            .flat_map(|eq| apply_equation(el, eq))
            .filter(|y| !seen.contains(y))
            .collect::<Vec<_>>();
        fresh_elements
            .into_iter()
            .map(|el_fresh| (el_fresh, el.clone()))
            .collect::<Vec<_>>()
    };

    let new_equations = elements.iter().flat_map(apply_eqs).collect::<Vec<_>>();
    let new_elements = new_equations
        .iter()
        .map(|(lhs, _)| lhs.clone())
        .collect::<Vec<_>>();
    seen.extend(new_elements.iter().cloned());

    match new_equations.is_empty() {
        true => new_equations,
        false => {
            let mut out = new_equations;
            out.extend(apply_equations_to_elements(eqs, seen, &new_elements));
            out
        }
    }
}

// Apply equations of the form e.g. X.Y = A from the alias: module A = X.Y.
// Return a list of equations on types.
// E.g. if the element is X.Y.t, return equation A.t = X.Y.t.
pub fn apply_equations(eqs: &[Eq], el: &T) -> Vec<Eq> {
    apply_equations_to_elements(eqs, BTreeSet::new(), std::slice::from_ref(el))
}
