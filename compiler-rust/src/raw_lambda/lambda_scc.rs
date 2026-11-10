//! Port of `compiler/ml/lambda_scc.ml`: split a syntactic `let rec` group
//! into its recursive clusters at Lambda production, demoting bindings that
//! are not recursive.

use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::LetKind;
use crate::lambda::arena::{LamArena, View};
use crate::raw_lambda::{RawArena, RawLambda};

type Bindings = Vec<(Ident, RawLambda)>;

/// OCaml `Lambda_scc.exists_var`: walk `l`, stopping as soon as `p` returns
/// true for a variable or assigned identifier.
fn exists_var(a: &LamArena, p: &mut impl FnMut(&Ident) -> bool, l: RawLambda) -> bool {
    match a.view(l) {
        View::Var(id) => return p(&id),
        View::Assign(id, _) if p(&id) => return true,
        _ => {}
    }
    let mut found = false;
    a.iter_children(l, |child| {
        found = found || exists_var(a, p, child);
    });
    found
}

/// OCaml `Lambda_scc.preprocess_deps` (compiler/ml/lambda_scc.ml, upstream
/// #9153): for each binding, the indices of the group members its right hand
/// side refers to, in binding order. One `seen` array is shared by all bodies
/// (`seen[j] == i` once body `i` has referred to binding `j`), so finding the
/// edges costs the size of the bodies rather than the group size per body.
fn preprocess_deps(a: &LamArena, groups: &Bindings) -> Vec<Vec<usize>> {
    let len = groups.len();
    // `Hash_ident.replace index id i`: a repeated member keeps its last index.
    let mut index = AHashMap::with_capacity(len);
    for (i, (member, _)) in groups.iter().enumerate() {
        index.insert(*member, i);
    }
    let mut seen = vec![usize::MAX; len];
    groups
        .iter()
        .enumerate()
        .map(|(i, (_, lam))| {
            let mut found = Vec::new();
            // stop walking `lam` once it has referred to every binding
            exists_var(
                a,
                &mut |id: &Ident| match index.get(id) {
                    Some(&j) if seen[j] != i => {
                        seen[j] = i;
                        found.push(j);
                        found.len() == len
                    }
                    _ => false,
                },
                *lam,
            );
            found.sort_unstable();
            found
        })
        .collect()
}

/// OCaml `Ext_scc.graph` (compiler/ext/ext_scc.ml:39-96): Tarjan's algorithm
/// over integer nodes, emitting each cluster as the stack range from its root.
fn graph(e: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct State<'a> {
        e: &'a [Vec<usize>],
        index: usize,
        s: Vec<usize>,
        output: Vec<Vec<usize>>,
        on_stack: Vec<bool>,
        index_array: Vec<Option<usize>>,
        lowlink: Vec<usize>,
    }
    fn scc(st: &mut State<'_>, v: usize) {
        st.index += 1;
        let new_index = st.index;
        st.s.push(v);
        st.index_array[v] = Some(new_index);
        st.lowlink[v] = new_index;
        st.on_stack[v] = true;
        for &w in &st.e[v] {
            if st.index_array[w].is_none() {
                scc(st, w);
                st.lowlink[v] = st.lowlink[v].min(st.lowlink[w]);
            } else if st.on_stack[w] {
                st.lowlink[v] = st.lowlink[v].min(st.lowlink[w]);
            }
        }
        if Some(st.lowlink[v]) == st.index_array[v] {
            let mut last_index = st.s.len() - 1;
            while st.s[last_index] != v {
                st.on_stack[st.s[last_index]] = false;
                last_index -= 1;
            }
            st.on_stack[v] = false;
            let cluster = st.s.split_off(last_index);
            st.output.push(cluster);
        }
    }
    let n = e.len();
    let mut st = State {
        e,
        index: 0,
        s: Vec::new(),
        output: Vec::new(),
        on_stack: vec![false; n],
        index_array: vec![None; n],
        lowlink: vec![0; n],
    };
    for i in 0..n {
        if st.index_array[i].is_none() {
            scc(&mut st, i);
        }
    }
    st.output
}

/// OCaml `Lambda_scc.bind_rec`: split a syntactic `let rec` group into the
/// actual recursive clusters and demote bindings that are not recursive.
pub(crate) fn bind_rec(b: &RawArena, groups: Bindings, body: RawLambda) -> RawLambda {
    if let [(id, bind)] = groups.as_slice() {
        let recursive = exists_var(&b.get(), &mut |v: &Ident| id.same(v), *bind);
        return if recursive {
            b.letrec(&groups, body)
        } else {
            b.let_(LetKind::Strict, *id, *bind, body)
        };
    }
    let node_vec = preprocess_deps(&b.get(), &groups);
    let clusters = graph(&node_vec);
    if clusters.len() <= 1 {
        return b.letrec(&groups, body);
    }
    let mut slots: Vec<Option<(Ident, RawLambda)>> = groups.into_iter().map(Some).collect();
    clusters.into_iter().rev().fold(body, |acc, cluster| {
        let mut bindings: Bindings = cluster
            .iter()
            .map(|&i| slots[i].take().expect("each binding is in one cluster"))
            .collect();
        if let [base_key] = cluster.as_slice()
            && node_vec[*base_key].binary_search(base_key).is_err()
        {
            let (id, lam) = bindings.pop().expect("one binding");
            b.let_(LetKind::Strict, id, lam, acc)
        } else {
            b.letrec(&bindings, acc)
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::FunctionAttribute;

    fn function(b: &RawArena, param: &str, body: RawLambda) -> RawLambda {
        b.function_(
            1,
            &[Ident::create_local(param)],
            body,
            FunctionAttribute::default(),
            LamLoc::NONE,
        )
    }

    #[test]
    fn splits_a_group_into_its_recursive_clusters() {
        let find_end = Ident::create_local("find_end");
        let find_beg = Ident::create_local("find_beg");
        let b = RawArena::new();
        let (e, g) = (b.var(find_end), b.var(find_beg));
        let seq = b.seq(e, g);
        let find_end_fn = function(&b, "n", seq);
        let g = b.var(find_beg);
        let find_beg_fn = function(&b, "p", g);
        let e = b.var(find_end);
        let lam = bind_rec(
            &b,
            vec![(find_end, find_end_fn), (find_beg, find_beg_fn)],
            e,
        );
        let a = b.get();
        let View::LetRec(outer, _, inner) = a.view(lam) else {
            panic!("expected letrec")
        };
        assert!(matches!(outer, [id] if id.same(&find_beg)));
        let View::LetRec(inner_bindings, _, body) = a.view(inner) else {
            panic!("expected nested letrec")
        };
        assert!(matches!(inner_bindings, [id] if id.same(&find_end)));
        assert!(matches!(a.view(body), View::Var(id) if id.same(&find_end)));
    }

    #[derive(Debug, PartialEq)]
    enum Shape {
        Let(String),
        Rec(Vec<String>),
    }

    /// Mirrors upstream `tests/ounit_tests/ounit_lambda_scc_tests.ml`: split
    /// `bodies` (each binding with the members its body refers to, in order)
    /// and read the bindings back outermost first.
    fn bind(bodies: &[(&str, &[&str])]) -> Vec<Shape> {
        let group: Vec<(&str, Ident)> = bodies
            .iter()
            .map(|(name, _)| (*name, Ident::create_local(*name)))
            .collect();
        let id_of = |name: &str| group.iter().find(|(n, _)| *n == name).unwrap().1;
        let b = RawArena::new();
        let bindings = bodies
            .iter()
            .map(|(name, refs)| {
                let body = refs.iter().fold(b.unit(), |acc, r| {
                    let var = b.var(id_of(r));
                    b.seq(acc, var)
                });
                (id_of(name), body)
            })
            .collect();
        let unit = b.unit();
        let mut lam = bind_rec(&b, bindings, unit);
        let a = b.get();
        let mut shape = Vec::new();
        loop {
            match a.view(lam) {
                View::Let(_, id, _, rest) => {
                    shape.push(Shape::Let(id.name().to_string()));
                    lam = rest;
                }
                View::LetRec(ids, _, rest) => {
                    let mut names: Vec<String> =
                        ids.iter().map(|id| id.name().to_string()).collect();
                    names.sort();
                    shape.push(Shape::Rec(names));
                    lam = rest;
                }
                _ => return shape,
            }
        }
    }

    fn rec(names: &[&str]) -> Shape {
        Shape::Rec(names.iter().map(|n| n.to_string()).collect())
    }

    fn let_(name: &str) -> Shape {
        Shape::Let(name.to_string())
    }

    #[test]
    fn a_reference_stays_an_edge_when_an_earlier_body_had_it_too() {
        // `x` refers to `c` first; `b`'s edge to `c` must survive the shared
        // `seen` array, or the cycle b <-> c falls apart into two plain lets.
        assert_eq!(
            bind(&[("x", &["c"]), ("b", &["c"]), ("c", &["b"])]),
            vec![rec(&["b", "c"]), let_("x")]
        );
    }

    #[test]
    fn a_mixed_group_keeps_cycles_self_recursion_and_plain_lets_apart() {
        let result = bind(&[
            ("a", &["b"]),
            // a body referring to the same binding twice
            ("b", &["a", "a"]),
            ("c", &["a"]),
            ("d", &["d"]),
            ("e", &[]),
        ]);
        assert_eq!(result.len(), 4);
        let position = |item: &Shape| result.iter().position(|x| x == item).unwrap();
        for item in [rec(&["a", "b"]), let_("c"), rec(&["d"]), let_("e")] {
            position(&item);
        }
        assert!(position(&rec(&["a", "b"])) < position(&let_("c")));
    }

    #[test]
    fn a_body_that_refers_to_every_binding() {
        assert_eq!(
            bind(&[("a", &["a", "b", "c"]), ("b", &[]), ("c", &["b"])]),
            vec![let_("b"), let_("c"), rec(&["a"])]
        );
    }

    #[test]
    fn demotes_a_non_recursive_binding() {
        let f = Ident::create_local("f");
        let b = RawArena::new();
        let unit = b.unit();
        let func = function(&b, "x", unit);
        let var = b.var(f);
        let lam = bind_rec(&b, vec![(f, func)], var);
        assert!(matches!(
            b.get().view(lam),
            View::Let(LetKind::Strict, _, _, _)
        ));
    }
}
