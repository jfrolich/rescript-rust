//! Port of `compiler/ml/lambda_scc.ml`: split a syntactic `let rec` group
//! into its recursive clusters at Lambda production, demoting bindings that
//! are not recursive.

use crate::ident::Ident;
use crate::lambda::LetKind;
use crate::raw_lambda::RawLambda;

type Bindings = Vec<(Ident, RawLambda)>;

/// OCaml `Lambda_scc.exists_var`: walk `l`, stopping as soon as `p` returns
/// true for a variable or assigned identifier.
fn exists_var(p: &mut impl FnMut(&Ident) -> bool, l: &RawLambda) -> bool {
    match l {
        RawLambda::Lshared(inner) => exists_var(p, inner),
        RawLambda::Lvar(id) => p(id),
        RawLambda::Lassign(id, e) => p(id) || exists_var(p, e),
        RawLambda::LstaticCatch(e1, _, e2)
        | RawLambda::LtryWith(e1, _, e2)
        | RawLambda::Lsequence(e1, e2)
        | RawLambda::Lwhile(e1, e2)
        | RawLambda::Lfor_of(_, e1, e2)
        | RawLambda::Lfor_await_of(_, e1, e2) => exists_var(p, e1) || exists_var(p, e2),
        RawLambda::Lfunction(f) => exists_var(p, &f.body),
        RawLambda::Llet(_, _, arg, body) => exists_var(p, arg) || exists_var(p, body),
        RawLambda::Lletrec(decl, body) => {
            exists_var(p, body) || decl.iter().any(|(_, lam)| exists_var(p, lam))
        }
        RawLambda::Lfor(_, e1, e2, _, e3) | RawLambda::LifThenElse(e1, e2, e3) => {
            exists_var(p, e1) || exists_var(p, e2) || exists_var(p, e3)
        }
        RawLambda::Lconst(_) | RawLambda::Lbreak | RawLambda::Lcontinue => false,
        RawLambda::Lapply(ap) => {
            exists_var(p, &ap.ap_func) || ap.ap_args.iter().any(|arg| exists_var(p, arg))
        }
        RawLambda::Lprim(info) => info.args.iter().any(|arg| exists_var(p, arg)),
        RawLambda::LstaticRaise(_, args) => args.iter().any(|arg| exists_var(p, arg)),
        RawLambda::Lswitch(arg, sw) => {
            exists_var(p, arg)
                || sw.sw_consts.iter().any(|(_, lam)| exists_var(p, lam))
                || sw.sw_blocks.iter().any(|(_, lam)| exists_var(p, lam))
                || sw
                    .sw_failaction
                    .as_deref()
                    .is_some_and(|lam| exists_var(p, lam))
        }
        RawLambda::LstringSwitch(arg, cases, default) => {
            exists_var(p, arg)
                || cases.iter().any(|(_, lam)| exists_var(p, lam))
                || default.as_deref().is_some_and(|lam| exists_var(p, lam))
        }
        RawLambda::LglobalModule(_) => false,
    }
}

/// OCaml `Lambda_scc.preprocess_deps`. Bindings are ranked in list order
/// (`Ordered_hash_map_local_ident`); each row lists the group members its
/// right hand side mentions, in `Hash_set_ident_mask.iter_and_unmask`
/// bucket order.
fn preprocess_deps(groups: &Bindings) -> Vec<Vec<usize>> {
    let mask_order = ocaml_ident_mask_iteration_order(groups);
    groups
        .iter()
        .map(|(_, lam)| {
            let mut hit = vec![false; groups.len()];
            let mut remaining = groups.len();
            exists_var(
                &mut |id: &Ident| {
                    if let Some(index) = groups.iter().position(|(member, _)| member.same(id))
                        && !hit[index]
                    {
                        hit[index] = true;
                        remaining -= 1;
                    }
                    remaining == 0
                },
                lam,
            );
            mask_order
                .iter()
                .copied()
                .filter(|index| hit[*index])
                .collect()
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
    fn scc(st: &mut State, v: usize) {
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
pub(crate) fn bind_rec(groups: Bindings, body: RawLambda) -> RawLambda {
    if let [(id, bind)] = groups.as_slice() {
        return if exists_var(&mut |v: &Ident| id.same(v), bind) {
            RawLambda::letrec(groups, body)
        } else {
            let (id, bind) = groups.into_iter().next().expect("one binding");
            RawLambda::let_(LetKind::Strict, id, bind, body)
        };
    }
    let node_vec = preprocess_deps(&groups);
    let clusters = graph(&node_vec);
    if clusters.len() <= 1 {
        return RawLambda::letrec(groups, body);
    }
    let mut slots: Vec<Option<(Ident, RawLambda)>> = groups.into_iter().map(Some).collect();
    clusters.into_iter().rev().fold(body, |acc, cluster| {
        let mut bindings: Bindings = cluster
            .iter()
            .map(|&i| slots[i].take().expect("each binding is in one cluster"))
            .collect();
        if let [base_key] = cluster.as_slice()
            && !node_vec[*base_key].contains(base_key)
        {
            let (id, lam) = bindings.pop().expect("one binding");
            RawLambda::let_(LetKind::Strict, id, lam, acc)
        } else {
            RawLambda::letrec(bindings, acc)
        }
    })
}

fn ocaml_ident_mask_iteration_order(bindings: &[(Ident, RawLambda)]) -> Vec<usize> {
    let bucket_len = ocaml_hashtbl_power_2_above(8, bindings.len());
    let mut buckets = vec![Vec::<usize>::new(); bucket_len];
    for (index, (id, _)) in bindings.iter().enumerate() {
        let bucket = (ocaml_hash_string_int(id.name(), id.stamp()) as usize) & (bucket_len - 1);
        buckets[bucket].insert(0, index);
    }
    buckets.into_iter().flatten().collect()
}

fn ocaml_hashtbl_power_2_above(mut x: usize, n: usize) -> usize {
    while x < n {
        x <<= 1;
    }
    x
}

fn ocaml_hash_string_int(s: &str, i: i32) -> u32 {
    let h = ocaml_hash_mix_string(0, s);
    ocaml_hash_final_mix(ocaml_hash_mix_uint32(h, ocaml_tagged_int_bits(i))) & 0x3fff_ffff
}

fn ocaml_tagged_int_bits(i: i32) -> u32 {
    ((i as u32) << 1) | 1
}

fn ocaml_hash_mix_string(mut h: u32, s: &str) -> u32 {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut i = 0usize;

    while i + 4 <= len {
        let word = u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        h = ocaml_hash_mix_uint32(h, word);
        i += 4;
    }

    let rem = len & 3;
    if rem != 0 {
        let mut word = 0u32;
        if rem >= 3 {
            word |= (bytes[i + 2] as u32) << 16;
        }
        if rem >= 2 {
            word |= (bytes[i + 1] as u32) << 8;
        }
        word |= bytes[i] as u32;
        h = ocaml_hash_mix_uint32(h, word);
    }

    h ^ (len as u32)
}

fn ocaml_hash_mix_uint32(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h = h.rotate_left(13);
    h = h.wrapping_mul(5).wrapping_add(0xe6546b64);
    h
}

fn ocaml_hash_final_mix(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::FunctionAttribute;

    fn function(param: &str, body: RawLambda) -> RawLambda {
        RawLambda::function_(
            1,
            vec![Ident::create_local(param)],
            body,
            FunctionAttribute::default(),
            crate::location::Location::none(),
        )
    }

    #[test]
    fn splits_a_group_into_its_recursive_clusters() {
        let find_end = Ident::create_local("find_end");
        let find_beg = Ident::create_local("find_beg");
        let lam = bind_rec(
            vec![
                (
                    find_end,
                    function(
                        "n",
                        RawLambda::seq(RawLambda::var(find_end), RawLambda::var(find_beg)),
                    ),
                ),
                (find_beg, function("p", RawLambda::var(find_beg))),
            ],
            RawLambda::var(find_end),
        );
        let RawLambda::Lletrec(outer, inner) = lam else {
            panic!("expected letrec")
        };
        assert!(matches!(outer.as_slice(), [(id, _)] if id.same(&find_beg)));
        let RawLambda::Lletrec(inner_bindings, body) = *inner else {
            panic!("expected nested letrec")
        };
        assert!(matches!(inner_bindings.as_slice(), [(id, _)] if id.same(&find_end)));
        assert!(matches!(*body, RawLambda::Lvar(ref id) if id.same(&find_end)));
    }

    #[test]
    fn demotes_a_non_recursive_binding() {
        let f = Ident::create_local("f");
        let lam = bind_rec(
            vec![(f, function("x", RawLambda::unit()))],
            RawLambda::var(f),
        );
        assert!(matches!(lam, RawLambda::Llet(LetKind::Strict, _, _, _)));
    }
}
