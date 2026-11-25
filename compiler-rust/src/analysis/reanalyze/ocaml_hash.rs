//! OCaml's `Hashtbl.hash` and the order `Hashtbl` iterates in
//! (runtime/hash.c, stdlib/hashtbl.ml).
//!
//! The OCaml tool iterates hash tables in two places whose order shows in
//! its output: the function table of the termination analysis, whose order
//! is the order errors are reported in, and a file's declarations, whose
//! order is the order of some debug lines. Reproducing those outputs needs
//! the same hashes and the same bucket layout.

/// `MIX` of runtime/hash.c.
fn mix(h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e_2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b87_3593);
    let h = (h ^ d).rotate_left(13);
    h.wrapping_mul(5).wrapping_add(0xe654_6b64)
}

/// `FINAL_MIX`, kept to the 30 bits `caml_hash` returns.
fn finish(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85eb_ca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2_ae35);
    h ^= h >> 16;
    h & 0x3fff_ffff
}

/// `caml_hash_mix_string`.
fn mix_string(mut h: u32, s: &str) -> u32 {
    let bytes = s.as_bytes();
    let mut chunks = bytes.chunks_exact(4);
    for chunk in &mut chunks {
        h = mix(
            h,
            u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]),
        );
    }
    let rest = chunks.remainder();
    if !rest.is_empty() {
        let mut w = 0u32;
        for (i, byte) in rest.iter().enumerate() {
            w |= u32::from(*byte) << (8 * i);
        }
        h = mix(h, w);
    }
    h ^ bytes.len() as u32
}

/// `Hashtbl.hash` of a string.
pub fn hash_string(s: &str) -> u32 {
    finish(mix_string(0, s))
}

/// `caml_hash_mix_intnat` of the integer `n`, which OCaml represents as
/// `2n + 1`.
fn mix_int(h: u32, n: i64) -> u32 {
    let tagged = n.wrapping_mul(2).wrapping_add(1);
    mix(h, ((tagged >> 32) ^ (tagged >> 63) ^ tagged) as u32)
}

/// The header of a block of `fields` fields with tag 0, as `caml_hash`
/// mixes it: `wosize << 10 | tag`.
fn mix_block(h: u32, fields: u32) -> u32 {
    mix(h, fields << 10)
}

/// `Hashtbl.hash` of the pair `(n, s)`: the block's header, then its
/// fields.
pub fn hash_int_string(n: i64, s: &str) -> u32 {
    let h = mix_int(mix_block(0, 2), n);
    finish(mix_string(h, s))
}

/// `Hashtbl.hash` of a `Lexing.position`: the record's header, then its
/// fields `pos_fname`, `pos_lnum`, `pos_bol` and `pos_cnum`.
pub fn hash_position(fname: &str, lnum: i64, bol: i64, cnum: i64) -> u32 {
    let h = mix_string(mix_block(0, 4), fname);
    finish(mix_int(mix_int(mix_int(h, lnum), bol), cnum))
}

/// The number of buckets of a table created with `initial` buckets (a power
/// of two, at least 16) after `keys` distinct keys were added: it doubles
/// whenever it holds more than two keys per bucket.
fn bucket_count(initial: usize, keys: usize) -> usize {
    let mut buckets = initial;
    for count in 1..=keys {
        if count > buckets * 2 {
            buckets *= 2;
        }
    }
    buckets
}

/// The order `Hashtbl.iter` and `Hashtbl.fold` visit the distinct keys of a
/// table created with `initial` buckets, as indices into `hashes`, the
/// hashes of the keys in the order they were added: bucket by bucket, the
/// latest key of a bucket first. Growing a table keeps each bucket's order,
/// so only the final bucket count matters.
pub fn iteration_order(initial: usize, hashes: &[u32]) -> Vec<usize> {
    let buckets = bucket_count(initial, hashes.len());
    let mut order: Vec<usize> = (0..hashes.len()).collect();
    order.sort_by_key(|i| (hashes[*i] as usize & (buckets - 1), std::cmp::Reverse(*i)));
    order
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strings_hash_as_in_ocaml() {
        // `Hashtbl.hash` of each string.
        for (s, hash) in [
            ("", 0),
            ("a", 721651713),
            ("ab", 856662637),
            ("abc", 767105082),
            ("abcd", 65890154),
            ("abcde", 335633756),
            ("alwaysLoop", 1064116890),
            ("parseList$loop", 961654741),
            ("testParametricFunction2", 382332246),
            ("callParseFunction", 927326645),
        ] {
            assert_eq!(hash_string(s), hash, "{s}");
        }
    }

    #[test]
    fn pairs_hash_as_in_ocaml() {
        // `Hashtbl.hash` of each pair.
        for ((n, s), hash) in [
            ((0, ""), 712711699),
            ((1, "a"), 973911938),
            ((123, "foo.res"), 956550293),
            ((4567, "record_rest_test.res"), 558671339),
            ((-1, "_none_"), 176399562),
            ((1000000, "DeadTest.res"), 999571564),
        ] {
            assert_eq!(hash_int_string(n, s), hash, "({n}, {s})");
        }
    }

    #[test]
    fn positions_hash_as_in_ocaml() {
        // `Hashtbl.hash` of each `Lexing.position`.
        for ((fname, lnum, bol, cnum), hash) in [
            (("", 0, 0, 0), 868769750),
            (("a.res", 1, 0, 4), 868784851),
            (("/home/user/project/src/a.res", 28, 512, 524), 1026493066),
            (("_none_", 1, 0, -1), 1053993565),
            (
                ("/x/y/Long_file_name_test.res", 1234, 56789, 56800),
                167124029,
            ),
        ] {
            assert_eq!(
                hash_position(fname, lnum, bol, cnum),
                hash,
                "{fname}:{lnum}"
            );
        }
    }

    #[test]
    fn string_keys_iterate_as_an_ocaml_hashtbl() {
        // `Hashtbl.iter` over a table created with `Hashtbl.create 1` that
        // these keys were added to in this order; 35 keys make it grow once.
        let keys: Vec<&str> = "f g h parseList parseListInt parseListListInt a1 a2 a3 b c d e \
                               x1 x2 x3 x4 x5 x6 x7 x8 x9 y1 y2 y3 y4 y5 y6 y7 y8 y9 z1 z2 z3 z4"
            .split_whitespace()
            .collect();
        let hashes: Vec<u32> = keys.iter().map(|key| hash_string(key)).collect();
        let order: Vec<&str> = iteration_order(16, &hashes)
            .into_iter()
            .map(|i| keys[i])
            .collect();
        assert_eq!(
            order.join(" "),
            "z2 y6 y1 h x2 a2 y3 y9 e b x6 x1 x5 z4 parseListListInt x4 a3 g x9 x7 z3 z1 y2 d x8 f x3 \
             parseListInt y5 a1 y4 y7 y8 parseList c"
        );
    }

    #[test]
    fn pair_keys_fold_as_an_ocaml_hashtbl() {
        // `Hashtbl.fold (fun _ v acc -> v :: acc) t []` over a table created
        // with 256 buckets holding `(i * 13, "g.res")` for `i` from 0 to 29:
        // the reverse of the order the table is visited in.
        let hashes: Vec<u32> = (0..30).map(|i| hash_int_string(i * 13, "g.res")).collect();
        let mut folded = iteration_order(256, &hashes);
        folded.reverse();
        assert_eq!(
            folded,
            [
                2, 15, 24, 16, 17, 26, 0, 27, 25, 11, 29, 14, 7, 6, 23, 12, 8, 13, 28, 10, 5, 9,
                19, 18, 20, 4, 3, 1, 21, 22
            ]
        );
        // 600 keys make the table grow once; the first 40 of the fold.
        let hashes: Vec<u32> = (0..600).map(|i| hash_int_string(i * 7, "f.res")).collect();
        let mut folded = iteration_order(256, &hashes);
        folded.reverse();
        assert_eq!(
            folded[..40],
            [
                198, 542, 487, 64, 156, 255, 371, 119, 1, 366, 387, 184, 219, 223, 330, 421, 83,
                374, 446, 551, 76, 598, 351, 462, 537, 82, 212, 220, 229, 101, 529, 546, 215, 257,
                272, 596, 153, 403, 126, 274
            ]
        );
    }
}
