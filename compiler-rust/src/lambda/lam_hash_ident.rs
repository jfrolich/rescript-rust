//! OCaml `Hash_ident` traversal order.
//!
//! `Lam_beta_reduce_util.simple_beta_reduce` folds over a native
//! `Hash_ident` table (compiler/core/lam_beta_reduce_util.ml), whose bucket
//! order depends on OCaml's `Hashtbl.hash` of each identifier and on the
//! table's retained capacity. This module reproduces that order so Rust
//! sequences unused arguments exactly as OCaml does.

use crate::ident::Ident;

fn mix(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h.rotate_left(13).wrapping_mul(5).wrapping_add(0xe6546b64)
}
fn finish(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h & 0x3fff_ffff
}
fn ident_hash(id: &Ident) -> u32 {
    if id.stamp() != 0 {
        // The native C stub's `MIX(h, d)` receives OCaml's tagged 64-bit
        // `value d`; its macro shifts/multiplies that width before truncating
        // into the 32-bit accumulator.
        let mut tagged = (id.stamp() as u64).wrapping_mul(2).wrapping_add(1);
        tagged = tagged.wrapping_mul(0xcc9e2d51);
        tagged = (tagged << 15) | (tagged >> 17);
        tagged = tagged.wrapping_mul(0x1b873593);
        let mut h = tagged as u32;
        h = h.rotate_left(13);
        h = h.wrapping_mul(5).wrapping_add(0xe6546b64);
        return finish(h);
    }
    let bytes = id.name().as_bytes();
    let mut h = 0;
    let mut i = 0;
    while i + 4 <= bytes.len() {
        h = mix(
            h,
            u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]),
        );
        i += 4;
    }
    if i < bytes.len() {
        let mut word = 0;
        for (shift, byte) in bytes[i..].iter().enumerate() {
            word |= (*byte as u32) << (shift * 8);
        }
        h = mix(h, word);
    }
    finish(h ^ bytes.len() as u32)
}

/// Reproduces `Hash_ident` bucket traversal, including retained resize capacity.
pub(crate) fn reference_fold_order(params: &[Ident], capacity: &mut usize) -> Vec<usize> {
    let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); (*capacity).max(32).next_power_of_two()];
    for (entry, id) in params.iter().enumerate() {
        let bucket = (ident_hash(id) as usize) & (buckets.len() - 1);
        buckets[bucket].insert(0, entry);
        if entry + 1 > buckets.len() << 1 {
            let mut resized = vec![Vec::new(); buckets.len() * 2];
            for old in &buckets {
                for &index in old {
                    let bucket = (ident_hash(&params[index]) as usize) & (resized.len() - 1);
                    resized[bucket].push(index);
                }
            }
            buckets = resized;
        }
    }
    *capacity = buckets.len();
    buckets.into_iter().flatten().collect()
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;

    fn ids(start: i32, count: usize) -> Vec<Ident> {
        (0..count)
            .map(|i| Ident::new(format!("p{i}"), start + i as i32, IdentFlags::NONE))
            .collect()
    }

    #[test]
    fn hash_ident_fold_order_preserves_collisions_resize_and_clear_capacity() {
        let mut capacity = 32;
        assert_eq!(
            reference_fold_order(&ids(1, 6), &mut capacity),
            vec![3, 1, 5, 2, 4, 0]
        );
        let expected = vec![
            13, 65, 0, 32, 50, 3, 42, 58, 57, 64, 39, 28, 34, 49, 4, 30, 25, 23, 20, 1, 61, 69, 8,
            6, 37, 47, 18, 38, 46, 5, 9, 66, 60, 52, 55, 56, 54, 31, 59, 14, 16, 53, 45, 63, 27,
            29, 21, 24, 11, 44, 12, 40, 36, 33, 10, 62, 48, 51, 35, 68, 26, 22, 15, 67, 43, 41, 2,
            19, 17, 7,
        ];
        assert_eq!(reference_fold_order(&ids(7, 70), &mut capacity), expected);
        assert_eq!(capacity, 64);
        assert_eq!(
            reference_fold_order(&ids(77, 6), &mut capacity),
            vec![0, 2, 4, 5, 1, 3]
        );
    }
}
