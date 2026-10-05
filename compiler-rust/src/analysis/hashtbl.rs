//! OCaml's `Hashtbl` (stdlib hashtbl.ml, non-randomized) with `Hashtbl.hash`
//! (runtime/hash.c), so iteration order matches the OCaml analysis, whose
//! output order often follows a table's traversal.

/// `Hashtbl.hash` of a key.
pub trait OcamlHash {
    fn ocaml_hash(&self) -> u32;
}

fn mix_uint32(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h = h.rotate_left(13);
    h.wrapping_mul(5).wrapping_add(0xe6546b64)
}

fn final_mix(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h
}

/// `caml_hash_mix_intnat` on a 64-bit target.
fn mix_intnat(h: u32, d: i64) -> u32 {
    let n = (d >> 32) ^ (d >> 63) ^ d;
    mix_uint32(h, n as u32)
}

/// `caml_hash_mix_string` over the bytes a string stands for (source text
/// holds bytes as Latin-1 characters).
fn mix_string(mut h: u32, s: &str) -> u32 {
    let bytes: Vec<u8> = s
        .chars()
        .flat_map(|c| {
            if (c as u32) <= 0xFF {
                vec![c as u8]
            } else {
                let mut buf = [0u8; 4];
                c.encode_utf8(&mut buf).as_bytes().to_vec()
            }
        })
        .collect();
    let len = bytes.len();
    let mut i = 0;
    while i + 4 <= len {
        h = mix_uint32(h, u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]));
        i += 4;
    }
    let rem = len & 3;
    if rem != 0 {
        let mut w = 0u32;
        if rem >= 3 {
            w |= (bytes[i + 2] as u32) << 16;
        }
        if rem >= 2 {
            w |= (bytes[i + 1] as u32) << 8;
        }
        w |= bytes[i] as u32;
        h = mix_uint32(h, w);
    }
    h ^ len as u32
}

impl OcamlHash for i32 {
    fn ocaml_hash(&self) -> u32 {
        // An immediate is hashed as its tagged representation.
        final_mix(mix_intnat(0, 2 * (*self as i64) + 1)) & 0x3fff_ffff
    }
}

impl OcamlHash for String {
    fn ocaml_hash(&self) -> u32 {
        final_mix(mix_string(0, self)) & 0x3fff_ffff
    }
}

/// A `Hashtbl.t`. Each bucket keeps its head first.
#[derive(Clone, Debug)]
pub struct Hashtbl<K, V> {
    buckets: Vec<Vec<(K, V)>>,
    size: usize,
}

impl<K: OcamlHash + Eq, V> Hashtbl<K, V> {
    /// `Hashtbl.create n`.
    pub fn create(n: usize) -> Self {
        let mut len = 16;
        while len < n {
            len *= 2;
        }
        Hashtbl {
            buckets: (0..len).map(|_| Vec::new()).collect(),
            size: 0,
        }
    }

    fn index(&self, key: &K) -> usize {
        key.ocaml_hash() as usize & (self.buckets.len() - 1)
    }

    fn resize(&mut self) {
        let new_len = self.buckets.len() * 2;
        let mut buckets: Vec<Vec<(K, V)>> = (0..new_len).map(|_| Vec::new()).collect();
        // `insert_all_buckets ~inplace:true` keeps each bucket's order.
        for (key, value) in std::mem::take(&mut self.buckets).into_iter().flatten() {
            let i = key.ocaml_hash() as usize & (new_len - 1);
            buckets[i].push((key, value));
        }
        self.buckets = buckets;
    }

    /// `Hashtbl.add`: shadows earlier bindings of `key`.
    pub fn add(&mut self, key: K, value: V) {
        let i = self.index(&key);
        self.buckets[i].insert(0, (key, value));
        self.size += 1;
        if self.size > self.buckets.len() << 1 {
            self.resize();
        }
    }

    /// `Hashtbl.replace`.
    pub fn replace(&mut self, key: K, value: V) {
        let i = self.index(&key);
        match self.buckets[i].iter_mut().find(|(k, _)| *k == key) {
            Some(slot) => slot.1 = value,
            None => self.add(key, value),
        }
    }

    /// `Hashtbl.find_opt`: the most recent binding.
    pub fn find(&self, key: &K) -> Option<&V> {
        self.buckets[self.index(key)]
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v)
    }

    pub fn find_mut(&mut self, key: &K) -> Option<&mut V> {
        let i = self.index(key);
        self.buckets[i]
            .iter_mut()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v)
    }

    /// `Hashtbl.find_all`: most recent first.
    pub fn find_all(&self, key: &K) -> Vec<&V> {
        self.buckets[self.index(key)]
            .iter()
            .filter(|(k, _)| k == key)
            .map(|(_, v)| v)
            .collect()
    }

    pub fn mem(&self, key: &K) -> bool {
        self.find(key).is_some()
    }

    /// `Hashtbl.remove`: the most recent binding.
    pub fn remove(&mut self, key: &K) {
        let i = self.index(key);
        if let Some(pos) = self.buckets[i].iter().position(|(k, _)| k == key) {
            self.buckets[i].remove(pos);
            self.size -= 1;
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// The bindings in `Hashtbl.iter`/`Hashtbl.fold` order.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.buckets.iter().flatten().map(|(k, v)| (k, v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hashes_like_ocaml() {
        // `Hashtbl.hash 0`, `Hashtbl.hash 1`, `Hashtbl.hash "a"`, `Hashtbl.hash ""`
        // from OCaml 5.3.
        assert_eq!(0i32.ocaml_hash(), 129913994);
        assert_eq!(1i32.ocaml_hash(), 883721435);
        assert_eq!("a".to_string().ocaml_hash(), 721651713);
        assert_eq!(String::new().ocaml_hash(), 0);
        assert_eq!(1000i32.ocaml_hash(), 912777258);
    }

    #[test]
    fn iterates_like_ocaml() {
        let keys = [
            5, 1000, 3, 42, 7, 1001, 9, 100, 2, 77, 55, 31, 8, 13, 21, 34, 89, 144, 233, 377, 610, 987, 1597, 2584,
            4181, 6765, 10946, 17711, 28657, 46368, 75025, 121393, 196418, 317811,
        ];
        let mut t = Hashtbl::create(1);
        for k in keys {
            t.add(k, ());
        }
        let order: Vec<i32> = t.iter().map(|(k, _)| *k).collect();
        assert_eq!(
            order,
            [
                987, 2, 8, 28657, 34, 7, 13, 377, 31, 9, 17711, 1001, 1000, 42, 196418, 1597, 100, 2584, 89, 233,
                46368, 144, 121393, 610, 4181, 21, 3, 55, 5, 77, 6765, 317811, 75025, 10946
            ]
        );
    }
}
