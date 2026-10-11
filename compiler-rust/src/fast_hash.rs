//! Hash maps and sets for the compiler's own tables.
//!
//! `ahash::AHashMap::new()` builds a fresh `ahash::RandomState` per map: a
//! call into the global random source plus four hasher rounds to derive the
//! keys. The compiler creates millions of short-lived maps (copy caches,
//! per-call visited sets), so that setup showed up as a measurable share of
//! the build. These drop-in types hash with the same `AHasher`, keyed from
//! fixed seeds, so creating a map costs nothing. Iteration order was already
//! unspecified (seeds differed per map), so no caller may depend on it.

use std::borrow::Borrow;
use std::collections::{hash_map, hash_set};
use std::hash::{BuildHasher, Hash};
use std::ops::{Deref, DerefMut, Index};

static FIXED: ahash::RandomState = ahash::RandomState::with_seeds(
    0x243f_6a88_85a3_08d3,
    0x1319_8a2e_0370_7344,
    0xa409_3822_299f_31d0,
    0x082e_fa98_ec4e_6c89,
);

/// Zero-sized `BuildHasher` producing `AHasher`s from fixed keys.
#[derive(Clone, Copy, Default, Debug)]
pub struct FastState;

impl BuildHasher for FastState {
    type Hasher = ahash::AHasher;

    #[inline]
    fn build_hasher(&self) -> ahash::AHasher {
        FIXED.build_hasher()
    }
}

/// `HashMap` keyed with [`FastState`]; API-compatible with `ahash::AHashMap`.
#[derive(Clone)]
pub struct AHashMap<K, V>(std::collections::HashMap<K, V, FastState>);

impl<K: serde::Serialize, V: serde::Serialize> serde::Serialize for AHashMap<K, V> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self.0.iter())
    }
}

impl<'de, K, V> serde::Deserialize<'de> for AHashMap<K, V>
where
    K: serde::Deserialize<'de> + Eq + std::hash::Hash,
    V: serde::Deserialize<'de>,
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let map = std::collections::HashMap::<K, V>::deserialize(deserializer)?;
        Ok(AHashMap(map.into_iter().collect()))
    }
}

/// `HashSet` keyed with [`FastState`]; API-compatible with `ahash::AHashSet`.
#[derive(Clone)]
pub struct AHashSet<T>(std::collections::HashSet<T, FastState>);

impl<K, V> AHashMap<K, V> {
    #[inline]
    pub fn new() -> Self {
        AHashMap(std::collections::HashMap::with_hasher(FastState))
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        AHashMap(std::collections::HashMap::with_capacity_and_hasher(
            capacity, FastState,
        ))
    }
}

impl<T> AHashSet<T> {
    #[inline]
    pub fn new() -> Self {
        AHashSet(std::collections::HashSet::with_hasher(FastState))
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        AHashSet(std::collections::HashSet::with_capacity_and_hasher(
            capacity, FastState,
        ))
    }
}

impl<K, V> AHashMap<K, V> {
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hasher: FastState) -> Self {
        AHashMap(std::collections::HashMap::with_capacity_and_hasher(
            capacity, hasher,
        ))
    }

    #[inline]
    pub fn into_values(self) -> hash_map::IntoValues<K, V> {
        self.0.into_values()
    }

    #[inline]
    pub fn into_keys(self) -> hash_map::IntoKeys<K, V> {
        self.0.into_keys()
    }

    #[inline]
    pub fn into_inner(self) -> std::collections::HashMap<K, V, FastState> {
        self.0
    }
}

// Inherent forwarding methods (as in `ahash::AHashMap`) so that calls such
// as `map.insert(k, self.compute())` keep two-phase borrows, which do not
// apply through `DerefMut`.
impl<K: Eq + Hash, V> AHashMap<K, V> {
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.0.insert(key, value)
    }

    #[inline]
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.remove(key)
    }

    #[inline]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.get(key)
    }

    #[inline]
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.get_mut(key)
    }

    #[inline]
    pub fn entry(&mut self, key: K) -> hash_map::Entry<'_, K, V> {
        self.0.entry(key)
    }
}

impl<T: Eq + Hash> AHashSet<T> {
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hasher: FastState) -> Self {
        AHashSet(std::collections::HashSet::with_capacity_and_hasher(
            capacity, hasher,
        ))
    }

    #[inline]
    pub fn insert(&mut self, value: T) -> bool {
        self.0.insert(value)
    }

    #[inline]
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.remove(value)
    }

    #[inline]
    pub fn into_inner(self) -> std::collections::HashSet<T, FastState> {
        self.0
    }
}

impl<K, V> Default for AHashMap<K, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Default for AHashSet<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Deref for AHashMap<K, V> {
    type Target = std::collections::HashMap<K, V, FastState>;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, V> DerefMut for AHashMap<K, V> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> Deref for AHashSet<T> {
    type Target = std::collections::HashSet<T, FastState>;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for AHashSet<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K: std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug for AHashMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for AHashSet<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<K: Eq + Hash, V: PartialEq> PartialEq for AHashMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K: Eq + Hash, V: Eq> Eq for AHashMap<K, V> {}

impl<T: Eq + Hash> PartialEq for AHashSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Eq + Hash> Eq for AHashSet<T> {}

impl<K, Q, V> Index<&Q> for AHashMap<K, V>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash + ?Sized,
{
    type Output = V;
    #[inline]
    fn index(&self, key: &Q) -> &V {
        self.0.index(key)
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for AHashMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        AHashMap(std::collections::HashMap::from_iter(iter))
    }
}

impl<T: Eq + Hash> FromIterator<T> for AHashSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        AHashSet(std::collections::HashSet::from_iter(iter))
    }
}

impl<K: Eq + Hash, V> Extend<(K, V)> for AHashMap<K, V> {
    #[inline]
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<'a, K: Eq + Hash + Copy + 'a, V: Copy + 'a> Extend<(&'a K, &'a V)> for AHashMap<K, V> {
    #[inline]
    fn extend<I: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<T: Eq + Hash> Extend<T> for AHashSet<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<'a, T: Eq + Hash + Copy + 'a> Extend<&'a T> for AHashSet<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<K, V> IntoIterator for AHashMap<K, V> {
    type Item = (K, V);
    type IntoIter = hash_map::IntoIter<K, V>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a AHashMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = hash_map::Iter<'a, K, V>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut AHashMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = hash_map::IterMut<'a, K, V>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<T> IntoIterator for AHashSet<T> {
    type Item = T;
    type IntoIter = hash_set::IntoIter<T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a AHashSet<T> {
    type Item = &'a T;
    type IntoIter = hash_set::Iter<'a, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<K: Eq + Hash, V, const N: usize> From<[(K, V); N]> for AHashMap<K, V> {
    fn from(entries: [(K, V); N]) -> Self {
        entries.into_iter().collect()
    }
}

impl<T: Eq + Hash, const N: usize> From<[T; N]> for AHashSet<T> {
    fn from(items: [T; N]) -> Self {
        items.into_iter().collect()
    }
}
