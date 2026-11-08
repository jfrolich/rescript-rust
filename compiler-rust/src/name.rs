//! Interned identifier names.
//!
//! A [`Name`] is a pointer to a process-wide, never-freed copy of a string.
//! Every distinct string is interned once, so names compare by pointer, copy
//! as one word and read without a table lookup. The set of distinct
//! identifier names in a build is small, so the strings are kept for the life
//! of the process.
//!
//! Hashing and ordering use the string contents, never the address, so maps
//! keyed by names behave the same from run to run.

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use smol_str::SmolStr;
use std::borrow::Cow;
use std::cell::RefCell;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{LazyLock, Mutex};

struct NameData {
    /// Hash of `text`, computed once with fixed seeds.
    hash: u64,
    text: &'static str,
}

/// An interned string. See the module documentation.
#[derive(Clone, Copy)]
pub struct Name(&'static NameData);

const SHARDS: usize = 64;

type Table = ahash::AHashMap<&'static str, Name>;

fn content_hasher() -> ahash::RandomState {
    ahash::RandomState::with_seeds(
        0x6a09_e667_f3bc_c908,
        0xbb67_ae85_84ca_a73b,
        0x3c6e_f372_fe94_f82b,
        0xa54f_f53a_5f1d_36f1,
    )
}

static HASHER: LazyLock<ahash::RandomState> = LazyLock::new(content_hasher);

static GLOBAL: LazyLock<Box<[Mutex<Table>]>> =
    LazyLock::new(|| (0..SHARDS).map(|_| Mutex::new(Table::default())).collect());

thread_local! {
    /// Names this thread has already interned, so repeated lookups skip the
    /// shared table and its lock.
    static LOCAL: RefCell<Table> = RefCell::new(Table::default());
}

impl Name {
    /// Interns `text`.
    pub fn new(text: &str) -> Name {
        if let Ok(Some(name)) = LOCAL.try_with(|local| local.borrow().get(text).copied()) {
            return name;
        }
        let hash = HASHER.hash_one(text);
        let name = {
            let mut shard = GLOBAL[(hash as usize) % SHARDS]
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            match shard.get(text) {
                Some(&name) => name,
                None => {
                    let text: &'static str = Box::leak(text.to_owned().into_boxed_str());
                    let name = Name(Box::leak(Box::new(NameData { hash, text })));
                    shard.insert(text, name);
                    name
                }
            }
        };
        // Unavailable only while the thread is being torn down.
        let _ = LOCAL.try_with(|local| local.borrow_mut().insert(name.0.text, name));
        name
    }

    /// The name for `text` if it has been interned, without interning it.
    /// A table keyed by names cannot contain a string that was never
    /// interned, so a `None` here answers every lookup for `text`.
    pub fn lookup(text: &str) -> Option<Name> {
        if let Ok(Some(name)) = LOCAL.try_with(|local| local.borrow().get(text).copied()) {
            return Some(name);
        }
        let hash = HASHER.hash_one(text);
        let name = GLOBAL[(hash as usize) % SHARDS]
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(text)
            .copied()?;
        let _ = LOCAL.try_with(|local| local.borrow_mut().insert(name.0.text, name));
        Some(name)
    }

    /// Hash of the text, computed once with fixed seeds: the same in every
    /// run, unlike the address.
    #[inline]
    pub(crate) fn content_hash(self) -> u64 {
        self.0.hash
    }

    /// The interned string.
    #[inline]
    pub fn as_str(self) -> &'static str {
        self.0.text
    }
}

impl PartialEq for Name {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Eq for Name {}

impl Hash for Name {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.hash);
    }
}

impl Ord for Name {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            std::cmp::Ordering::Equal
        } else {
            self.as_str().cmp(other.as_str())
        }
    }
}

impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::ops::Deref for Name {
    type Target = str;
    #[inline]
    fn deref(&self) -> &str {
        self.0.text
    }
}

impl AsRef<str> for Name {
    #[inline]
    fn as_ref(&self) -> &str {
        self.0.text
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0.text, f)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.text)
    }
}

impl Default for Name {
    fn default() -> Self {
        Name::new("")
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        self.0.text == other
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool {
        self.0.text == *other
    }
}

impl PartialEq<String> for Name {
    fn eq(&self, other: &String) -> bool {
        self.0.text == other.as_str()
    }
}

impl PartialEq<SmolStr> for Name {
    fn eq(&self, other: &SmolStr) -> bool {
        self.0.text == other.as_str()
    }
}

impl PartialEq<Name> for str {
    fn eq(&self, other: &Name) -> bool {
        self == other.0.text
    }
}

impl PartialEq<Name> for &str {
    fn eq(&self, other: &Name) -> bool {
        *self == other.0.text
    }
}

impl From<&str> for Name {
    fn from(text: &str) -> Self {
        Name::new(text)
    }
}

impl From<&String> for Name {
    fn from(text: &String) -> Self {
        Name::new(text)
    }
}

impl From<String> for Name {
    fn from(text: String) -> Self {
        Name::new(&text)
    }
}

impl From<Box<str>> for Name {
    fn from(text: Box<str>) -> Self {
        Name::new(&text)
    }
}

impl From<Cow<'_, str>> for Name {
    fn from(text: Cow<'_, str>) -> Self {
        Name::new(&text)
    }
}

impl From<SmolStr> for Name {
    fn from(text: SmolStr) -> Self {
        Name::new(&text)
    }
}

impl From<&SmolStr> for Name {
    fn from(text: &SmolStr) -> Self {
        Name::new(text)
    }
}

impl From<&Name> for Name {
    fn from(name: &Name) -> Self {
        *name
    }
}

impl From<Name> for SmolStr {
    fn from(name: Name) -> Self {
        SmolStr::new(name.as_str())
    }
}

impl From<Name> for String {
    fn from(name: Name) -> Self {
        name.as_str().to_owned()
    }
}

impl Serialize for Name {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.0.text)
    }
}

impl<'de> Deserialize<'de> for Name {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let text = Cow::<'de, str>::deserialize(deserializer)?;
        Ok(Name::new(&text))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interning_is_shared_across_threads() {
        let a = Name::new("hello");
        let b = std::thread::spawn(|| Name::new("hello")).join().unwrap();
        assert_eq!(a, b);
        assert!(std::ptr::eq(a.as_str(), b.as_str()));
        assert_ne!(a, Name::new("world"));
        assert_eq!(a, "hello");
        assert_eq!(std::mem::size_of::<Name>(), 8);
    }

    #[test]
    fn lookup_does_not_intern() {
        assert_eq!(Name::lookup("name_lookup_never_interned_zq"), None);
        let name = Name::new("name_lookup_interned_zq");
        assert_eq!(Name::lookup("name_lookup_interned_zq"), Some(name));
        let other = std::thread::spawn(|| Name::lookup("name_lookup_interned_zq"))
            .join()
            .unwrap();
        assert_eq!(other, Some(name));
    }

    #[test]
    fn hash_and_order_follow_contents() {
        let a = Name::new("a_name");
        let b = Name::new("b_name");
        assert!(a < b);
        let hasher = content_hasher();
        assert_eq!(hasher.hash_one(a), hasher.hash_one(Name::new("a_name")));
    }
}
