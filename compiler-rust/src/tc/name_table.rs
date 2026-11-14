//! Names of one worker as dense indices (R4a).
//!
//! A [`Name`] indexes every per-name table of `tc::scope`. The table lives as
//! long as its worker: names are never removed, so an index stays valid
//! across units and the imported member tables keyed by it can be kept.
//!
//! This is the one hash structure of R4. A name arrives as bytes (from the
//! syntax tree or from a segment's string pool) and no index exists for bytes;
//! everything after the interning is indexed by the `Name`.
//!
//! The numbers depend on the order a worker met the names in, which depends
//! on scheduling. Nothing observable may depend on them: they are compared
//! for equality and used as indices, never printed, never an output order
//! (CHECKER_REWRITE 2.1, O18).

/// The hasher of every name table, keyed by fixed seeds: a name hashes the
/// same in every process, so the numbering depends on nothing but the order
/// the names arrive in. The seeds are `crate::name`'s; the first is not the
/// first word of ahash's second constant table, which would make every key
/// hash to one bucket (see `SUBST_MAP_STATE` in `cmi::persistent_env`).
static HASHER: ahash::RandomState = ahash::RandomState::with_seeds(
    0x6a09_e667_f3bc_c908,
    0xbb67_ae85_84ca_a73b,
    0x3c6e_f372_fe94_f82b,
    0xa54f_f53a_5f1d_36f1,
);

/// One hash of `bytes` with [`HASHER`]: O(len), no allocation.
fn hash(bytes: &[u8]) -> u64 {
    HASHER.hash_one(bytes)
}

/// O(1): the text of the span `(start, len)` in `bytes`. A span always
/// starts and ends at the boundaries of a text copied whole.
fn span_text(bytes: &str, (start, len): (u32, u32)) -> &str {
    &bytes[start as usize..(start + len) as usize]
}

/// An interned name of this worker. At most 2^29: a [`super::scope::Key`]
/// keeps three bits for the namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub u32);

/// The names of one worker. All text is in one buffer; a name is a span.
#[derive(Default)]
pub struct NameTable {
    /// Every name's bytes, back to back. A `String`, not a `Vec<u8>`, so that
    /// [`NameTable::text`] slices it in O(1) without revalidating UTF-8.
    pub(crate) bytes: String,
    /// `spans[name]` is the name's `(start, len)` in `bytes`.
    pub(crate) spans: Vec<(u32, u32)>,
    /// The names by content. Hashes come from `hasher`, with fixed seeds.
    pub(crate) table: hashbrown::HashTable<u32>,
}

impl NameTable {
    /// One hash of `text` and one probe; the first time a text is seen, also
    /// one copy of its bytes (amortized, no allocation per name).
    /// Panics at 2^29 names.
    pub fn intern(&mut self, text: &str) -> Name {
        // A probe first, not `HashTable::entry`: `entry` reserves room
        // before it probes, so it could grow the table for a text that is
        // already in it. A second intern of a text writes nothing.
        let wanted = text.as_bytes();
        let hash = hash(wanted);
        if let Some(name) = self.find_hashed(hash, wanted) {
            return name;
        }
        let name = self.spans.len() as u32;
        assert!(name < 1 << 29, "more than 2^29 names");
        let start = u32::try_from(self.bytes.len()).ok();
        let len = u32::try_from(wanted.len()).ok();
        let span = start
            .zip(len)
            .filter(|&(start, len)| start.checked_add(len).is_some())
            .expect("name bytes beyond 4 GiB");
        self.bytes.push_str(text);
        self.spans.push(span);
        let Self {
            bytes,
            spans,
            table,
        } = self;
        table.insert_unique(hash, name, |&name| {
            self::hash(span_text(bytes, spans[name as usize]).as_bytes())
        });
        Name(name)
    }

    /// One hash of `text` and one probe; nothing is written. `None` means no
    /// table of this worker can hold the name.
    pub fn find(&self, text: &str) -> Option<Name> {
        let wanted = text.as_bytes();
        self.find_hashed(hash(wanted), wanted)
    }

    /// One probe of the table for `wanted`, whose hash is `hash`: O(1)
    /// expected, one byte comparison per name of equal hash bits. No write.
    fn find_hashed(&self, hash: u64, wanted: &[u8]) -> Option<Name> {
        self.table
            .find(hash, |&name| {
                span_text(&self.bytes, self.spans[name as usize]).as_bytes() == wanted
            })
            .map(|&name| Name(name))
    }

    /// O(1): the text of a name.
    pub fn text(&self, name: Name) -> &str {
        span_text(&self.bytes, self.spans[name.0 as usize])
    }

    /// O(1): how many names exist; every [`Name`] is below it.
    pub fn len(&self) -> u32 {
        self.spans.len() as u32
    }

    /// O(1).
    pub fn is_empty(&self) -> bool {
        self.spans.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<Name>(), 4);
    }
}
