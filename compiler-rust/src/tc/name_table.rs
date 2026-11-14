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

/// An interned name of this worker. At most 2^29: a [`super::scope::Key`]
/// keeps three bits for the namespace.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub u32);

/// The names of one worker. All text is in one buffer; a name is a span.
#[derive(Default)]
pub struct NameTable {
    /// Every name's bytes, back to back.
    pub(crate) bytes: Vec<u8>,
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
        todo!("R4a")
    }

    /// One hash of `text` and one probe; nothing is written. `None` means no
    /// table of this worker can hold the name.
    pub fn find(&self, text: &str) -> Option<Name> {
        todo!("R4a")
    }

    /// O(1): the text of a name.
    pub fn text(&self, name: Name) -> &str {
        todo!("R4a")
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
