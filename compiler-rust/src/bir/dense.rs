//! Reusable scratch tables for dense unit-local identities.

pub(super) struct DenseTable<T> {
    values: Vec<Option<T>>,
    touched: Vec<usize>,
    #[cfg(test)]
    accesses: std::cell::Cell<usize>,
}

impl<T: Copy> DenseTable<T> {
    /// O(size) initialization, once per unit pass, not once per candidate.
    pub(super) fn new(size: usize) -> Self {
        Self {
            values: vec![None; size],
            touched: Vec::new(),
            #[cfg(test)]
            accesses: std::cell::Cell::new(0),
        }
    }

    /// O(1) lookup. Fresh identities outside the original unit have no entry.
    pub(super) fn get(&self, index: usize) -> Option<T> {
        #[cfg(test)]
        self.accesses.set(self.accesses.get() + 1);
        self.values.get(index).copied().flatten()
    }

    /// Amortized O(1); records each touched identity once, including overwrites.
    pub(super) fn insert(&mut self, index: usize, value: T) {
        #[cfg(test)]
        self.accesses.set(self.accesses.get() + 1);
        if self.values[index].replace(value).is_none() {
            self.touched.push(index);
        }
    }

    /// O(touched entries); retains both allocations for the next candidate.
    pub(super) fn clear(&mut self) {
        for index in self.touched.drain(..) {
            #[cfg(test)]
            self.accesses.set(self.accesses.get() + 1);
            self.values[index] = None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::VarId;

    #[test]
    fn ten_thousand_variables_have_linear_table_accesses() {
        let mut table = DenseTable::new(10_000);
        for _ in 0..2 {
            for i in 0..10_000 {
                table.insert(i, VarId(i as u32));
                table.insert(i, VarId(i as u32));
                assert_eq!(table.get(i), Some(VarId(i as u32)));
            }
            table.clear();
            assert!(table.touched.is_empty());
        }
        assert_eq!(table.accesses.get(), 80_000);
        assert_eq!(std::mem::size_of::<DenseTable<VarId>>(), 56);
    }
}
