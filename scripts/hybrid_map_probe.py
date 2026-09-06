#!/usr/bin/env python3
"""Instrument only a disposable B archive, never a timing source tree.
Usage: hybrid_map_probe.py /tmp/rescript-hybrid-map-experiment/probe-source
Per-map counters measure storage requests, not allocator traffic or nested T.
"""
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
assert root == Path('/tmp/rescript-hybrid-map-experiment/probe-source').resolve()
p = root / 'compiler-rust/src/types/type_expr.rs'
source = subprocess.check_output(['git', 'show', '16caa9a93:compiler-rust/src/types/type_expr.rs']).decode()
start = source.index('#[derive(Debug, Clone)]\npub(crate) struct TypeExprRefMap')
end = source.index('/// Intentional Rust performance representation for short-lived type-node sets.', start)
s = source[start:end]
s = s.replace('    offset: u32,', '''    probe: MapProbe,
    offset: u32,''', 1)
s = s.replace('    pub(crate) fn new() -> Self {', '    #[track_caller]\n    pub(crate) fn new() -> Self {', 1)
s = s.replace('            offset: 0,', '''            probe: MapProbe { caller: std::panic::Location::caller(), ..MapProbe::default() },
            offset: 0,''', 1)
s = s.replace('    pub(crate) fn insert(&mut self, key: TypeExprRef, value: T) -> Option<T> {', '''    pub(crate) fn insert(&mut self, key: TypeExprRef, value: T) -> Option<T> {
        let old_len = self.values.len();
        let old_capacity = self.values.capacity();
        let prepend = !self.values.is_empty() && key.0 < self.offset;
        let result = self.insert_unmeasured(key, value);
        self.probe.inserts += 1;
        self.probe.entries += usize::from(result.is_none());
        if prepend || self.values.capacity() != old_capacity {
            self.probe.requests += 1;
            self.probe.requested_slots += self.values.capacity();
        }
        if prepend { self.probe.prepend_moved_slots += old_len; }
        self.probe.initialized_slots += self.values.len() - old_len;
        result
    }

    fn insert_unmeasured(&mut self, key: TypeExprRef, value: T) -> Option<T> {''', 1)
s += '''#[derive(Debug, Clone)]
struct MapProbe {
    caller: &'static std::panic::Location<'static>,
    entries: usize,
    inserts: usize,
    requests: usize,
    requested_slots: usize,
    initialized_slots: usize,
    prepend_moved_slots: usize,
}
impl Default for MapProbe {
    fn default() -> Self {
        Self { caller: std::panic::Location::caller(), entries: 0, inserts: 0,
            requests: 0, requested_slots: 0, initialized_slots: 0, prepend_moved_slots: 0 }
    }
}
impl<T> Drop for TypeExprRefMap<T> {
    fn drop(&mut self) {
        eprintln!("HYBRID_MAP {}:{} {} {} {} {} {} {} {} {} {}",
            self.probe.caller.file(), self.probe.caller.line(),
            self.probe.entries, self.values.len(), self.values.capacity(),
            self.probe.inserts, self.probe.requests, self.probe.requested_slots,
            self.probe.initialized_slots, self.probe.prepend_moved_slots,
            std::mem::size_of::<Option<T>>());
    }
}

'''
p.write_text(source[:start] + s + source[end:])
print(p)
