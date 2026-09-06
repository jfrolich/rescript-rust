#!/usr/bin/env python3
"""Instrument only the archived candidate. No global counters or normal-build probe.
Census measures context-destruction retained arrows and cumulative get_desc clones,
not every temporary TypeArg creation or allocator metadata/DRAM traffic.
"""
from pathlib import Path
import difflib

ROOT = Path('/tmp/rescript-type-arg-experiment/probe-source').resolve()
p = ROOT / 'compiler-rust/src/types/context.rs'
assert ROOT != Path(__file__).resolve().parents[1]
old = p.read_text()
s = old.replace('    types: TypeArena,', '    types: TypeArena,\n    type_arg_snapshot_probe: Cell<[u64; 8]>,')
s = s.replace('            types: TypeArena::new(),', '            types: TypeArena::new(),\n            type_arg_snapshot_probe: Cell::new([0; 8]),')
needle = '        TypeDescSnapshot(self.types.get(r).desc().clone())'
assert s.count(needle) == 1
s = s.replace(needle, '''        let desc = self.types.get(r).desc();
        let mut counts = self.type_arg_snapshot_probe.get();
        type_arg_probe(&desc, &mut counts, true);
        self.type_arg_snapshot_probe.set(counts);
        TypeDescSnapshot(desc.clone())''')
s += '''
// Probe indices: arrows, arguments, hot capacity bytes, cold box count,
// cold box bytes, owned string capacity bytes, nonempty strings, optional count.
fn type_arg_probe(desc: &TypeDesc, out: &mut [u64; 8], cloned: bool) {
    if let TypeDesc::Tarrow { args, .. } = desc {
        out[0] += 1;
        out[1] += args.len() as u64;
        let capacity = if cloned { args.len() } else { args.capacity() };
        out[2] += (capacity * std::mem::size_of::<super::type_expr::TypeArg>()) as u64;
        for arg in args {
            match arg.label() {
                ArgLabel::Nolabel => (),
                ArgLabel::Labelled(l) | ArgLabel::Optional(l) => {
                    out[3] += 1;
                    out[4] += std::mem::size_of::<ArgLabel>() as u64;
                    out[5] += if cloned { l.txt.len() } else { l.txt.capacity() } as u64;
                    out[6] += u64::from(!l.txt.is_empty());
                    out[7] += u64::from(arg.label().is_optional());
                }
            }
        }
    }
}
impl Drop for TypeContext {
    fn drop(&mut self) {
        let mut retained = [0; 8];
        for i in 0..self.types.len() {
            let d = self.types.get(TypeExprRef::from_usize(i)).desc();
            type_arg_probe(&d, &mut retained, false);
        }
        eprintln!("TYPE_ARG_PROBE retained={:?} snapshots={:?}", retained, self.type_arg_snapshot_probe.get());
    }
}
'''
assert s != old
p.write_text(s)
(ROOT.parent / 'type-arg-probe.patch').write_text(''.join(difflib.unified_diff(
    old.splitlines(True), s.splitlines(True), fromfile='a/compiler-rust/src/types/context.rs',
    tofile='b/compiler-rust/src/types/context.rs')))
