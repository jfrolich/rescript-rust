# R4 kernel measurements

The operations of CHECKER_REWRITE.md section 9.3, decision 5, measured on the
`Scopes` of trunk `6b86494b16` (slices R4a to R4c). Nothing of R4 is on a
build's path: these are kernel costs, not savings in a compiler build.

## Method

As TC_KERNEL_R1.md: Valgrind 3.22 cachegrind, `--cache-sim=no`, the pinned
Rust toolchain, the release profile (fat LTO), one codegen unit, line tables,
on x86-64 Linux.

```sh
CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 \
CARGO_PROFILE_BENCH_DEBUG=line-tables-only \
  cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel --no-run
for op in empty binder find_local find_open find_miss2 bind_leave intern; do
  for n in 0 1000000; do
    valgrind --tool=cachegrind --cache-sim=no \
      --cachegrind-out-file=$op.$n.cg BENCH $op $n
  done
done
cg_annotate --auto=yes --threshold=0 find_open.1000000.cg
```

Each figure is `(full - zero) / 1,000,000`. The `empty` operation of R1 is
not a control for these loops: its body is the R1 dispatch `match` and the
`clear_instances` test (18 of its 19 instructions), which the R4 loops do
not run. Each R4 loop is therefore split by debug-info attribution instead:
the instructions of `tc_kernel::main` on lines of `benches/tc_kernel.rs`,
`core/hint.rs` (`black_box`), `core/iter/range.rs` and `core/cmp.rs` (the
range's comparison) are the loop; everything else (the lines of `tc/scope.rs`,
`tc/name_table.rs` and the slice, vector and option code inlined into them,
and the non-inlined `Scopes::find`, `Scopes::search` and `name_table::hash`)
is the operation.

The shapes (every operation takes an interned `Name`, made before the loop):

- `binder`: `binders.payload[b]`, `b = black_box(Binder(537))` in an array
  of 1,000 binders.
- `find_local`: two opened layers of 256 values each, then a binding of a
  name that is also a member of the inner layer; `find` of it.
- `find_open`: the same two layers, no binding; `find` of a member of the
  inner layer.
- `find_miss2`: three layers of 256; `find` of a member of the outermost.
- `bind_leave`: `enter`, `Binders::push`, `bind`, `leave` in scope 0; the
  per-unit rows are reset to the frozen prefix every 4,096 iterations.
- `intern`: `NameTable::intern("abcdefgh")`, already in a table of 257 names.

## Results

| Operation | Zero run | Full run | Per iteration | Loop | Operation | Gate |
|---|---:|---:|---:|---:|---:|---:|
| `binder` | 421,399 | 11,421,672 | 11.00 | 6.00 | **5.00** | 10: met |
| `find_local` | 913,336 | 66,913,615 | 66.00 | 9.00 | **57.00** | 80: met |
| `find_open` | 890,632 | 243,890,899 | 243.00 | 9.00 | **234.00** | 80: **missed** |
| `find_miss2` | 1,112,178 | 644,112,459 | 643.00 | 9.00 | **634.00** | reported |
| `bind_leave` | 333,030 | 191,517,384 | 191.18 | 17.00 | **174.18** | reported (kernel of 2.2: 44) |
| `intern` | 625,831 | 179,626,105 | 179.00 | 10.00 | **169.00** | reported |

For reference, the R1 `empty` loop: 331,152 and 19,333,410, 19.00 an
iteration.

## `find_open` misses its gate

The shape is the one decision 5 states; it was not changed. Annotated lines
of `tc/scope.rs`, one million iterations:

```text
 2,000,000          self.heads.get(key.0 as usize).copied().unwrap_or(NONE)
10,000,000      pub fn find(&self, key: Key) -> Option<Found> {
 5,000,000          self.find_from(key, head, self.scopes[self.current as usize].opens)
 8,000,000      }
 2,000,000          while layer != NONE {
 3,000,000              let row = self.layers[layer as usize];
 6,000,000              if let Some(member) = self.search(row.table, key) {
 2,000,000          let (pool, row) = if table.0 & IMPORTED != 0 {
 1,000,000              (&self.members, self.tables[table.0 as usize])
 1,000,000          (&pool[..first + row.len as usize], first)
 1,000,000      pub fn search(&self, table: TableId, key: Key) -> Option<u32> {
18,000,000          while lo < hi {
32,000,000              let mid = lo + (hi - lo) / 2;
88,000,000              match rows[mid].key.cmp(&key.0) {
 3,000,000      }
 3,000,000          if table.0 & IMPORTED != 0 {
 2,000,000              Resolved::binder(Binder(self.members[row as usize].target))
15,000,006  <unknown (line 0)>
```

`Scopes::search` is 155 of the 234: nine iterations of the lower-bound loop
on 256 rows at about 15.3 instructions each (2 for the loop test, 3.6 for
`mid`, 9.8 for the bounds-checked load, the comparison and the branchy
update of `lo`, `hi` and `hit`). The rest is `find`'s frame (18), the head
load, the layer walk and `rows`. A probe of a 256-member table is at least
eight comparisons, so the gate of 80 leaves under 10 instructions a
comparison for the whole lookup; this `search` spends 15. `find_miss2` is
the same cost three times (three searches).

## The other operations, annotated

`find_local` (57): `find`'s frame 18, the head load 2, one layer row read
and the mark test 5 (the layer is older than the binding, so it is not
searched), the scope's `opens` 5, the rest in unattributed lines.

`bind_leave` (174): `Binders::push` 13 plus the six vector pushes (in
library lines), `enter` 7 plus the scope and `entered` pushes, `bind` 22
plus the log push, `leave` 13 (the undo loop 8 and the head restore 2).
The kernel of 2.2 measured 44 for a design without layers or the six
binder arrays.

`intern` (169): `name_table::hash` 3 plus the hasher in library lines,
`intern`'s frame 19, `find_hashed` 20 plus the probe of the hash table and
the byte comparison in library lines.
