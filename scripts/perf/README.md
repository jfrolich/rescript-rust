# Build performance tools

| Script | What it does |
| --- | --- |
| `profile_build.sh` | Records clean builds with samply and prints the data-movement breakdown (`dod_breakdown.py`). |
| `dod_breakdown.py` | Breaks samply profiles down into allocation, copying, drops, clones and hashing per compiler area. |
| `alloc_count.sh` | Counts the allocations of one clean build (needs an `alloc-stats` binary). |
| `alloc_sites.py` | Summarizes sampled allocation sites by construct, module, function and file:line. |

Set `RESCRIPT_RUNTIME` to the checkout's `packages/@rescript/runtime` for all of
them, as for any direct rewatch run.

## Allocation statistics

The `rescript` CLI has an `alloc-stats` cargo feature, off by default. With it,
the global allocator is a thin counting wrapper around mimalloc
(`rewatch/cli/src/alloc_stats.rs`); without it, builds use plain mimalloc and
carry none of this code. Two environment variables read the counters out:

- `RESCRIPT_ALLOC_COUNT=1` prints the total allocations, bytes, frees and
  reallocs, plus a size histogram, to stderr when the process exits.
- `RESCRIPT_ALLOC_SITES=<file>` captures a backtrace for every 8192nd
  allocation of each thread and writes them to `<file>` at exit.

Allocation counts barely depend on machine load, which makes them a steadier
gate than wall time when comparing two binaries.

### Totals

```bash
cargo build --release --manifest-path rewatch/Cargo.toml -p rescript-cli --features alloc-stats
cp rewatch/target/release/rescript /tmp/rescript-alloc
scripts/perf/alloc_count.sh /tmp/rescript-alloc path/to/project
```

`ALLOC_STATS=1 scripts/perf/profile_build.sh ...` runs the same count after
profiling, when given an `alloc-stats` binary.

### Sites with file:line

Backtraces need debug info to resolve file and line. On macOS, build with
packed split debug info and put the dSYM bundle next to the binary under the
binary's name, where the backtrace symbolizer looks for it:

```bash
CARGO_PROFILE_RELEASE_DEBUG=limited \
CARGO_PROFILE_RELEASE_SPLIT_DEBUGINFO=packed \
CARGO_PROFILE_RELEASE_STRIP=none \
  cargo build --release --manifest-path rewatch/Cargo.toml -p rescript-cli --features alloc-stats
cp rewatch/target/release/rescript /tmp/rescript-alloc
cp -R rewatch/target/release/deps/rescript-*.dSYM /tmp/rescript-alloc.dSYM
scripts/perf/alloc_count.sh /tmp/rescript-alloc path/to/project /tmp/sites.txt
scripts/perf/alloc_sites.py /tmp/sites.txt
```

If several `rescript-*.dSYM` bundles exist in `deps/`, take the newest. On
Linux, `CARGO_PROFILE_RELEASE_DEBUG=limited` alone is enough. Capturing and
symbolizing backtraces makes the sampled build several times slower; use the
totals, not the sampled run, for timing.

`alloc_sites.py` attributes each sample to the first frame in
`compiler-rust/src` or `rewatch/src` that is not a generic helper (clone,
collect, formatting) and to the construct that allocated: `String`, `format!`,
`Vec` growth, clone or `with_capacity`, `HashMap`, `Box`, `Arc`, `Rc`,
`SmallVec` spill. Each sample stands for about 8192 allocations.
