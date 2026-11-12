# Three-way printer instruction measurement

## Status

The direct Bir emitter and dense naming implementation are built and parity
checked. The three-way measurements must be run on the merged candidate; final
numbers are **not yet recorded here**. Earlier interrupted profiles are not
measurements. The default printer remains legacy, and the default-switch gate
remains closed.

The final report must include the measured commit, binary hash, Rust/Valgrind
versions and architecture; `tests/tests` and a 3,735-module application; totals
for legacy, JS-IR oxc and direct Bir oxc; and naming, AST construction, codegen,
import, shared allocation and unattributed work. Native timing must give mean,
standard deviation and min/max from repeated hyperfine runs, not profiler wall
time.

## Reproduce

Build one release binary for all modes, with line tables for attribution:

```sh
CARGO_PROFILE_RELEASE_DEBUG=1 cargo build --release --manifest-path rewatch/Cargo.toml
```

Set `BIN` to that executable, `PROJECT` to the project, `RESCRIPT_RUNTIME` to a
prepared runtime package, and `OUT` to a local output directory. Build the
runtime before measurement. Run from the project directory with `build .`;
prepare and clean each project identically. Keep all raw profiles local.

```sh
export RAYON_NUM_THREADS=1 RESCRIPT_FULL_BUILD=1
unset RESCRIPT_JS_PRINTER_STATS RESCRIPT_BACKEND RESCRIPT_BACKEND_STATS
unset RESCRIPT_JS_PRINTER_SOURCE_MAPS
export RESCRIPT_JS_PRINTER=legacy
"$BIN" build "$RESCRIPT_RUNTIME"
cd "$PROJECT"
for mode in legacy oxc oxc-bir; do
  "$BIN" clean .
  RESCRIPT_JS_PRINTER="$mode" valgrind --tool=cachegrind \
    --cache-sim=no --branch-sim=no \
    --cachegrind-out-file="$OUT/$mode.cg" "$BIN" build .
done
```

Require a successful full build for every sample. All CLI startup, runtime
bootstrap and filesystem work that still runs inside that process is included.
Run the repository's summary tool on the three profiles:

```sh
python3 scripts/printer_instruction_summary.py legacy.cg oxc.cg oxc-bir.cg
```

Its buckets are **named self instructions**, not inclusive phase costs. Inlining
can move work into a caller's bucket. Shared allocation/container work must not
be charged exclusively to import or emission. In particular, subtracting only
the named import bucket does not establish the cost of direct emission alone.

For that separation, additionally record Callgrind profiles of the same clean
builds and binary. Inspect inclusive `driver::render_js_program` and
`bir::bridge_j::import_js` costs; import is a child of rendering, so these must
not be added together. The difference is rendering without import, including
fallback rendering. The separate `emit::emit_bir` and `emit::program::emit`
boundaries can cross-check the two oxc paths. Confirm the boundaries remain
present in the measured binary and do not substitute a self count if they are
inlined away.

```sh
for mode in legacy oxc oxc-bir; do
  "$BIN" clean .
  RESCRIPT_JS_PRINTER="$mode" valgrind --tool=callgrind \
    --cache-sim=no --branch-sim=no \
    --callgrind-out-file="$OUT/$mode.callgrind" "$BIN" build .
done
callgrind_annotate --inclusive=yes --threshold=100 --auto=no \
  --show=Ir --show-percs=no oxc-bir.callgrind
```

Report Callgrind's own totals with its inclusive costs, rather than silently
mixing counts from two profiler runs. The application has no printer fallback;
public-corpus fallbacks must remain visible in the interpretation.

For native timing, clean in hyperfine's prepare step and repeat all three modes
with the same environment and binary. Use at least one warmup and five measured
runs per mode; report all four summary statistics. Run builds and profilers
sequentially so they do not compete with each other.

Only aggregate counts and timings belong in the report. Do not commit profiles,
application paths, source names, generated code or dependency details.
