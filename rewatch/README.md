# Rewatch build system

Rewatch is the Rust implementation of the ReScript build and watch commands.
It reads `rescript.json`, discovers packages and source files, maintains module
dependencies, and invokes the compiler in dependency order.

## Code map

- [`src/config.rs`](src/config.rs) parses configuration and converts supported
  settings to compiler arguments.
- [`src/build/packages.rs`](src/build/packages.rs) discovers packages and
  resolves package dependencies.
- [`src/build/parse.rs`](src/build/parse.rs) produces compiler AST artifacts.
- [`src/build/deps.rs`](src/build/deps.rs) builds the module dependency graph.
- [`src/build/compile.rs`](src/build/compile.rs) invokes the compiler and
  updates build artifacts.
- [`src/watcher.rs`](src/watcher.rs) maps filesystem and configuration changes
  to incremental rebuilds.
- [`src/cli.rs`](src/cli.rs) and [`cli/src/main.rs`](cli/src/main.rs) own
  command-line parsing and dispatch. The `rescript` executable is the
  [`cli`](cli) package, whose [build script](cli/build.rs) compiles
  `packages/@rescript/runtime` into it
  ([`src/build/embedded_runtime.rs`](src/build/embedded_runtime.rs)).

Focused documentation:

- [configuration support matrix](CompilerConfigurationSpec.md)
- [monorepo discovery and build scope](MonorepoSupport.md)
- [feature-gated source directories](Features.md)
- [integration-test workspace](testrepo/README.md)

The ReScript website owns user-facing configuration documentation. The support
matrix in this directory records what the current Rewatch implementation
accepts, including compatibility fields which are not recommended for new
projects.

## Location-free build path

Ordinary builds retain the parsed AST between dependency discovery and compilation,
but do not populate source-position or location side tables. Scanner cursor positions
remain transient grammar state. AST handles retain declaration identity and whether a
node is generated; neither carries a source span. The source bytes are retained for a
location-enabled retry, then dropped with the AST after compilation.

- A frontend warning or parse error reparses the file with locations before reporting it.
- Compiler warnings retry only the affected module with locations. Type/backend errors
  restart the build with located dependency signatures too: cross-module errors can cite
  a declaration in another source file. Speculative diagnostic text is never shown.
  Subsequent watch builds can use the fast path again.
- Location-valued generated code (`__LINE__`, assertions, match failures, recursive
  module initialization) retries only that module, before publishing its signature or JS.
- Source maps, editor tooling and requested IR dumps use locations.

The default standalone parser API still retains complete location side tables for
formatting and AST marshalling. Location-free compilation does not change
the OCaml wire representation.

## Building and testing

Run commands from the repository root:

```sh
make rewatch
make test-rewatch-rust
cargo test --manifest-path rewatch/Cargo.toml
cargo clippy --manifest-path rewatch/Cargo.toml --all-targets --all-features
cargo fmt --check --manifest-path rewatch/Cargo.toml
```

`make test-rewatch-rust` builds this implementation and runs the integration
suite against it; in this repository `make test-rewatch` runs the same suite
against the same Rust `rescript` binary.
`make rewatch-pgo` makes a profile-guided release build
([`scripts/build_rewatch_pgo.sh`](../scripts/build_rewatch_pgo.sh)): it builds
an instrumented binary, has it compile a copy of `tests/tests`, and builds
again with the recorded profile. Use it for a binary whose speed matters; it
takes two release builds and needs `rustup component add llvm-tools`.

The integration suite is [`tests/suite.sh`](tests/suite.sh). It creates and
modifies projects under `testrepo/`; use its helpers for portable path and file
operations rather than adding platform-specific `sed` commands or fixed
sleeps.

When a CLI or configuration value affects compilation, trace it through both
build and watch entry points. Command-line values override project
configuration. Keep that precedence and the compiler-argument conversion in
one owning layer where possible, and add both unit and integration coverage.

Put public Rust API contracts in source documentation, local algorithm or
state invariants beside their implementation, and cross-module navigation in
this guide. Update or remove focused documents when the implementation changes;
do not preserve completed plans as descriptions of current behavior.

### Check without generating code

```sh
rescript build --check-only
rescript build path/to/project --check-only
RESCRIPT_PHASE_TIMINGS=1 rescript build path/to/project --check-only
```

`--check-only` is available on `build`, not `watch`. It parses and type checks
all source modules, using the normal dependency scheduler and worker parallelism.
Interfaces are published in memory for dependent modules. It does not run Lambda
conversion, JavaScript generation/printing or genType, and does not write build
artifacts, logs, locks or incremental state. Existing build outputs are untouched.
It cannot be combined with `--after-build` or intermediate-representation dumps.

Parser, frontend and type-checker diagnostics retain their normal text, locations,
ordering and error exit status. Diagnostics raised **while generating code** are
not reported. These include polymorphic comparison (warning 102), unknown builtin
or unrecognized intrinsic primitives, Lambda attribute warnings (duplicated or
misplaced attributes and invalid attribute payloads), unsupported dynamic imports,
flattened-export name collisions, unsafe recursive-module initialization and
refutable top-level `let` patterns. genType and other backend diagnostics are also
omitted: passing check-only does not guarantee a successful full build.

`RESCRIPT_PHASE_TIMINGS=1` prints the existing aggregate compiler phase report on
stderr for either build mode. Use `RESCRIPT_MODULE_TIMINGS=1` for per-module timings
or `RESCRIPT_RUNTIME_TIMINGS=1` for runtime preparation timings. Check-only has no
Lambda, codegen, printing or genType work. For a clean-build comparison, clean the
normal build before each measurement; a normal incremental no-op is not comparable
to check-only, which checks every module on every invocation.

## Derives

`ppx-flags` accepts only built-in spice derives. Other entries fail configuration
validation with the package name and flag; source-marker filtering cannot hide
an unsupported PPX. Spice needs no installed executable and runs on the current
AST, without a frozen-v0 conversion.


## SQLite publication locks

All paths below are in the owning package's `lib/rescript` directory. On
Linux/macOS/BSD, the application uses `fs2` (`flock`); on Windows it uses
`LockFileEx`. **Never take an application lock on a file SQLite opens.** BSD
systems can make a `flock` conflict with SQLite's `fcntl` locks on the same inode.

| Owner / purpose | File | Acquisition on Unix |
| --- | --- | --- |
| Root build / watch exclusion | `.build.lock.guard` / `.watch.lock.guard` | `flock(LOCK_EX | LOCK_NB)`, bounded retry in `lock.rs` |
| Package writers, private-file creation/cleanup, atomic publication | `rescript.sqlite.guard` | `flock(LOCK_EX)` |
| Multi-connection package reader | `rescript.sqlite.guard` | `flock(LOCK_SH)` across all table reads |
| Private preparation lifetime | `.rescript-record-<unique>.sqlite.lock` | `flock(LOCK_EX)` on a newly created sidecar |
| Abandoned-private-file cleanup | Same private `.sqlite.lock` sidecar | `flock(LOCK_EX | LOCK_NB)`; skip a locked sidecar |
| SQLite itself | Live/private `.sqlite` and SQLite-managed side files | SQLite's own locking protocol (`fcntl` byte-range locks for Unix databases) |

The package guard covers creation and acquisition of the private sidecar lock,
then is released before schema creation. The lifetime lock stays held until
SQLite is closed and the private file is removed or renamed; the sidecar is then
removed while still locked. Cleanup holds the package guard and probes private
sidecars, including sidecars orphaned by a kill after rename. A private database
without a sidecar is abandoned under this protocol. Files left by the older
same-inode-lock implementation must only be cleaned once those old builds have
stopped.

Private SQLite connections have a zero busy timeout: contention on an unpublished
file is a protocol error, not a reason to wait. A preparation error is reported
once; that package is excluded from the successfully prepared set. After the
preparation worker joins, the existing final-state recording path reconstructs
its rows and writes its record. Other packages continue streaming normally.

Run `python3 scripts/test_busy_private_record.py rewatch/target/debug/rescript`
with a debug executable. It holds a conflicting `fcntl` lock from a second
process across the entire fallback, testing both schema creation and insertion,
clean and existing-record builds, root and dependency packages, and 1/2/8 workers.
The fallback must finish within five seconds, preserve rows/output and incremental
reuse, report once, and remove private files/sidecars. This emulates SQLite busy
on Linux; it does not replace native macOS validation.
