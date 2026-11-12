# A prebuilt snapshot of the runtime and Belt: design and staged plan

Status: design. Section A describes trunk; everything from section B on is
proposed and not implemented. This document is the spec for the stages in
section F.

## 0. Summary

### The problem

A clean build of a 3,735-module application (619,000 lines) also compiles the
compiler's own libraries: `@rescript/runtime` (113 modules, 158 files, 29,500
lines) and `@rescript/belt` (43 modules, 81 files, 18,600 lines). Together
that is 239 files and 48,000 lines, reported as 7.7% of that build's
instructions. Their sources are the same for every user of a compiler
version, so the work can be done once, when the packages are built.

### What the code already does

Half of this exists. Since the runtime was compiled into the executable
(`rewatch/src/build/snapshot.rs`), a build whose runtime sources equal
the ones the executable was built from registers the runtime's interfaces from
the executable's memory and compiles none of it. What remains:

1. **Belt is compiled from source in every clean build**, as an ordinary
   dependency package, and its JavaScript is written into the installed
   package.
2. **The runtime shortcut has holes**: it fails on a runtime directory laid
   out as the published package is, it stores the build machine's absolute
   paths, it reads and hashes every runtime source on every build, it does
   per-module work for all 113 modules, and nothing tells a user or CI when
   it silently falls back to compiling from source.

### What is measured, estimated and unknown

| Fact | Value | Status |
|---|---|---|
| Runtime plus Belt as a share of the benchmark build | 7.7% of 76 G instructions | reported for the benchmark; not reproduced here |
| Compiling the runtime from source (113 modules) | 0.98 G instructions | measured (see below) |
| Compiling Belt as a dependency and writing its JavaScript (43 modules, one package spec) | 1.31 G instructions | measured |
| A build that registers the embedded runtime, one user module, no Belt | 16.0 M instructions in total | measured |
| Hashing the runtime sources to verify the embedded runtime (857 KB) | about 2.8 M of those 16.0 M (17% of samples in `blake3`) | measured by sampling |
| Size of the embedded runtime data | 2.46 MB, containing 309 absolute paths of the build machine | measured |
| Size of Belt's stored interfaces and of its JavaScript | under 1 MB (its build database is 983 KB); 360 KB per module format | measured |
| Whether the benchmark's runtime matched its executable's embedded runtime | - | unknown |
| Cost of decoding the runtime units the benchmark references | - | unknown, part of today's build either way |

The measurements were made for this document on an x86-64 Linux machine with
an optimized (thin LTO) `rescript`, counting user-space instructions of the
whole process with `perf stat`, on a project with one source file. They are
not the benchmark machine or the benchmark project. Against the benchmark's
76 G they come to 1.3% for the runtime and 1.7% for Belt, 3.0% together, which
is less than half of 7.7%. The difference is not explained: the two libraries
may cost more per module inside a large build, the instruction counts of two
architectures are not comparable one to one, or the 7.7% may include a runtime
compiled from source. Section F therefore gives savings as a range, and stage
S1 starts by measuring.

### The design in one page

- **One artifact, the snapshot**, holds for each prebuilt package (the runtime
  and Belt) what a dependent reads: each module's interface in the encoding
  the incremental store already uses (`cmi/stored_module.rs`), plus, for
  Belt, its JavaScript for both module formats.
- **It is carried inside the `rescript` executable**, as the runtime's
  interfaces are today. The encoding has no version of its own and can only be
  decoded by the compiler build that wrote it; embedding makes that match by
  construction. The same bytes can be written to a file, which CI and the
  later cache for third-party packages use.
- **It is found through an index**, not registered module by module: a module
  nobody references costs nothing. A referenced module is decoded on first
  lookup, as stored interfaces already are.
- **It is used only when it is provably equivalent**: the package's sources
  hash to the recorded digest and the build's options are among those the
  snapshot was proven for. Otherwise the package is compiled from source, as
  today, and verbose mode says why.
- **A snapshot build is the same as an incremental build of an unchanged
  dependency**: the build system already knows how to stand a stored interface
  in for a compile (`incremental::load_stored`). The snapshot supplies the
  interface from the executable instead of the package's build database, and
  the JavaScript from the snapshot instead of an earlier build.

## A. Today

### A.1 Where the packages are and how they are found

| Package | Source layout in the repository | What is published | How a build finds it |
|---|---|---|---|
| `@rescript/runtime` | `packages/@rescript/runtime/*.res(i)`, flat; its `rescript.json` sets two package specs (`commonjs`/`.cjs`, `esmodule`/`.mjs`, not in-source) and the flags `-make-runtime -nostdlib -nopervasives -open Pervasives ...` | `lib` only (`files` in its `package.json`): `lib/es6/*.mjs`, `lib/js/*.cjs` (both tracked in git), and `lib/ocaml/*.res(i)`, copies of the sources written when the package is built (`source_copies_for_build_dirs`) | `get_runtime_path` in `rewatch/src/build/compile.rs`: the `RESCRIPT_RUNTIME` environment variable, else `helpers::try_package_path` resolves `@rescript/runtime` from the project. Not part of the package graph |
| `@rescript/belt` | `packages/@rescript/belt/src/*.res(i)` | sources and `rescript.json` only; no compiled output | an ordinary dependency: a project lists it in `dependencies` and `packages.rs` discovers it in `node_modules` |

The resolved runtime path is kept in `CompilerInfo::runtime_path` and recorded
in every package's build database (`compiler_info.rs`, key
`compiler.runtime_path`); a different path cleans the package.

### A.2 How and when the runtime is compiled

`pre_compile_runtime_modules` (`compile.rs`) runs on its own thread while the
project sources are parsed (`incremental_build_without_lock` in `build.rs`).
It lists `lib/ocaml/*.res` of the runtime (`runtime_source_paths`) and then
tries, in order:

1. **Already registered** in this process (later builds of a watch session):
   nothing to do.
2. **Embedded** (`snapshot::register`). The executable's build script
   (`rewatch/cli/build.rs`) compiles `packages/@rescript/runtime` with
   `snapshot::compile` and the result is included with
   `include_bytes!` and installed at start-up (`rewatch/cli/src/main.rs`).
   The data is: a magic number, a BLAKE3 digest, then each module's name and
   stored-module bytes. The digest covers the runtime's `rescript.json` and
   each module's name and `.res`/`.resi` contents, not their paths
   (`sources_digest`). At run time the digest of the runtime being used is
   recomputed, and on a match every module is registered with
   `ModuleRegistry::register_stored_static`, borrowing the executable's
   memory.
3. **Stored** by the previous build (`load_runtime_interfaces`): the root
   package's database has a `runtime_interfaces` table, valid under a key
   (`RuntimeStore::key`) made of the executable's hash, the runtime's path and
   configuration, and each source's path, size and modification time.
4. **From source** (`compile_runtime_sources`): all modules are parsed and
   compiled in dependency order on a dedicated pool, and the result is stored
   for step 3 of the next build.

A from-source runtime compile runs the whole pipeline including code
generation, but the JavaScript is dropped: the result's `js` is never written
(`compile_runtime_module_from_source`). A user's build never writes runtime
JavaScript; it relies on the files shipped in `lib/es6` and `lib/js`.

When the project being built is the runtime package itself, its modules are
project modules (`is_runtime` in `compile.rs`): they are compiled, their
JavaScript is written to `lib/es6` and `lib/js`, and their sources are copied
to `lib/ocaml`.

### A.3 How and when Belt is compiled

Belt is a dependency like any other. Every package of a build is compiled
with the **root** project's package specs, suffix, JSX settings and source-map
settings (`build_package_compiler_options`, `js_package_specs`,
`js_output_targets_for_source`), and with its own `compiler-flags`. So:

- a clean build compiles all 43 Belt modules, whether or not they are used;
- Belt's JavaScript is written inside the installed package, where the root
  configuration says: `node_modules/@rescript/belt/src/X<suffix>` for an
  in-source spec, `node_modules/@rescript/belt/lib/<es6|js>/src/X<suffix>`
  otherwise, once per package spec (`js_output_path_for_spec`);
- `rescript clean` removes that JavaScript and Belt's build database.

### A.4 What dependents read

| What | From where | Used for |
|---|---|---|
| Signature | `PortablePersStruct` in the `ModuleRegistry` (`cmi/persistent_env.rs`), internalised once per build into the shared pool (`types/shared_store.rs`) | type checking |
| Constants, arities and inlinable function bodies of exports | `InMemoryModuleInfo`: `cmj_export_constants`, `cmj_export_arities`, `cmj_export_lambdas` (with a location table, `lambda/lam_loc.rs`) | cross-module optimisation |
| Purity | `InMemoryModuleInfo::is_pure` | dropping unused imports |
| Where the module's JavaScript is | for a runtime module, `is_runtime`; the import is always `@rescript/runtime/lib/es6/X.mjs` or `@rescript/runtime/lib/js/X.cjs` (`runtime_module_path` in `js_ir/mod.rs`). For a Belt module, `package_name`, `package_root`, `js_output_suffix` and `package_outputs`, which follow the root configuration | the import path in the dependent's JavaScript |
| GenType declarations | registered by typed-artifact path when the module is registered (the "extras" of `cmi/stored_module.rs`) | genType translation of imported types |
| Source path | `InMemoryModuleInfo::source_path`, `ps_filename`, and the file names inside the signature and the lambda location table | diagnostics, source maps of inlined code, editor tooling |

A stored module (`stored_module::encode`) is exactly this: the extras, then
the core (`PortablePersStruct` and `InMemoryModuleInfo`) in the `binser`
encoding. `ModuleRegistry::register_stored_parts` registers the extras at once
and leaves the core as bytes until the first lookup
(`LazyStoredModules::materialize_with`).

### A.5 What the incremental store records

Each package has `lib/bs/rescript.sqlite` (`state_db.rs`).

- **Runtime.** Only the `runtime_interfaces` table of the root package's
  database, written after a from-source compile. Nothing is written when the
  embedded runtime is used. For scale: a no-change build of the test project
  costs 6.3 M instructions in total, and one that recompiles a single module
  and loads the runtime through path 3 costs 18 M.
- **Belt.** Its own database inside the installed package, with what every
  package records: per module the interface digest, the item digests, the
  reads of other units, the warnings, and the stored interface (`interfaces`
  and `interface_extras`). An incremental build neither parses nor compiles
  Belt; `incremental::stored_loadable` and `load_stored` register the stored
  interfaces of the modules a round needs, and the cores are read from the
  database on first lookup (`state_db::InterfaceCores`).

The interface digest of a module (`item_deps::item_digests`) hashes, besides
the declarations and the backend metadata, `ps_filename`,
`InMemoryModuleInfo::source_path`, `package_name`, `js_output_suffix` and
`package_outputs`.

### A.6 Watch mode

The first build of a watch session takes the same paths as a one-shot build.
Later builds find the runtime registered (path 1). Per the module
documentation of `incremental.rs`, watch mode compiles every project and
dependency module into memory, Belt included, and then recompiles the
dependents of what changes. Every build starts the worker type stores empty
(`thread_store::begin_build`), so the units a build references are
internalised again. Editor tooling type-checks runtime and project sources on
demand against the registry (`rewatch/src/build/tooling.rs`, `Runtime::load`
reads `lib/ocaml`).

### A.7 Defects of the embedded runtime found while writing this

| # | Defect | Evidence |
|---|---|---|
| D1 | A runtime directory without `rescript.json` fails the build with "failed to read runtime config", before the embedded check. The published package ships only `lib`; `npm pack --dry-run` in the package lists no `rescript.json` | reproduced by removing the file from a copy |
| D2 | The embedded data records the absolute source paths of the machine that built the executable (309 occurrences), in `ps_filename`, `source_path` and the file-name tables. They enter the interface digest and can reach whatever prints a dependency's file name. One source-map sample did not show them; this was not searched exhaustively | `strings` on the build script's output |
| D3 | Every build reads and hashes all runtime sources, and decodes the extras of and inserts a registry entry for all 113 modules | `snapshot::register` |
| D4 | A fallback to compiling from source is logged only at debug level; no test fails when the embedded runtime stops matching | `log::debug!` in `register` |
| D5 | The build script watches the sources that existed when it last ran. A runtime that gains a source file is compiled from source at run time until the executable is rebuilt | the comment on `watch_sources` |
| D6 | On fallback, code generation runs for 113 modules and its output is discarded | `compile_runtime_module_from_source` |

## B. The artifact

### B.1 Contents

For each prebuilt package:

| Part | Runtime | Belt | Form |
|---|---|---|---|
| Sources digest | yes | yes | BLAKE3 of each module's name and `.res`/`.resi` contents, and of the package's `compiler-flags` and experimental features as the producer parsed them |
| Per module: core | yes | yes | `stored_module::encode_parts` core: the portable signature (with its fingerprint) and the backend summaries. This is the form dependents consume today |
| Per module: extras | only if not empty | only if not empty | the genType declarations. Both packages have none today; the producer fails if a module has any, until someone needs them (then they go in a separate table registered up front) |
| Per module: JavaScript | no | yes, per module format | see B.3 |
| Recorded root | yes | yes | the package root the producer compiled in, for path rebasing (B.4) |

**JavaScript: the runtime's is shipped, Belt's is written from the
snapshot.** The runtime's JavaScript is already prebuilt in the package and
its import path does not depend on the user's configuration, so nothing
changes. Belt's must appear where a from-source build puts it, with the bytes
a from-source build writes, because the import path in the user's JavaScript
is part of the output contract and follows the root configuration (A.3).
Shipping Belt's JavaScript at a fixed path, as the runtime does, would change
the imports the user's modules emit and is rejected.

### B.2 On-disk format

The stored-module encoding is reused unchanged. It is sound for this purpose
with one condition: `binser` is not self-describing ("deserializing needs the
exact type that was serialized"), so the bytes are valid only for the
compiler build that wrote them. The container therefore does not try to be
portable across versions.

```
magic        8 bytes   "RESSNAP1"
producer     32 bytes  identity of the compiler build (B.5); zero when embedded
packages     u32
per package:
  name, recorded root            length-prefixed strings
  sources digest                 32 bytes
  module count                   u32
  index: module count records, sorted by module name, fixed width
    name offset, name length     u32, u32
    core offset, core length     u32, u32
    js offset, js length         u32, u32  per module format (0, 0 for none)
    slot offset, slot count      u32, u32  per module format (B.3)
blobs        names, cores, JavaScript texts, slot lists
```

All integers are little endian and all offsets are from the start of the
file. Looking a module up is a binary search over fixed-width records that
compares names in place; nothing is decoded or allocated for the modules that
are not looked up. The container is written and read by one module,
`rewatch/src/build/snapshot.rs`, replacing the former runtime-only container.

### B.3 Belt's JavaScript as a template

Measured: Belt's ES-module JavaScript built with suffix `.js`, not in-source,
is byte-identical to the build with suffix `.res.mjs`, in-source, once the
suffix inside sibling imports (`from "./Belt_MapDict.res.mjs"`) is replaced,
for all 43 files. Imports of runtime modules use the fixed runtime path. So
Belt's JavaScript is a function of the module format and the suffix only.

The snapshot stores, per module and format, the text with the suffix removed
and the list of byte offsets where the suffix goes (the slots). Writing a
file is a concatenation.

The producer does not trust this by inspection. It compiles the package under
two suffixes and requires that the two outputs differ exactly at the slots,
and under in-source and out-of-source and requires equality. If a future
change makes Belt's JavaScript depend on anything else, producing the
snapshot fails.

### B.4 Paths

The snapshot stores paths as the producer saw them, plus the recorded root.
The consumer rewrites the prefix `recorded root` to the package's actual root
in the three places a path is kept: `PortablePersStruct::ps_filename`,
`InMemoryModuleInfo::source_path`, and the file-name tables of the signature
and of `CmjExportLambdas` when they are decoded. `package_name`,
`package_root`, `js_output_suffix` and `package_outputs` of a Belt module are
not stored; they are computed for the build as
`in_memory_module_info_for_package` computes them.

Invariant: for every module, the interface digest and item digests of a
snapshot unit equal those of the same unit compiled from source in the same
place. This is what makes switching between the two invisible to the
incremental store, and it is the test that proves the rebasing complete.

### B.5 Keying and verification

| Key | What it guards | How |
|---|---|---|
| Compiler build | the encoding, and every compiler behaviour | embedded: by construction, the bytes were written by this executable's own code. File: the `producer` field must equal the executable's identity, the hash `get_compiler_info` already computes |
| Package sources | the snapshot describes these sources | sources digest, recomputed from the files being used. Covers a patched or older package, and a runtime under development |
| Package options | the flags the package was compiled with | part of the sources digest, taken from the parsed configuration, not the file's bytes. A runtime directory without `rescript.json` (the published layout, D1) is accepted as having the producer's options |
| Root options that reach a dependency | Belt's output | module format and suffix: any, through the template. In-source: any, proven at production. Source maps, dump flags: not supported, fall back (section D). JSX settings and `LetUnwrap`: proven irrelevant at production by a second compile with them set |

Verification cost: the digest reads and hashes 857 KB for the runtime, about
2.8 M instructions measured, and about 600 KB more for Belt. Estimated under
2 ms warm; the wall time was not measured on its own. To keep incremental
builds below that, the root package's database memoises
`(path, size, modification time of each source) -> verified digest`, the key
`RuntimeStore::key` already computes, so an incremental build only calls
`stat`.

### B.6 Loading

1. At process start, `snapshot::install` keeps the `&'static [u8]` and checks
   the magic and the header bounds. No module is touched.
2. Per build, for each prebuilt package in use: verify (B.5), then attach the
   package's index to the registry as one entry,
   `LazyStoredModules { snapshot: Option<Arc<SnapshotPackage>>, .. }`.
3. A lookup that misses the decoded maps asks the snapshot: binary search,
   decode the core from the borrowed bytes, rebase paths, insert. This is
   `materialize_with` with a third source next to `PendingCore::Bytes` and
   `PendingCore::Fetch`.
4. `is_pending_stored`, `is_empty` and the "already registered" test of
   `pre_compile_runtime_modules` ask the snapshot as well.

Budget: under 5 ms and no per-module work for unreferenced modules. Steps 1
and 2 are a header check and the digest. The executable's pages holding
unreferenced modules are never read.

### B.7 On a mismatch

The package is compiled from source exactly as today (A.2 path 4 for the
runtime, an ordinary dependency compile for Belt). The reason is logged at
info level, which `-v` shows:

```
Not using the prebuilt @rescript/belt: its sources differ from the ones this
compiler was built with. Compiling it from source.
```

Reasons: sources differ, options not supported (naming the option), snapshot
absent (an executable built without the packages), disabled by
`RESCRIPT_SNAPSHOT=off`. With `RESCRIPT_SNAPSHOT=require` a mismatch is an
error; CI uses it (C.3).

### B.8 Where the format must change with the checker redesign

`docs/CHECKER_REDESIGN.md` sections B and F change what a published unit is.

| Stage there | Effect on the snapshot | Format change |
|---|---|---|
| P3, publish into the shared pool, encode later | The portable encoding becomes something produced on request. The snapshot producer is such a request. P3's invariant (fingerprint and digests from the graph equal those from the portable form) keeps B.4's invariant true | none |
| P4, process-wide views, no stamp replay | Snapshot units take part in no replay today and need none | none; re-run the equivalence gate |
| P5, absolute paths in exports, indexes built at publication | A snapshot unit's indexes and constructor and label descriptions would be built at first lookup. Storing the unit already in absolute-path form removes the rewrite | the core's contents change. No version bump is needed because the key is the compiler build, but producer and loader change together |
| P10, segments and `UnitExports` | The natural snapshot is the serialised `Segment` and `UnitExports` of each unit plus the ground types it names, in structural form. B.4 there makes segments self-contained, which is what makes them storable. Ground handles differ per process, so a mapped segment cannot be used in place: the loader interns the unit's ground types and copies its nodes once with the handles replaced, a linear pass with no hashing of segment nodes | new container version, `RESSNAP2`. Open question G.6: a reserved range of the ground tier for snapshot types would make the copy unnecessary |
| B.7 there, world lifetime in watch mode | Snapshot units are never retired, and a new world re-internalises them from the snapshot, which is the "encoded form" that section assumes | none |

## C. Producing it

### C.1 When and by which command

| Where | Command | What happens |
|---|---|---|
| Building the executable | `cargo build --manifest-path rewatch/Cargo.toml` (and `make rewatch`, `make rewatch-pgo`) | `rewatch/cli/build.rs` calls `snapshot::produce` for `packages/@rescript/runtime` and `packages/@rescript/belt` and embeds the result, as it embeds the runtime today. The build script lists the package directories, not single files, in `rerun-if-changed` (the `lib` output folders excluded by listing sources and the directory itself), which closes D5 |
| Inspecting or checking | `rescript snapshot --write <file>` and `rescript snapshot --check` (hidden commands, like the existing `bsc` test command) | `--write` produces the snapshot from the packages on disk to a file. `--check` produces it again and compares it with the embedded one, byte for byte |
| `make lib` | unchanged commands, one added step | after building the two packages, `rescript snapshot --check` |
| Release pipeline | unchanged | the executable in each platform package was built from the tagged sources; `--check` runs against the packages that are about to be published |

The producer compiles with the same code path as a build
(`compile_runtime_sources` for the runtime, the package compile for Belt), so
there is no second implementation to keep in step. It needs determinism:
producing twice must give the same bytes. The registry already serialises its
maps sorted (`serialize_sorted`), and the build's determinism rule covers the
rest; `--check` is the test.

The encoding is independent of the host platform (`binser` uses varints and
length prefixes), so a cross-compiled executable can embed a snapshot produced
on the build host. Paths differ per host, which B.4 handles.

### C.2 Proving it is up to date

`rescript snapshot --check` in CI, after `yarn workspace @rescript/runtime
build` and `yarn workspace @rescript/belt build`. It fails when the embedded
snapshot is absent or differs from a fresh one. Together with the existing
`git diff --exit-code lib/js lib/es6` on the runtime, this proves that the
executable, the runtime's shipped JavaScript and the sources agree.

### C.3 Proving equivalence

A script, `scripts/test_snapshot_equivalence.sh`, builds each project of a
list twice from clean, once with `RESCRIPT_SNAPSHOT=require` and once with
`RESCRIPT_SNAPSHOT=off`, and compares:

- every JavaScript file of the project and of its dependencies, including the
  Belt files written into the installed package;
- the diagnostics;
- each module's interface digest and item digests in the build databases.

The list: `tests/tests`, `tests/belt_tests`, the `rewatch/testrepo` projects,
and one small project per row of the supported configurations in section D
(both module formats, in-source and not, two suffixes, two package specs at
once). It runs in the validation workflow next to the parity scripts.

## D. Which configurations can use it

"Falls back" always means: that package is compiled from source, as today.

| Configuration | Runtime | Belt |
|---|---|---|
| Module format `esmodule` or `commonjs`, any suffix, in-source or not, several package specs | snapshot (unaffected: its JavaScript is shipped) | snapshot; one file written per spec from the template |
| Source maps enabled | snapshot. Inlined runtime code names runtime files in the map, so the path rebasing of B.4 must be in place first | falls back: Belt's maps are not in the snapshot |
| JSX version, JSX module, preserve mode, `LetUnwrap` in the root | snapshot | snapshot (proven irrelevant at production) |
| genType configured in the root or another package | snapshot | snapshot; neither package has genType declarations |
| A runtime or Belt of another version, or with edited sources | falls back | falls back |
| `RESCRIPT_RUNTIME` pointing anywhere | decided by the digest alone | - |
| The project being built is `@rescript/runtime` | not used: its modules are project modules and are compiled and written | not applicable |
| The project being built is `@rescript/belt` | snapshot | not used |
| Belt as a workspace package of a monorepo | snapshot | snapshot when the digest matches. The producer requires that Belt compiles without warnings, so no diagnostic is lost |
| Dump flags (`build_state.dump`), `RESCRIPT_FULL_BUILD` | falls back | falls back |
| Watch mode | snapshot | snapshot for the first build; when a source of a snapshot package changes, that package falls back for the rest of the session |
| An executable built outside the repository, without the packages | falls back, with the build script's warning | falls back |

## E. Third-party packages

The same mechanism can cache any dependency in `node_modules`, as a later
stage, with three differences.

- **Nobody ships it.** The cache is produced by the first build on a machine
  and stored as snapshot files, one per package, under
  `node_modules/.cache/rescript/`, so that `rescript clean` and a CI cache of
  that directory keep it.
- **The key is wider.** The compiler build; the package's sources and
  configuration; the root options that reach a dependency compile (package
  specs and suffix, JSX settings, source maps, experimental features); and
  the interface digest of every unit of another package that the package's
  compiles read, which the incremental store already records as imports.
  With the root options in the key, the JavaScript is stored verbatim and no
  template is needed.
- **Some packages cannot use it**: a package with a `ppx` (the key would need
  the PPX executable's hash), a package whose sources are generated during
  the build, a pinned or workspace package (`is_local_dep`), which is edited
  like project code.

What it saves is unknown: it is the share of a clean build spent in
`node_modules`, which was not measured for the benchmark. An alternative with
no new format is to let `rescript clean` keep the build databases and
JavaScript of non-local dependencies unless asked to remove them; the
incremental store then already does the rest. That is a product decision and
is listed in G.7.

## F. Staged plan

Every stage is one pull request that leaves trunk passing and shipping.
"Gate" always includes `cargo build` and `cargo test` for `compiler-rust` and
`rewatch`, the four output parity scripts, `make test-rewatch` and the
instruction-count workflow. Only additions are listed. Savings are shares of
today's 76 G benchmark build. Where two numbers are given, the first follows
from the local measurements in section 0 and the second scales them to the
reported 7.7%.

| # | Stage | Depends on | Size (lines) | Saving | Hand to a less capable model |
|---|---|---|---|---|---|
| S1 | Belt from the snapshot; switch, message and equivalence gate | - | 1,100 | 1.7% to 4.4% on a clean build | yes, with the notes below |
| S2 | Runtime: published layout, path rebasing, visible fallback | S1 | 500 | 0 where the embedded runtime matches today; 1.3% to 3.3% where D1 or a stale embed prevents it | yes |
| S3 | Index lookup and memoised verification; no code generation on fallback | S2 | 500 | under 0.1% of a clean build; about 3 M instructions of every incremental build | yes |
| S4 | `rescript snapshot --write/--check`, `make lib` and CI freshness | S1 | 300 | 0 | yes |
| S5 | Watch mode and tooling audit | S2 | 300 plus tests | 0 for one-shot builds | yes |
| S6 | Cache for third-party packages | S3, S4 | 1,200 | unknown (E) | no |
| S7 | Follow the checker redesign (B.8) | P5 and P10 there | with those stages | removes the decode and internalise of referenced snapshot units; not measured | no |

S1 comes first because Belt is the part that is compiled in every clean build
today. S2 to S5 can proceed in parallel after S1 except that S2 and S3 both
edit `snapshot.rs`.

### F.1 S1: Belt from the snapshot

#### S1 baseline measurement

Measured at `6f17907981` on x86-64 Linux, with a fat-LTO release build
(`cargo build --release --manifest-path rewatch/Cargo.toml`), Valgrind 3.22.0
Cachegrind (`--tool=cachegrind --cache-sim=no`) and `RAYON_NUM_THREADS=1`.
The project was a disposable source-only copy of `tests/belt_tests`, with
source-only copies of Belt and the runtime. Runtime preparation was outside
the measurement; both measured builds used the same executable and paths.

| Build | Modules compiled | Instructions |
|---|---:|---:|
| Clean project and Belt | 80 | 1,814,122,576 |
| Clean project, Belt output retained | 37 | 668,482,159 |

For the second build, only the root project's `lib` directory and generated
`src/*.mjs` files were removed from the build location; Belt's database and
JavaScript were retained. The measured difference is 1,145,640,417
instructions (63.15% of this test project's clean build). The S1 snapshot
budget for this fixture is at most 701,906,266 instructions (the retained-Belt
build plus 5%). The baseline executable is 35,292,816 bytes. These counts are
for the test fixture, not the 3,735-module application.

Code/document discrepancy: build databases are under `lib/rescript`, not
`lib/bs` as section A.5 says. Hardware instruction counting was unavailable
in the measurement environment; the figures above are Cachegrind counts.

- **Changes.** Replace the runtime-only container with `snapshot.rs` and the
  container of B.2 with two packages. The build script produces Belt's part:
  it compiles Belt against the runtime it just compiled, under the proof
  configurations of B.3 and B.5, and stores cores and JavaScript templates.
  In a build, after packages are discovered, a dependency named
  `@rescript/belt` whose digest matches and whose build options are supported
  is marked prebuilt: its modules are not parsed and not compiled, their
  interfaces are registered from the snapshot with the package fields
  computed for this build (B.4, Belt part only), and their JavaScript is
  written from the templates for each root package spec when the file is
  missing or different. `RESCRIPT_SNAPSHOT=off|require` and the info-level
  message of B.7. The equivalence script of C.3.
- **Files.** `rewatch/src/build/snapshot.rs`, `rewatch/cli/build.rs`, `rewatch/cli/src/main.rs`,
  `rewatch/src/build.rs`, `rewatch/src/build/compile.rs`,
  `rewatch/src/build/incremental.rs` (reuse `load_stored`'s registration),
  `rewatch/src/build/clean.rs` (cleaning still removes the written files),
  `scripts/test_snapshot_equivalence.sh`, the validation workflow.
- **Invariants.** B.4's digest equality for every Belt module. The files
  written are byte-identical to a from-source build's. A build with the
  snapshot and a later incremental build without it (or the reverse)
  recompile nothing in the project.
- **Gate.** The equivalence script. A unit test that a template with slots
  reproduces both proof builds. The instruction-count workflow shows no
  change (its project does not depend on Belt); `tests/belt_tests` built with
  both settings is the measurement to report in the pull request, together
  with a before and after count on a project that depends on Belt.
- **First step, before writing code.** Count a clean build of a project that
  uses Belt with and without Belt's modules marked as already built, to
  replace the range above with a number.
- **Hand-off.** Yes. The points needing care are listed as invariants; the
  mechanism it reuses exists.

### F.2 S2: the runtime path made reliable

- **Changes.** Accept a runtime without `rescript.json` (B.5), and add
  `rescript.json` to the runtime package's `files` so that a fallback can
  read its flags. Rebase paths for runtime units (B.4), and make the digest
  cover the parsed options instead of the configuration file's bytes. Info
  message on fallback. Delete the `runtime_interfaces` table only if S3's
  measurement shows the stored path is no longer worth keeping; otherwise
  keep it as the second chance for a runtime that does not match.
- **Files.** `snapshot.rs`, `compile.rs` (`pre_compile_runtime_modules`),
  `cmi/portable_types.rs` and `lambda/lam_loc.rs` (prefix rewrite at decode),
  `packages/@rescript/runtime/package.json`.
- **Invariants.** No path of the build machine is reachable from a registered
  unit. Digest equality with a from-source compile for every runtime module.
- **Gate.** The equivalence script with the runtime copied to a different
  directory than the one the executable was built in, and with
  `rescript.json` removed. A test that searches the registered units for the
  recorded root. An installed-package test in CI with
  `RESCRIPT_SNAPSHOT=require`.

### F.3 S3: index lookup, memoised verification, cheaper fallback

- **Changes.** B.6 steps 2 to 4 for both packages, replacing the per-module
  `register_stored_static` loop. The verification memo of B.5. On a
  from-source runtime compile, stop before code generation (D6).
- **Files.** `cmi/persistent_env.rs` (`LazyStoredModules`), `snapshot.rs`,
  `state_db.rs`, `compile.rs`.
- **Invariants.** A module that no compile looks up is never decoded and
  causes no allocation. The memo is discarded with the build directory.
- **Gate.** A counter (`perf_counters.rs`) of decoded snapshot modules, with a
  test that a one-module project decodes only what it references. The
  instruction count of a no-change build does not rise.

### F.4 S4: producing and checking

- **Changes.** C.1's two commands, the `make lib` step, the CI step of C.2,
  the build script's directory watching (D5).
- **Invariants.** Producing twice gives the same bytes.
- **Gate.** `rescript snapshot --check` passes in CI; editing a runtime
  source without rebuilding the executable makes it fail.

### F.5 S5: watch mode and tooling

- **Changes.** When a source of a snapshot package changes during a session,
  drop that package's snapshot entries and compile it from source. Check
  every reader of a registered unit that assumes it was compiled in this
  process: editor tooling (`tooling.rs`), genType contexts, the item-digest
  caches cleared at the start of each build.
- **Gate.** Watch tests in `rewatch/tests`: start with the snapshot, edit a
  Belt source in the installed package, and compare the output with a
  from-source session.

### F.6 S6 and S7

S6 is section E and needs the product decision of G.7 first. S7 is B.8 and
belongs to the pull requests of P5 and P10 in the checker redesign; this
document is their checklist for the snapshot.

## G. Risks and open questions

| # | Question | Recommended answer |
|---|---|---|
| G.1 | Is the saving 3% or 7.7%? | Unknown. Measure first (F.1). Even at the low end S1 is worth doing: it is the only library work left in every clean build |
| G.2 | Embed in the executable or ship a file in the npm packages? | Embed. The encoding is tied to the compiler build, and a file in a separately versioned package can be paired with the wrong executable (a development build, a prerelease). The cost is executable size: 2.5 MB today, about 4.5 MB with Belt, in an executable of tens of megabytes |
| G.3 | Do build-machine paths in the embedded runtime change any output today? | Not shown. They change interface digests, which only matters when a build switches between embedded and from-source. S2 removes the question |
| G.4 | Can writing files into `node_modules/@rescript/belt` race with another build of the same installation? | It already does: every build writes Belt's JavaScript there. Writing only when missing or different, with the content fixed by the snapshot, makes it safer than today |
| G.5 | Is Belt's JavaScript really a function of format and suffix only? | Measured for two configurations. The producer proves it on every build of the executable (B.3) and fails otherwise |
| G.6 | Should the ground tier of the redesigned checker reserve a range for snapshot types, so snapshot segments can be used in place? | Decide in P10. Start with the copy; it costs only for referenced units |
| G.7 | Should `rescript clean` keep the outputs of non-local dependencies (E)? | A product decision. If yes, S6 shrinks to fresh installs and CI caches |
| G.8 | Does the build script make building the executable slower? | It already compiles the runtime, with the compiler as a build dependency of `rewatch/cli`. Belt adds about four compiles of 43 modules. Not measured |
| G.9 | What if Belt gains genType annotations or JSX? | Producing fails with a message naming the module. Then add the extras table (B.1) or the option to the key |
| G.10 | Windows | Path rebasing must compare prefixes in the form the producer recorded them. A checkout that converts line endings changes the sources digest and falls back; the published package is not affected |

Not determined from the code: whether a diagnostic can print the file name of
a declaration in a dependency (which would make D2 visible to users), and
whether watch mode's first build takes the incremental plan or compiles every
dependency; the two descriptions in `build.rs` and `incremental.rs` read
differently and no watch session was run for this document.
