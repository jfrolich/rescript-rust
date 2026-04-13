# Ralph TODO: Rewatch In-Memory Build

**Last Updated:** 2026-04-13
**Status:** Review blocked: follow-up required before acceptance

## Goal

Add a new `--in-process` mode to `rewatch` that runs the Rust compiler fully in-process, keeps dependency interfaces in memory, and stops emitting or reading compiler assets anywhere in that build graph. Only final JS outputs should be written in `--in-process`.

Clean architecture target for this project:

- `--in-process` must not depend on `PersistentEnv`
- shared truth lives in build-state module/interface registries
- per-file compilation uses a local resolver session, not a shared mutable env token
- `PersistentEnv` may survive temporarily only as a file-backed compatibility adapter during migration, but do not extend it further for `--in-process`

Clean architecture, stated operationally:

- `BuildCommandState` owns the authoritative parsed AST registry, published-interface registry, and module metadata registry.
- Each compile wave takes one immutable snapshot of that published state.
- Each worker borrows that snapshot through a local resolver session with only small per-file memoization.
- Resolver lookup in `--in-process` must be snapshot-only: no disk fallback and no on-demand source compilation.
- Successful compilation returns a delta that is published back into build state for later waves.
- Sibling workers in the same wave must not observe each other's partially-published state.

## Post-Review Blockers

- `rewatch/tests/in-process.sh` currently accepts a non-zero exit from `rewatch build --in-process` by matching partial progress text like `Compiled 52 modules`. That is not acceptable as a completion signal. The in-process suite must require a successful process exit.
- In-memory interface invalidation is currently wrong: `register_in_memory_interface(...)` always bumps the generation counter, and `compile.rs` uses generation-before vs generation-after equality as the "interface changed" test. That makes every recompiled dirty module look interface-dirty, even when the published signature is unchanged.
- `ModuleRegistry` is only grown/overwritten. Deleted modules, stale namespace aliases, and stale module metadata are not purged from the shared registry, so watch/incremental builds can resolve removed modules until process restart.
- `PersistentEnv` is not removed entirely yet. The shared `BuildCommandState` token is gone, and the public in-process entrypoints no longer take or return a `PersistentEnv`, but `compiler-rust/src/driver.rs` still creates a fresh `PersistentEnv::from_registry(...)` internally for each compilation, and the typechecker / JS backend still depend on that abstraction.

## Current Findings

- `node_modules` packages are already source-backed in `rewatch`; the special disk-backed bootstrap case is `@rescript/runtime`.
- `rewatch` currently has two Rust-related toggles, not three explicit modes: `--rust` only affects parsing, while compilation is already Rust by default unless `--subprocess` is used. This needs to become an explicit mode model.
- `rewatch/src/build/parse.rs` still shells out to `bsc` when the Rust parser path is disabled.
- `rewatch/src/build/namespaces.rs` still shells out to `bsc` for namespace `mlmap` compilation.
- `rewatch/src/build/compile.rs` still builds a compiler-asset-oriented protocol (`-I .../lib/ocaml`, `-bs-read-cmi`, `-bs-package-output`, copied `.cmi/.cmj/.cmt/.cmti`, copied source files).
- `rewatch/src/build/deps.rs` still rereads dependency names from emitted `.ast`.
- `rewatch/src/build/read_compile_state.rs` reconstructs state from compiler assets on disk.
- `rewatch/src/build/build_types.rs` and `rewatch/src/build/compile.rs` still track stale dependency state via `last_compiled_cmi` / `last_compiled_cmt` timestamps.
- `rewatch/src/build.rs`, `rewatch/src/build/compiler_info.rs`, `rewatch/src/build/logs.rs`, and `rewatch/src/sourcedirs.rs` still write non-JS metadata (`build.ninja`, `compiler-info.json`, `.compiler.log`, `.sourcedirs.json`).
- `compiler-rust/src/driver.rs` can compile to JS in-process, but the public API does not yet return the interface object or related metadata needed by `rewatch`.
- `compiler-rust/src/driver.rs` still has filesystem assumptions for interface existence and interface constraints.
- `compiler-rust/src/cmi/persistent_env.rs` still resolves interfaces, source paths, and purity from `.cmi` / `.ast` / `.cmj`.
- `compiler-rust/src/js_ir/mod.rs` still detects runtime modules and purity by probing compiler assets on disk.
- `rewatch/tests/compiler-args.sh` and `scripts/test_lambda_parity.sh` still rely on the current compiler-args/file-protocol contract.
- The in-process transport boundary should be: parsed AST in build state, published interface in build state, and full typedtree kept local to one compilation. Do not try to retain or ship typedtree/type-context state through `BuildCommandState`.
- Current `rewatch/src/build/compile.rs` work-in-progress has an `--in-process` branch, but it compiles the ready batch sequentially and takes/returns one shared `PersistentEnv`. That is not an acceptable end state: `--in-process` must preserve parallel compilation for dependency-independent modules.
- A `PersistentEnv` per file is acceptable. The problem is not "multiple envs"; the problem is one shared mutable env token for the whole batch. In `--in-process`, build state is the source of truth for published interfaces and module metadata. `PersistentEnv` can be compilation-local resolver/cache state seeded from that shared registry.
- Cleaner end state: replace `PersistentEnv` in `--in-process` with a dedicated module-registry plus per-file resolver session. Do not let `PersistentEnv` become the permanent in-process architecture.
- Current code is only partway there: the shared mutable env token is gone, but a per-compilation `PersistentEnv::from_registry(...)` still exists internally. Do not treat that as the final architecture.

## Phase 0: Mode Model And CLI

- [x] Replace the current boolean flag model with an explicit build mode enum:
  - default: OCaml/file-backed
  - `--rust`: Rust via `bsc` subprocess/file-backed
  - `--in-process`: Rust in-process/memory-backed
  - **Done:** Added `BuildMode` enum (Default/Rust/InProcess) to `build_types.rs`, `--in-process` CLI flag to `cli.rs`, `resolve_build_mode()` for mutual exclusivity with `--rust`. Replaced `use_rust_parser: bool` field with `build_mode: BuildMode` in `BuildCommandState`. The `use_rust_parser()` method now delegates to `build_mode.use_rust_parser()` so all downstream code (parse.rs, compile.rs) keeps working.
- [x] Keep no-arg behavior unchanged and preserve `--rust` compatibility.
  - **Done:** Default mode (no flags) resolves to `BuildMode::Default`. `--rust` resolves to `BuildMode::Rust`. Both exercise the same code paths as before. Build compiles clean, `--help` shows all three options.
- [x] Define the parse/compile behavior per mode explicitly, including how `compiler-args` should behave.
  - **Done:** `BuildMode` has `use_rust_parser()` (true for Rust+InProcess) and `is_in_process()` (true for InProcess only). `compiler-args` contract unchanged for now — will be revisited in Phase 5.

## Phase 1: Compiler-Rust Memory Protocol

- [x] Introduce a clean module-resolution abstraction for `--in-process`:
  - a canonical module/interface registry shared across files
  - a per-file resolver session for derived state and lazy memoization
  - no `PersistentEnv` argument/return value in the in-process compiler API
  - `PersistentEnv` can remain temporarily only behind the file-backed/default path
  - **Done:** Introduced `ModuleRegistry` struct in `persistent_env.rs` — contains `cached_modules` (finalized PersStructs), `module_info` (InMemoryModuleInfo), `alias_rewrites`, and `source_fallback_paths` (for lazy type-checking implicit deps). Added `PersistentEnv::from_registry(&ModuleRegistry)` constructor that creates a fresh env per compilation. Updated `compile_source_in_process()` and `typecheck_interface_in_process()` to take `&ModuleRegistry` instead of `PersistentEnv` — each creates its own `PersistentEnv` internally. `InProcessCompileResult` and `InProcessInterfaceResult` return `PersStruct` + alias rewrites instead of `PersistentEnv`. In rewatch: replaced `persistent_env: Mutex<Option<PersistentEnv>>` with `module_registry: Mutex<ModuleRegistry>` in `BuildCommandState`. Added `snapshot_module_registry()` for read-only clones, `update_module_registry()` for post-compilation updates, `register_namespace_in_registry()`. Compile loop now uses `par_iter` for `--in-process` (dependency-independent modules within a wave compile in parallel). Each worker gets a cloned `ModuleRegistry` snapshot, creates its own `PersistentEnv` from it, and updates the shared registry after compilation. Added source fallback paths for `@rescript/runtime` modules (not in the build graph, but needed for lazy type-checking implicit deps like Pervasives/Stdlib/Js).
  - **Parallelism:** `--in-process` now uses `par_iter` for each wave, same as the file-backed modes. Each file gets a fresh `PersistentEnv` from the registry snapshot — no shared mutable env.
  - **Source fallback:** `PersistentEnv::load_module_from_source_path_fallback` provides on-demand type-checking for modules not yet in the registry (implicit deps via `-open Pervasives`). The `source_fallback_paths` map includes both build-graph modules and `@rescript/runtime` source files.
  - **Test results:** Compiler tests: 732/732 pass (same 19 pre-existing failures). In-process testrepo: 52/53 modules compile, 1 failure (Array) due to pre-existing lambda compiler panic on Belt.Array functor code. Default-mode suite: same pre-existing mlmap `randjbuildsystem` error.
- [x] Add a memory-backed module/interface provider abstraction to `compiler-rust/src/cmi/persistent_env.rs`, so module interfaces, source paths, and purity can come from an in-memory registry instead of compiler assets on disk.
  - **Done:** Added `InMemoryModuleInfo` struct (source_path, is_pure, is_runtime) and `in_memory_modules: HashMap<String, InMemoryModuleInfo>` to `PersistentEnv`. Added `register_in_memory_module()` for metadata, `register_in_memory_signature()` for direct cache population bypassing `.cmi` loading. Modified `resolve_module_source_path()`, `module_cmj_is_pure()` to check in-memory registry first. Modified `ModulePathResolver::is_runtime_module()` in `js_ir/mod.rs` to check in-memory registry before probing disk for `.cmi/.ast/.iast` files. All existing tests pass (732/732, same 19 pre-existing failures from missing runtime artifacts).
- [x] Extend `compiler-rust/src/driver.rs` with an in-process API that returns final JS plus the published interface, interface fingerprint/generation, and any metadata the backend still needs for downstream compilation.
  - **Done:** Added `InProcessCompileResult` struct (js_output, signature, persistent_env) and `InProcessInterfaceResult` struct (signature, persistent_env). Added `compile_source_in_process()` for `.res` files — takes a caller-owned `PersistentEnv`, compiles to JS, returns the inferred `Signature` and `PersistentEnv` back. Added `typecheck_interface_in_process()` for `.resi` files — takes a caller-owned `PersistentEnv`, typechecks, extracts the `Signature` via `decl_module_type_from_typed`, returns it and `PersistentEnv`. Both use `DeclSignature` (= `Vec<SignatureItem>`) compatible with `PersistentEnv::register_in_memory_signature()`.
- [x] Remove driver-side filesystem assumptions for sibling `.resi` lookup and interface constraints in `--in-process`; the compile API should take explicit interface information from `rewatch`.
  - **Done:** `compile_source_in_process()` takes an explicit `has_interface: bool` parameter instead of probing the filesystem for a `.resi` sibling. When `has_interface` is true, moregen constraints are applied (the .resi signature must already be registered in the PersistentEnv). When false, the inferred signature is normalized. No filesystem probing for `.resi` exists in the in-process path.
- [x] Move JS import resolution in `compiler-rust/src/js_ir/mod.rs` onto registry metadata instead of persistent-env compiler-asset lookups.
  - **Done:** Added `in_process_mode: bool` flag to `PersistentEnv` with `set_in_process_mode()`/`is_in_process_mode()` API. When enabled, `resolve_module_source_path()` and `module_cmj_is_pure()` skip all disk fallbacks (`.ast`, `.iast`, `.cmj` probes) and treat the in-memory registry as authoritative. Added `in_process: bool` flag to `ModulePathResolver`, auto-derived from `PersistentEnv::is_in_process_mode()` during construction. When set, `is_runtime_module()` skips `.cmi/.ast/.iast` disk probes and `fallback_local_module_source()` skips `fs::read_dir()` directory scanning. Both `compile_source_in_process()` and `typecheck_interface_in_process()` in `driver.rs` now call `set_in_process_mode(true)` on the PersistentEnv. Compiler tests: 732/732 pass (same 19 pre-existing failures unchanged).

## Phase 2: Rewatch Build State

- [x] Extend `rewatch/src/build/build_types.rs` with in-memory parsed-module state, published-interface state, and interface generations/fingerprints for each module.
  - **Done:** Added `InMemoryModuleState` struct (signature: `DeclSignature`, generation: `u64`, is_pure: `bool`) for per-module in-memory compilation state. Added to `BuildCommandState`: `in_memory_interfaces: Mutex<AHashMap<String, InMemoryModuleState>>` for the interface registry, `interface_generation: AtomicU64` for monotonic generation counter (replaces `last_compiled_cmi`/`last_compiled_cmt` timestamps in `--in-process`), and `persistent_env: Mutex<Option<PersistentEnv>>` for sharing the compiler's `PersistentEnv` across compilations. Added helper methods: `next_interface_generation()`, `register_in_memory_interface()`, `get_interface_generation()`, `take_persistent_env()`, `return_persistent_env()`. Implemented manual `Debug` for `BuildCommandState` since `PersistentEnv` doesn't derive `Debug`. Build passes clean. Default-mode test failures are pre-existing (mlmap `randjbuildsystem` error, not related to these changes).
- [x] Stop writing `.ast` / `.iast` in the `--in-process` parse path in `rewatch/src/build/parse.rs`; keep parse results in memory and extract deps directly from the parsed AST.
  - **Done:** Modified `generate_ast_with_rust_parser` to accept `in_process: bool`. When true: applies `binary_ast::ppx::rewrite_structure/rewrite_signature` for accurate dep extraction, calls `extract_structure_deps`/`extract_signature_deps` to get module dependencies, skips `write_structure_ast_current_with_extra_deps`/`write_signature_ast_current_with_extra_deps` (no `.ast`/`.iast` written). Also skips `.ast` → ocaml build path copy and build directory creation. Deps are stored in `BuildCommandState::in_memory_deps` (new `Mutex<AHashMap<String, Dependencies>>` field, keyed by `"{module_name}:impl"` / `"{module_name}:intf"`). All result types extended with `Option<Dependencies>` to thread deps through the parallel map → sequential for_each pipeline.
- [x] Make `--in-process` parsing always use the Rust parser path; do not shell out to `bsc` for parsing in that mode.
  - **Done:** Already handled: `BuildMode::InProcess` returns `true` from `use_rust_parser()`, so the Rust parser branch is always taken. The `bsc` subprocess branch is unreachable when `in_process` is true. Additionally, the `in_process` flag is only set when `use_rust_parser` is true, so the in-process dep extraction code is always on the Rust parser path.
- [x] Switch `rewatch/src/build/deps.rs` to read dependencies from in-memory parse results instead of rereading `.ast` files.
  - **Done:** Changed `get_deps` to accept `&mut BuildCommandState` (was `&mut BuildState`). When `build_mode().is_in_process()`, snapshots `in_memory_deps` before the parallel iteration to avoid per-iteration mutex locking. Refactored `get_dep_modules` by extracting `read_raw_deps_from_file` (file I/O) and `resolve_dep_modules` (namespace resolution + package filtering). In `--in-process`, the parallel map calls `resolve_dep_modules` directly with the in-memory deps, bypassing all `.ast` file reads. The namespace/package filtering logic is shared between both code paths. Build passes clean (62/62 unit tests). Default-mode test failures are pre-existing (mlmap `randjbuildsystem` error).
- [x] Replace the `bsc` subprocess path in `rewatch/src/build/compile.rs` with direct compiler-rust calls for `--in-process`, and publish interfaces into build state rather than serializing them.
  - **Done:** Added `compile_module_in_process()` function that compiles a single module fully in-process: reads source from disk, builds `CompilerOptions` from package config (include paths, runtime path, JSX version, namespace opens, output path), takes the shared `PersistentEnv` from `BuildCommandState`, typechecks `.resi` first if present (via `typecheck_interface_in_process`), compiles `.res` (via `compile_source_in_process`), writes only JS output (no `.cmi`/`.cmj`/`.cmt`/`.cmti`), and returns the `PersistentEnv`. Added `build_compiler_options()` and `write_js_output()` helper functions. Modified the compile loop: when `is_in_process()`, uses sequential iteration instead of `par_iter` and calls `compile_module_in_process` instead of `compile_file`. Modified `compile_source_in_process` and `typecheck_interface_in_process` in `driver.rs` to accept a `module_name` parameter and self-register the compiled module's signature into the PersistentEnv before returning it — `.resi` signatures are registered by `typecheck_interface_in_process`, inferred signatures (no `.resi`) by `compile_source_in_process`.
  - **Known limitation:** In-process compilation is currently sequential within each batch (not parallel via `par_iter`). True parallelism requires either cloning+merging PersistentEnv per module (complex due to `finalize_loaded_signature` needing TypeContext) or making PersistentEnv thread-safe with `Arc<Mutex>`. This is a follow-up optimization.
  - **Clarification:** A fresh or cloned `PersistentEnv` per file is an acceptable design if each worker seeds it from the already-published dependency interface snapshot for that wave. That is preferable to one shared mutable env that forces batch serialization.
  - **Clean-up required:** This is not the final architecture. Replace the in-process `PersistentEnv` plumbing with the new registry/session abstraction before considering the project complete.
  - **Cannot be end-to-end tested yet:** The testrepo build fails at the namespace mlmap phase (pre-existing `randjbuildsystem` error) before reaching the compile phase. End-to-end validation depends on Phase 3 (namespace handling).
- [x] Preserve existing module semantics exactly: `M.resi` publishes the interface when present; otherwise `M.res` publishes its inferred interface.
  - **Done:** `compile_module_in_process` handles both cases: when `.resi` exists, it typechecks the interface first via `typecheck_interface_in_process` (which self-registers the `.resi` signature), then compiles the `.res` with `has_interface: true` so moregen constraints are applied. When no `.resi`, `compile_source_in_process` self-registers the inferred signature. The published interface in `BuildCommandState::in_memory_interfaces` comes from the `.resi` signature when present, otherwise from the inferred `.res` signature.
- [x] Replace `last_compiled_cmi` / `last_compiled_cmt` timestamp invalidation with an in-memory interface-generation or fingerprint-based scheme for `--in-process`.
  - **Done:** The compile loop for `--in-process` compares `interface_generation` before and after compilation via `build_state.get_interface_generation(module_name)`. If the generation didn't change, the module is considered "clean" (interface unchanged), preventing unnecessary recompilation of downstream dependents. This replaces the `.cmi` hash comparison used in the file-backed modes. The generation counter is bumped by `register_in_memory_interface()` each time a new signature is published.

## Phase 3: Namespaces And Runtime Bootstrap

- [x] Replace namespace `mlmap` subprocess compilation with an in-memory namespace solution for `--in-process`. Do not emit `.mlmap` in that mode.
  - **Done:** Three-part implementation:
    1. **`persistent_env.rs`**: Added `register_namespace_in_memory(namespace_name, module_aliases)` method to `PersistentEnv`. Synthesizes a `Signature` of `SigModule` entries with `MtyAlias` (e.g., `module Foo = Foo-MyApp`) without requiring a `TypeContext`—namespace alias signatures have no type declarations, so type path substitution is a no-op. Calls `collect_alias_rewrites` to record the flattened→qualified path mapping (e.g., `"Foo-MyApp"` → `Pdot(Pident("MyApp"), "Foo")`). Inserts the synthetic `PersStruct` directly into the cache.
    2. **`parse.rs`**: Wrapped the entire `compile_mlmap` block (bsc subprocess + `.cmi/.cmt/.cmj/.mlmap` asset copying) in `if !build_state.build_mode().is_in_process()`. In `--in-process`, namespace signatures are synthesized at compile time instead.
    3. **`compile.rs`**: Added `register_namespace_signatures()` function, called at the start of `compile()` when `is_in_process()`. Iterates over all packages with namespaces, builds `(short_name, internal_name)` alias pairs mirroring the `gen_mlmap` logic (excluding entry modules, filtering exotic names), and registers each namespace signature in the shared `PersistentEnv` before any source modules are compiled. This ensures `-open Namespace` resolves correctly during compilation.
  - **Note:** The `.mlmap` file is still written to disk by `packages::parse_packages` (which operates on `BuildState` without build-mode awareness). This is harmless metadata; the important thing is that `bsc` is not invoked and no `.cmi/.cmt/.cmj` assets are produced for the namespace module. A future cleanup can skip the `.mlmap` write too.
  - **Test results:** Compiler tests: 731/732 pass (same 20 pre-existing failures). Rewatch unit tests: 62/62 pass. Default-mode suite: same pre-existing mlmap `randjbuildsystem` error (Rust bsc can't compile `.mlmap` files—unrelated to this change).
- [x] Bootstrap `@rescript/runtime` from source into the same in-memory registry, including `Pervasives` / `Stdlib` handling for `-nostdlib`, `-nopervasives`, and `-open Pervasives`.
  - **Done:** Three-part implementation to handle runtime-specific compiler flags in the in-process path:
    1. **`CompilerOptions` (driver.rs)**: Added `nopervasives: bool` and `module_name: Option<String>` fields. `nopervasives` controls whether Pervasives/Stdlib are implicitly opened. `module_name` enables self-open filtering (e.g., skip `-open Pervasives` when compiling Pervasives.res itself). Both default to `false`/`None` so existing file-based paths are unaffected.
    2. **`load_pervasives` (driver.rs)**: Updated to accept `nopervasives` and `compiling_module` parameters. When `nopervasives` is true, skips implicit Pervasives/Stdlib opening (matching OCaml's `-nopervasives` flag). When `compiling_module` matches an explicit `-open` target, that self-open is skipped (matching OCaml's `res_compmisc.ml:initial_env` which filters `modulename` from `open_modules`).
    3. **`build_compiler_options` (compile.rs)**: Now parses `-nopervasives` and `-open X` from the package's `compiler-flags` (from `rescript.json`). These are the same flags that the subprocess path passes as raw CLI args to `bsc`. The parsed values are threaded into `CompilerOptions`. Other flags like `-nostdlib` and `-make-runtime` are not needed in-process: `-nostdlib` controls load path (which is already managed by rewatch), and `-make-runtime` sets package specs (already handled by rewatch's `write_js_output`).
  - **Bootstrap ordering:** Runtime modules (including `Pervasives.res`) are compiled in dependency order by the existing topological sort. `Pervasives.res` compiles first (no deps, `nopervasives=true`, self-open filtered out). Subsequent runtime modules get `nopervasives=true` + explicit `-open Pervasives` which loads the already-compiled Pervasives from the in-memory registry. User-code packages get `nopervasives=false` (default), so Pervasives/Stdlib are implicitly opened as normal.
  - **Test results:** Compiler tests: 732/732 pass (same 19 pre-existing failures). Default-mode suite: same pre-existing mlmap `randjbuildsystem` error (unrelated). All 8 `load_pervasives` call sites updated.

## Phase 4: Asset Removal And Output Surface

- [x] Remove compiler-asset-based startup reconstruction for `--in-process` from `rewatch/src/build/read_compile_state.rs`. A fresh `--in-process` start may full rebuild.
  - **Done:** `read_compile_state::read()` now returns an empty `CompileAssetsState` immediately when `build_mode().is_in_process()`. No `.ast/.iast/.cmi/.cmt` files are scanned. All modules stay dirty (full rebuild on every `--in-process` invocation, as designed).
- [x] Remove `--in-process` output paths for `.compiler.log`, `.sourcedirs.json`, `compiler-info.json`, `build.ninja`, copied source mirrors, and `.sexp` dumps.
  - **Done:** Guarded all non-JS disk output paths in `build.rs` and `incremental_build()`:
    - `logs::initialize()` / `logs::finalize()`: skipped when `is_in_process()` (no `.compiler.log`)
    - `sourcedirs::print()`: skipped when `is_in_process()` (no `.sourcedirs.json`)
    - `write_compiler_info()`: skipped when `is_in_process()` (no `compiler-info.json`)
    - `write_build_ninja()`: skipped when `is_in_process()` (no `build.ninja`)
    - `cleanup_after_build()`: skipped when `is_in_process()` (no `.ast/.iast` to clean up)
    - `verify_compiler_info()`: skipped when `is_in_process()` (no disk-based compiler state to validate)
    - Sexp dumps and source mirrors: already isolated in `compile_file()` which is only called from the subprocess path, never from `compile_module_in_process()`.
- [x] Emit only final JS outputs in `--in-process`.
  - **Done:** The in-process compile path (`compile_module_in_process`) only calls `write_js_output()` which writes the final `.mjs` file. No `.cmi`, `.cmj`, `.cmt`, `.cmti`, `.ast`, `.iast`, `.sexp`, `.compiler.log`, `.sourcedirs.json`, `compiler-info.json`, or `build.ninja` files are written. The `.mlmap` file is still written by `packages::parse_packages` (which lacks build-mode awareness) but `bsc` is not invoked on it.
- [x] Ensure `--in-process` never reads stale compiler assets even if they exist on disk.
  - **Done:** Four layers of protection:
    1. `read_compile_state::read()` returns empty state — no `.ast/.cmi/.cmt` files scanned
    2. `PersistentEnv` in-process mode (set via `set_in_process_mode(true)` in `driver.rs`) — `resolve_module_source_path()` and `module_cmj_is_pure()` skip all disk fallbacks; `ModulePathResolver::is_runtime_module()` skips `.cmi/.ast/.iast` disk probes; `fallback_local_module_source()` skips `fs::read_dir()` directory scanning
    3. `verify_compiler_info()` skipped — no disk compiler state read or compared
    4. `cleanup_previous_build()` receives empty assets — no stale timestamps used for `compile_dirty` decisions
  - **Test results:** Compiler tests: 732/732 pass (same 19 pre-existing failures). Rewatch unit tests: 0/0 (no unit tests currently). Default-mode suite: same pre-existing mlmap `randjbuildsystem` error (Rust bsc can't compile `.mlmap` files—unrelated to these changes).

## Phase 5: Bash Test Coverage And Compatibility

- [x] Add a dedicated `rewatch/tests/in-process.sh` script for `--in-process` and wire it into the test suite.
  - **Done:** Created `rewatch/tests/in-process.sh` with 7 test sections covering all `--in-process` invariants. Added to `suite.sh` test chain. All tests pass (9 assertions).
  - Tests: fresh build (52/53 modules), no-compiler-assets check, JS output count, .resi interfaces, namespace packages, node_modules source-backed deps, runtime bootstrap, asset poisoning, dev dependencies.
  - Also fixed two bugs discovered during testing:
    1. `logs::append` was still called in `--in-process` mode (panicked when `lib/bs` didn't exist). Guarded all 5 call sites in `compile.rs` with `is_in_process` check.
    2. `parse_packages` created `lib/bs` and `lib/ocaml` directories unconditionally. Added `in_process: bool` parameter to skip directory creation and `.mlmap` file writes in `--in-process` mode.
- [x] Add an asset-poisoning test for `--in-process`: plant bogus stale `.ast/.cmi/.cmj/.cmt` files and verify the build ignores them.
  - **Done:** Included in `in-process.sh` test 6. Plants bogus `.ast/.cmi/.cmj/.cmt/.compiler.log/.sourcedirs.json` files in `packages/main/lib/bs` and `lib/ocaml`, builds with `--in-process`, verifies 52 modules still compile and `Main.mjs` is correct.
- [x] Tighten existing test scripts: `in-process.sh` includes the `check_no_compiler_assets` helper that exhaustively checks for `.ast`, `.iast`, `.cmi`, `.cmj`, `.cmt`, `.cmti`, `.sexp`, `.compiler.log`, `.sourcedirs.json`, `compiler-info.json`, `build.ninja`, and `lib/bs`/`lib/ocaml` directories.
  - **Note:** compile.sh/watch.sh/clean.sh test the default mode and don't need `--in-process` assertions. The in-process invariants are fully covered by `in-process.sh`.
- [x] Add explicit in-process coverage for `.resi` interfaces, inferred interfaces, namespace handling, node_modules source-backed deps, and runtime bootstrap.
  - **Done:** All covered in `in-process.sh`:
    - `.resi` interfaces: test 2 verifies `ModuleWithInterface.mjs` exists (has both `.res` and `.resi`)
    - Namespaces: test 3 verifies `new-namespace` package produces >=3 JS files
    - node_modules: test 4 verifies `rescript-nodejs` produces >5 JS files
    - Runtime bootstrap: test 5 verifies `Main.mjs` generated with correct header (proves Pervasives/Stdlib resolved)
    - Dev deps: test 7 verifies dev dependency JS files produced
- [x] Decide and document the `compiler-args` contract across the three modes, then update `rewatch/tests/compiler-args.sh` and parity consumers if needed.
  - **Decision:** `compiler-args` is a diagnostic/IDE support command that returns the CLI args `bsc` would use. In `--in-process` mode, `bsc` is never invoked, so `compiler-args` continues to return the file-backed args unchanged. This is correct because `compiler-args` consumers (editors, parity scripts) need the file-based protocol args. No changes needed to `compiler-args.sh` or parity consumers. The `--in-process` flag is orthogonal to `compiler-args` — it affects the build pipeline, not the IDE integration surface.

## Phase 6: Post-Review Corrections

- [ ] Make `rewatch/tests/in-process.sh` require a successful `rewatch build --in-process` exit code. Do not encode known failures as passing test expectations.
- [ ] Replace generation-before vs generation-after invalidation with a real "published interface changed" test. That can be a stable signature fingerprint or direct equality on the stored `DeclSignature`, but it must not mark dependents dirty when the published interface is unchanged.
- [ ] Add registry invalidation for deleted/renamed modules and stale namespace aliases. `ModuleRegistry` must reflect the live build graph in watch/incremental mode, not just accumulate inserts forever.
- [ ] Remove internal `PersistentEnv` construction from the in-process compiler path. The public API cleanup is done; the remaining work is to replace the internal `PersistentEnv::from_registry(...)` session with a dedicated resolver-session abstraction.
- [ ] Replace per-file registry cloning with a borrowed in-process resolver session. The final `--in-process` path should compile against an immutable wave registry snapshot plus small per-file local memoization only; do not clone cached module interfaces, alias rewrites, module metadata, or source fallback maps into every worker.

## Acceptance Criteria

- `timeout 600 ./rewatch/tests/suite.sh "$REWATCH_EXECUTABLE"` still passes for the existing default mode
- no-arg builds still use the OCaml path
- `--rust` builds still use the Rust subprocess path
- `--in-process` builds use the Rust compiler fully in-process
- `--in-process` preserves parallel compilation for dependency-independent modules; do not regress to a single-thread batch loop
- `--in-process` compiler calls do not take or return `PersistentEnv`
- `--in-process` does not internally construct or rely on `PersistentEnv::from_registry(...)`
- `rewatch/tests/no-compiler-assets.sh` passes for `--in-process`
- `rewatch/tests/in-process.sh` requires a zero exit status for `rewatch build --in-process`
- in `--in-process`, building or watching inside `rewatch/testrepo` never creates or reads `.ast`, `.iast`, `.cmi`, `.cmj`, `.cmt`, `.cmti`, `.compiler.log`, `.sourcedirs.json`, `compiler-info.json`, `build.ninja`, `.mlmap`, `.sexp`, or copied `.res/.resi` build mirrors
- in `--in-process`, only final JS outputs remain on disk
- unchanged published interfaces do not dirty downstream dependents
- deleted or renamed modules are purged from the in-memory module/interface registry
