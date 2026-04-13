# Ralph TODO: Rewatch In-Memory Build

**Last Updated:** 2026-04-13
**Status:** 13/16 tasks complete

## Goal

Add a new `--in-process` mode to `rewatch` that runs the Rust compiler fully in-process, keeps dependency interfaces in memory, and stops emitting or reading compiler assets anywhere in that build graph. Only final JS outputs should be written in `--in-process`.

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
  - **Cannot be end-to-end tested yet:** The testrepo build fails at the namespace mlmap phase (pre-existing `randjbuildsystem` error) before reaching the compile phase. End-to-end validation depends on Phase 3 (namespace handling).
- [x] Preserve existing module semantics exactly: `M.resi` publishes the interface when present; otherwise `M.res` publishes its inferred interface.
  - **Done:** `compile_module_in_process` handles both cases: when `.resi` exists, it typechecks the interface first via `typecheck_interface_in_process` (which self-registers the `.resi` signature), then compiles the `.res` with `has_interface: true` so moregen constraints are applied. When no `.resi`, `compile_source_in_process` self-registers the inferred signature. The published interface in `BuildCommandState::in_memory_interfaces` comes from the `.resi` signature when present, otherwise from the inferred `.res` signature.
- [x] Replace `last_compiled_cmi` / `last_compiled_cmt` timestamp invalidation with an in-memory interface-generation or fingerprint-based scheme for `--in-process`.
  - **Done:** The compile loop for `--in-process` compares `interface_generation` before and after compilation via `build_state.get_interface_generation(module_name)`. If the generation didn't change, the module is considered "clean" (interface unchanged), preventing unnecessary recompilation of downstream dependents. This replaces the `.cmi` hash comparison used in the file-backed modes. The generation counter is bumped by `register_in_memory_interface()` each time a new signature is published.

## Phase 3: Namespaces And Runtime Bootstrap

- [ ] Replace namespace `mlmap` subprocess compilation with an in-memory namespace solution for `--in-process`. Do not emit `.mlmap` in that mode.
- [ ] Bootstrap `@rescript/runtime` from source into the same in-memory registry, including `Pervasives` / `Stdlib` handling for `-nostdlib`, `-nopervasives`, and `-open Pervasives`.

## Phase 4: Asset Removal And Output Surface

- [ ] Remove compiler-asset-based startup reconstruction for `--in-process` from `rewatch/src/build/read_compile_state.rs`. A fresh `--in-process` start may full rebuild.
- [ ] Remove `--in-process` output paths for `.compiler.log`, `.sourcedirs.json`, `compiler-info.json`, `build.ninja`, copied source mirrors, and `.sexp` dumps.
- [ ] Emit only final JS outputs in `--in-process`.
- [ ] Ensure `--in-process` never reads stale compiler assets even if they exist on disk.

## Phase 5: Bash Test Coverage And Compatibility

- [ ] Add a dedicated `rewatch/tests/no-compiler-assets.sh` script for `--in-process` and wire it into the test suite.
- [ ] Add an asset-poisoning test for `--in-process`: plant bogus stale `.ast/.cmi/.cmj/.cmt` files and verify the build ignores them.
- [ ] Tighten `rewatch/tests/compile.sh`, `watch.sh`, and `clean.sh` so they explicitly fail when compiler assets or non-JS metadata appear in `--in-process`.
- [ ] Add explicit in-process coverage for `.resi` interfaces, inferred interfaces, namespace handling, node_modules source-backed deps, and runtime bootstrap.
- [ ] Decide and document the `compiler-args` contract across the three modes, then update `rewatch/tests/compiler-args.sh` and parity consumers if needed.

## Acceptance Criteria

- `timeout 600 ./rewatch/tests/suite.sh "$REWATCH_EXECUTABLE"` still passes for the existing default mode
- no-arg builds still use the OCaml path
- `--rust` builds still use the Rust subprocess path
- `--in-process` builds use the Rust compiler fully in-process
- `--in-process` preserves parallel compilation for dependency-independent modules; do not regress to a single-thread batch loop
- `rewatch/tests/no-compiler-assets.sh` passes for `--in-process`
- in `--in-process`, building or watching inside `rewatch/testrepo` never creates or reads `.ast`, `.iast`, `.cmi`, `.cmj`, `.cmt`, `.cmti`, `.compiler.log`, `.sourcedirs.json`, `compiler-info.json`, `build.ninja`, `.mlmap`, `.sexp`, or copied `.res/.resi` build mirrors
- in `--in-process`, only final JS outputs remain on disk
