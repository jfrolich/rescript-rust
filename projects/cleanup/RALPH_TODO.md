# Cleanup TODO

## P0 Release Blockers

- [x] Restore or replace `cli/bsc.js`, or update `package.json` `bin.bsc` and
  `packages/artifacts.json` together so beta packages expose a working `bsc`.
- [x] Remove tracked absolute symlinks:
  `compiler-rust/compiler-rust` and `packages/packages`.
- [x] Remove generated local build artifacts under `lib/bs/`.
- [x] Remove generated `.performance-cache/typechecker/*` files from the
  branch.
- [x] Remove or env-gate the `/tmp/moregen_debug_<module>.txt` write in
  `compiler-rust/src/driver.rs`.
- [x] Restore `tests/tests/src/tagged_template_lib.js` or update all imports and
  generated snapshots that reference it.

## P1 Must Review

- [x] Remove generated snapshots and keep generated outputs aligned with
  upstream snapshot policy.
- [x] Remove one-off migration scripts (`fix_boxing.py` and
  `compiler-rust/fix_*.py`).
- [x] Replace the GenType CMT-read panic with a controlled diagnostic.
- [x] Review each new `unsafe` block and either refactor to safe Rust or add a
  narrow invariant comment and release justification.
- [x] Remove OCaml debug instrumentation from hot paths.
- [x] Replace hard-coded platform and personal checkout paths in new scripts.
- [x] Replace new variable-based directory cleanup in scripts with safer
  file-specific deletion or existing repository cleanup behavior.
- [x] Preserve the symlink semantics of
  `tests/build_tests/duplicated_symlinked_packages`.

## P2 Decisions

- [x] Remove generated `playground/public/stdlib.json` from the branch.
- [x] Keep `CLAUDE.md` as a regular Claude-specific entry point that points to
  `AGENTS.md`.
- [x] Keep rewatch `mimalloc` and optional OTLP telemetry as intentional
  behavior, with comments.
- [x] Remove `compiler-rust` release `panic = "abort"`.

## Follow-Up Cleanup

- [x] Remove stale project temp artifacts from `projects/**/.tmp/`.
- [x] Remove committed `dbg!` macros from rewatch config tests.
- [x] Parameterize the personal Hyperindex replay checkout path.
- [x] Make stale AST parity helpers platform-aware.
- [x] Fix the rewatch watcher test helper after the `BuildCommandState::new`
  signature change.
- [x] Move root parity scratch notes under `projects/`.
- [x] Isolate `ralph.sh` output files per run.
- [x] Add a prepack guard for platform package binaries.
- [x] Compact the JS output parity handoff.
- [x] Make the remaining binary-AST and typechecker benchmark helpers
  platform-aware.
- [x] Remove redundant rewatch watcher fields that produced debug-build warning
  noise.
- [x] Replace a personal-looking binary AST writer test fixture path with a
  neutral absolute path.
- [x] Restore the compiler-rust lib-test target enough for focused tests to run.
- [x] Make the JS output parity wrapper skip Spice PPX AST parity by default,
  with explicit opt-in.
- [x] Make the full `cargo test --manifest-path compiler-rust/Cargo.toml --lib`
  suite green, or split/retire stale JS/lambda unit tests with a documented
  replacement gate.

## Verification Commands

Run from the repo root after cleanup changes:

```bash
git status --short
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
./scripts/test_typedtree_parity.sh --quick
./scripts/test_lambda_parity.sh --quick
./scripts/test_js_output_parity.sh
npm pack --dry-run
```

Use debug artifacts for iteration. Only run release builds when explicitly
testing release packaging or performance.
