# Cleanup TODO

## P0 Release Blockers

- [ ] Restore or replace `cli/bsc.js`, or update `package.json` `bin.bsc` and
  `packages/artifacts.json` together so beta packages expose a working `bsc`.
- [ ] Remove tracked absolute symlinks:
  `compiler-rust/compiler-rust` and `packages/packages`.
- [ ] Remove generated local build artifacts under `lib/bs/`.
- [ ] Remove `.performance-cache/typechecker/latest.csv` and
  `.performance-cache/typechecker/latest.json` unless they are explicitly
  release fixtures.
- [ ] Remove or env-gate the `/tmp/moregen_debug_<module>.txt` write in
  `compiler-rust/src/driver.rs`.
- [ ] Restore `tests/tests/src/tagged_template_lib.js` or update all imports and
  generated snapshots that reference it.

## P1 Must Review

- [ ] Decide whether `tests/tests/src/*.ocaml.mjs` and added generated `.js`
  files are intended to be committed. If not, remove them and document the
  snapshot-generation policy.
- [ ] Remove one-off migration scripts (`fix_boxing.py` and
  `compiler-rust/fix_*.py`) or move them to a documented maintenance directory
  after stripping personal absolute paths.
- [ ] Finish or hide the GenType CMT-read path so
  `compiler-rust/src/gentype/main.rs:501` cannot panic in beta usage.
- [ ] Review each new `unsafe` block and either refactor to safe Rust or add a
  narrow invariant comment and release justification.
- [ ] Remove OCaml debug instrumentation from `compiler/ml/ctype.ml` and
  `compiler/ml/typecore.ml`, or cache the env flags and document why it remains.
- [ ] Replace hard-coded `darwin-arm64` and personal Tella paths in new scripts.
- [ ] Replace new variable-based `rm -rf` cleanup in scripts with validated temp
  cleanup helpers or file-specific deletion.
- [ ] Preserve the symlink semantics of
  `tests/build_tests/duplicated_symlinked_packages` if that fixture is still
  intended to test symlinked dependencies.

## P2 Decisions

- [ ] Decide whether `playground/public/stdlib.json` should be committed or
  generated as part of `playground` build/deploy.
- [ ] Confirm `CLAUDE.md` should be a regular file instead of a symlink to
  `AGENTS.md`.
- [ ] Confirm `mimalloc` and optional OTLP telemetry are intended for beta
  rewatch binaries.
- [ ] Confirm `compiler-rust` release `panic = "abort"` is acceptable for beta.

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
