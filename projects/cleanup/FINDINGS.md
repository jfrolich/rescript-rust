# Cleanup Findings

Findings are ordered by release risk. Line numbers refer to the reviewed head.

## P0 Release Blockers

1. `bsc` package bin points to a deleted file.

   `package.json:46-48` still declares `"bsc": "cli/bsc.js"`, while
   `cli/bsc.js` is deleted and `packages/artifacts.json:7-15` no longer ships
   it. A beta package would expose a broken `bsc` executable unless this wrapper
   is restored or the bin entry is changed to a shipped file.

2. Absolute local symlinks are tracked.

   `compiler-rust/compiler-rust` is a symlink to
   `/Users/jake/dev/rescript-rust/compiler-rust`, and `packages/packages` is a
   symlink to `/Users/jake/dev/rescript-rust/packages`. These will be broken for
   every other checkout and should not be in a release branch.

3. Machine-local build artifacts are tracked.

   `lib/bs/.sourcedirs.json:1` contains `/Users/jake/dev/rescript-rust/...`
   package paths. `lib/bs/compiler-info.json:3` and
   `lib/bs/compiler-info.json:6` contain local `bsc_path` and `runtime_path`
   values. `lib/bs/build.ninja` is an empty generated file. These are build
   outputs, not source.

4. The Rust compiler writes unconditional debug files to `/tmp`.

   `compiler-rust/src/driver.rs:12842-12888` always populates a debug vector and
   writes `/tmp/moregen_debug_<module>.txt` for `.res` files with interfaces.
   This is not gated by an env var and can leak files during normal builds.

5. A deleted test helper is still imported.

   `tests/tests/src/tagged_template_lib.js` was deleted, but
   `tests/tests/src/tagged_template_test.res:5`,
   `tests/tests/src/tagged_template_test.res:18`,
   `tests/tests/src/tagged_template_test.mjs:5`, and
   `tests/tests/src/tagged_template_test.ocaml.mjs:5` still import
   `./tagged_template_lib.js`.

## P1 Must Review Before Beta

6. Generated snapshots and performance cache files are tracked.

   The diff adds 657 `tests/tests/src/*.ocaml.mjs` files, 49
   `tests/tests/src/*.js` files, `.performance-cache/typechecker/latest.csv`,
   and `.performance-cache/typechecker/latest.json`. The performance JSON has a
   `generated_at_epoch_s` field and machine-run timing data. These should be
   removed unless the release policy explicitly versions them.

7. One-off migration scripts are tracked.

   `fix_boxing.py:19` hard-codes
   `/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust/src`.
   `compiler-rust/fix_all_boxing.py:13` hard-codes
   `/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust`.
   The `compiler-rust/fix_*.py` files rewrite source files in place. These look
   like historical migration tools and should be removed or moved to a documented
   maintenance area before beta.

8. GenType has a reachable staged `unimplemented!`.

   `compiler-rust/src/gentype/main.rs:496-501` reads CMT files and calls
   `unimplemented!("Cmt_format.read_cmt typedtree decoding is wired in Phase 3")`
   for valid CMT magic. If beta exposes this path through `-bs-gentype`, it will
   panic.

9. New `unsafe` code needs explicit release review.

   New Rust compiler code uses `unsafe` in `compiler-rust/src/types/context.rs:57-77`,
   synthetic parse-arena mutation paths such as
   `compiler-rust/src/types/typecore.rs:3381-3424` and
   `compiler-rust/src/types/typecore.rs:6437-6504`, plus `unsafe impl Send/Sync`
   in `compiler-rust/src/raw_lambda/matching.rs:8678-8694`. This conflicts with
   the repository guidance against new unsafe compiler code unless invariants are
   narrowly documented and justified.

10. OCaml reference compiler has debug instrumentation in hot paths.

    `compiler/ml/ctype.ml:112-147`, `compiler/ml/ctype.ml:913-956`,
    `compiler/ml/ctype.ml:2596-2689`, and `compiler/ml/typecore.ml:417-510`
    add env-controlled debug code. `compiler/ml/typecore.ml:2758-2774`,
    `compiler/ml/typecore.ml:2896-2912`, and
    `compiler/ml/typecore.ml:3733-3810` add extra status-specific debug checks.
    Even when gated, repeated `Sys.getenv_opt` and debug-only branches in
    typechecker hot paths should be removed or cached before beta.

11. Several new scripts are not portable.

    `scripts/test_typedtree_parity.sh:141`,
    `scripts/test_lambda_parity.sh:94`,
    `scripts/profile_rust_errors.sh:11`, and
    `scripts/categorize_failures.py:28` hard-code `darwin-arm64` instead of
    using `scripts/platform.sh`. `scripts/test_gentype_output_parity.sh:29`
    hard-codes `/Users/jake/dev/tella-fusion` instead of defaulting through
    `TELLA_DIR`.

12. New scripts use variable-based `rm -rf` cleanup.

    Examples include `scripts/test_parser_ast_parity.sh:241`,
    `scripts/test_parser_ast_parity.sh:519`,
    `scripts/test_parser_ast0_parity.sh:191`,
    `scripts/test_parser_ast0_parity.sh:380`,
    `scripts/benchmark_parser.sh:45`,
    `scripts/profile_rust_errors.sh:17`,
    `scripts/test_js_single.sh:133`, and
    `scripts/test_js_failing.sh:167`. These are new-script cleanup patterns and
    should be made safer before beta.

13. The duplicated symlinked packages fixture no longer tests symlinks.

    The diff deletes symlinks under
    `tests/build_tests/duplicated_symlinked_packages/...` and replaces them with
    real package directories. If the fixture is meant to test duplicated
    symlinked packages, this changes the behavior under test.

## P2 Cleanup / Decision Items

14. `playground/public/stdlib.json` is a generated 1.9 MB one-line asset.

    `playground/scripts/bundle-stdlib.js` generates it from
    `packages/@rescript/runtime`. Decide whether this is intentionally checked
    in for playground deployment or should be generated during the playground
    build.

15. `CLAUDE.md` changed from symlink to regular file.

    The content points to `AGENTS.md` but now duplicates local assistant rules.
    This may be intentional, but the type change should be confirmed before
    release.

16. Rewatch now ships telemetry and a global allocator.

    `rewatch/src/main.rs:6-7` installs `mimalloc` globally, and
    `rewatch/src/telemetry.rs` enables OTLP export when OTEL endpoint env vars
    are set. This is opt-in, but the dependency footprint and process shutdown
    behavior should be accepted explicitly for beta.

17. Rust release profile uses `panic = "abort"`.

    `compiler-rust/Cargo.toml` sets release panics to abort while the compiler
    still has user-reachable panic sites. Confirm this is acceptable for beta
    binaries or change the release profile.
