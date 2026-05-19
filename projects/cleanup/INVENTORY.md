# Cleanup Inventory

## Diff Summary

Base: `0a51c27b718bb8e49d88cd570d1dc6dcfba627f9`

Head: `22e9d4247dd416989df8672cc201b068ec5b4a5c`

`git diff --shortstat`:

```text
2103 files changed, 548166 insertions(+), 768 deletions(-)
```

Path status counts:

```text
2059 A
   6 D
  37 M
   1 T
```

## Added Files by Top-Level Area

```text
1719 tests
 195 compiler-rust
  76 projects
  27 scripts
  19 playground
   6 compiler
   5 src
   4 lib
   2 .performance-cache
   1 rewatch
   1 ralph.sh
   1 packages
   1 fix_boxing.py
   1 MATCHING_PORT_CHECKLIST.md
   1 DICT_PATTERN_ANALYSIS.md
```

## Added Files by Type

```text
183 .rs files
 14 .py files
 81 .md files
 22 .json files
  2 .csv files
675 .mjs files
657 .ocaml.mjs generated JS snapshots
  3 lock files
```

## Modified Files

```text
.github/workflows/ci.yml
.gitignore
AGENTS.md
Makefile
compiler/bsc/rescript_compiler_main.ml
compiler/core/js_implementation.ml
compiler/core/lam_compile_main.ml
compiler/frontend/bs_ast_mapper.ml
compiler/ml/clflags.ml
compiler/ml/clflags.mli
compiler/ml/ctype.ml
compiler/ml/typecore.ml
compiler/syntax/cli/dune
compiler/syntax/cli/res_cli.ml
compiler/syntax/src/res_ast_debugger.ml
compiler/syntax/src/res_ast_debugger.mli
package.json
packages/artifacts.json
rewatch/Cargo.lock
rewatch/Cargo.toml
rewatch/rust-toolchain.toml
rewatch/src/build.rs
rewatch/src/build/build_types.rs
rewatch/src/build/clean.rs
rewatch/src/build/compile.rs
rewatch/src/build/deps.rs
rewatch/src/build/logs.rs
rewatch/src/build/parse.rs
rewatch/src/cli.rs
rewatch/src/config.rs
rewatch/src/lib.rs
rewatch/src/main.rs
rewatch/src/sourcedirs.rs
rewatch/src/watcher.rs
scripts/test_syntax.sh
tests/syntax_tests/data/parsing/other/stringLiterals.res
yarn.lock
```

## Deleted Files

```text
cli/bsc.js
tests/build_tests/duplicated_symlinked_packages/a/node_modules/c
tests/build_tests/duplicated_symlinked_packages/b/node_modules/c
tests/build_tests/duplicated_symlinked_packages/node_modules/a
tests/build_tests/duplicated_symlinked_packages/node_modules/b
tests/tests/src/tagged_template_lib.js
```

## Type-Changed Files

```text
CLAUDE.md
```

`CLAUDE.md` changed from a symlink to a regular file.

## Largest Added Files

```text
1994861 playground/public/stdlib.json
1300604 projects/js-output-parity/RALPH_TODO.md
1291849 compiler-rust/src/types/typecore.rs
1119919 tests/tests/src/ticker.js
1079820 compiler-rust/src/types/typemod.rs
 693703 compiler-rust/src/binary_ast/ppx.rs
 558969 compiler-rust/src/driver.rs
 539772 compiler-rust/src/raw_lambda/convert.rs
 446130 compiler-rust/src/types/ctype.rs
 387751 compiler-rust/src/parser/printer.rs
 366653 compiler-rust/src/raw_lambda/matching.rs
 360595 compiler-rust/src/lambda/lam_compile_tests.rs
 329085 compiler-rust/src/lambda/lam_compile.rs
 322527 compiler-rust/src/parser/expr.rs
 320646 compiler-rust/src/js_ir/printer.rs
```

## High-Risk Added File Groups

- `compiler-rust/`: new Rust compiler crate, including typechecker, parser,
  Lambda, JS output, GenType, CMI, and CLI entry points.
- `rewatch/src/telemetry.rs`: new optional OpenTelemetry setup.
- `scripts/`: 27 new parity, benchmark, and triage scripts.
- `tests/tests/src/*.ocaml.mjs`: 657 generated OCaml-output snapshots.
- `tests/tests/src/*.js`: 49 generated or expected JS files.
- `tests/error_output_parity/`: 850 added error-output parity fixture paths.
- `tests/parity_baselines/`: 4 added baseline files.
- `lib/bs/`: generated build metadata.
- `.performance-cache/typechecker/`: generated local performance results.
- `compiler-rust/fix_*.py` plus root `fix_boxing.py`: one-off migration scripts.
- `compiler-rust/compiler-rust` and `packages/packages`: absolute symlinks.
