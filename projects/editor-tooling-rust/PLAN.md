# Editor tooling in Rust, inside the watcher

## Goal

Port all editor tooling to Rust and run it inside `rescript watch`:

- `analysis/src` (`rescript-editor-analysis`, ~17k lines of OCaml)
- `analysis/reanalyze` (dead code, exceptions, termination; ~9.5k lines)
- `tools/src` (`rescript-tools`: doc, migrate, ...; ~2k lines)

Builds serialize no `.cmi`/`.cmt`/`.cmti` files. Tooling must not read
compiler assets from disk; it works on the Rust parse and typed trees.

## Architecture

- `rescript watch` keeps the published interfaces in memory (the module
  registry). It serves tooling on a local port announced in
  `lib/rescript-watch.addr` (`rewatch/src/tooling_server.rs`).
- `rescript analysis <command> <args...>` is the client. It forwards
  `RUN {"cwd", "args"}`, prints the reply, and exits with 69 when no
  watcher runs.
- The watch loop answers requests (`rewatch/src/build/tooling.rs`). A
  command that needs types type-checks the module it is about on demand,
  from its current source, against the registry
  (`driver::typecheck_structure_for_tooling`). Implementations are not kept
  in memory; they are fast to recompile.
- The analysis itself lives in `compiler-rust/src/analysis` and mirrors
  `analysis/src` file by file (`document_symbol.ml` ->
  `document_symbol.rs`, ...). `analysis::run` dispatches like
  `analysis/bin/main.ml`.

## Design rules

- **Port, don't reinvent.** Follow the OCaml code's logic and output
  exactly. The test expectations in `tests/analysis_tests` and
  `tests/tools_tests` are OCaml's output and must not be edited to fit.
- **Traversal order.** OCaml `Hashtbl` iteration drives result order in
  many places; use `analysis::hashtbl::Hashtbl` (an exact port of
  `Hashtbl`/`Hashtbl.hash`) wherever the OCaml code uses a `Hashtbl` whose
  order is observable.
- **JSON.** Print with `analysis::json::Json::pretty` (an exact port of
  `Yojson.Safe.pretty_to_string` on the OCaml-compatible `Format`
  engine). `Cli.print_string` is `print_endline`.
- **Text.** Source text is held as Latin-1 characters standing for bytes;
  `analysis::Output::into_bytes` turns output back into bytes.
- **Types.** OCaml stores `Types.type_expr`; Rust has `TypeExprRef` into a
  module's own `TypeContext`, which is not `Send`. A command runs on one
  thread that owns every module type-checked for it, keeping their
  `TypeContext`s alive for the command.
- **Partial type information.** OCaml saves a partial `.cmt` when type
  checking fails (`Cmt_format.Partial_implementation` from the saved
  types). The Rust equivalent is in memory: type checking records the same
  saved parts and the tooling uses them when the module has errors.

## Status

| Area | OCaml | Rust | State |
|------|-------|------|-------|
| Client + server protocol | - | `rescript analysis`, `tooling_server.rs` | done |
| JSON printer | yojson `safe.ml` | `analysis/json.rs` | done |
| `Hashtbl` order | stdlib | `analysis/hashtbl.rs` | done |
| `test` harness | `cli.ml` `test` | `analysis/mod.rs` | `doc` only |
| documentSymbol | `document_symbol.ml` | `analysis/document_symbol.rs` | done |
| Data model | `shared_types.ml` | - | next |
| Module items from typed tree | `process_cmt.ml` | - | next |
| Positions/references | `process_extra.ml` | - | |
| Type printing | `Printtyp` via `shared.ml` | - | |
| hover, definition, typeDefinition, references, rename | | - | |
| completion (+ partial typing) | `completion_*.ml` | - | |
| signatureHelp, inlayHint, codeLens, semanticTokens, codeActions, createInterface, format, diagnosticSyntax | | - | |
| reanalyze | `analysis/reanalyze` | - | |
| rescript-tools | `tools/src` | - | |

## Verifying

```bash
cargo build --release --manifest-path rewatch/Cargo.toml
cd tests/analysis_tests/tests
RESCRIPT_RUNTIME=$(realpath ../../../packages/@rescript/runtime) \
  ../../../rewatch/target/release/rescript watch &
../../../rewatch/target/release/rescript analysis test src/DocumentSymbol.res \
  | diff src/expected/DocumentSymbol.res.txt -
```

The test projects' Makefiles run their `test.sh` under a watcher
(`tests/analysis_tests/with-watcher.sh`); `test.sh` still calls the OCaml
binary and moves to `rescript analysis` as commands are ported.
