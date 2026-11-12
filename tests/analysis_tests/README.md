# Analysis tests

Each test project holds ReScript files with `//^xxx` directives under the
position they test, and in `src/expected` (and `not_compiled/expected`) what
`rescript-editor-analysis test <file>` prints for them: one block per
directive, headed by a line such as `Hover src/Hover.res 26:6`. The snapshots
are the OCaml analysis's output and the reference for both analyses.

| Directive | Command | Rust analysis |
| --- | --- | --- |
| `def` | definition | yes |
| `typ` | type definition | yes |
| `hov` | hover | yes, except hovers OCaml answers through completion |
| `ref` | references | yes |
| `pre` | prepare rename | yes |
| `ren` | rename | yes |
| `doc` | document symbols | yes |
| `com`, `cre` | completion, completion resolve | no |
| `she` | signature help | no |
| `xfm`, `c-a` | code actions, codemods | no |
| `hin`, `cle`, `hig`, `sem` | inlay hints, code lens, highlighting, semantic tokens | no |
| `int` | create interface | no |
| `ast`, `dia`, `dce` | AST dump, syntax diagnostics, dead code | no |
| `db±`, `dv±`, `in±` | logging and incremental type checking flags | ignored |

## The OCaml analysis

`make test-analysis` (from the repository root) builds each project and
regenerates its snapshots with `rescript-editor-analysis`, failing when they
change. That binary reads `.cmt` files; in-process Rust builds write none, so
it fails on them. To regenerate the snapshots, build with the OCaml compiler
first, the runtime and the dependencies before the projects:

```sh
rescript=$PWD/packages/@rescript/<platform>/bin/rescript.exe
bsc=$PWD/_build/install/default/bin/bsc
export RESCRIPT_RUNTIME=$PWD/packages/@rescript/runtime
for dir in packages/@rescript/runtime packages/@rescript/belt \
  tests/dependencies/rescript-react; do
  "$rescript" build-reference --bsc "$bsc" "$dir"
done
cd tests/analysis_tests/tests   # or another project
"$rescript" build-reference --bsc "$bsc" . && bash ./test.sh
```

## The Rust analysis

The Rust port (`compiler-rust/src/analysis`) runs inside `rescript watch`,
on the watcher's typed trees. `rescript analysis <command> <args...>` takes
the arguments `rescript-editor-analysis` takes, sends them to the watcher
serving the project (found through `lib/rescript-watch.addr`), and prints
its answer. Without a watcher it exits with 69 (`no-watcher.sh` checks this).

```sh
make test-analysis-rust                         # from the repository root
tests/analysis_tests/test-rust.sh [project...]  # after `make lib`
```

`test-rust.sh` starts `rescript watch` in each project (`with-watcher.sh`),
runs `rescript analysis test <file>` for every source file with directives,
splits its output and the snapshot into the directives' blocks, and compares
them block by block. It prints each difference, then a table per directive:

- `match` and `differ`: blocks compared with the snapshot;
- `unsupported`: directives the Rust analysis answers with
  `` `xxx` is not available inside the watcher yet ``, and hovers
  (`hov(completion)`) that OCaml answers through its completion engine where
  Rust answers null;
- `error`: the file's command failed; `missing`: no block for a directive;
  `no-snapshot`: a block the snapshot lacks;
- `control`: flag directives, which print nothing.

It exits 1 when a block differs or a file fails. With
`RUST_ANALYSIS_DUMP=<dir>` it also writes each file's Rust output to
`<dir>/<project>/<file>.txt`.

`tests-reanalyze` runs `rescript-editor-analysis reanalyze`, which the Rust
analysis does not provide, so `test-rust.sh` does not cover it.
