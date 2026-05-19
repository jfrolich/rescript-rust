# Rust GenType TODO

Work one phase at a time. Commit after each meaningful change. Every semantic
commit must cite the OCaml/ReScript reference location it ports.

## Rewrite Stages

- [x] Stage 1: port leaf utilities and shared data file-for-file.
- [x] Stage 2: port config, paths, imports, generated-file effects, dependency
  helpers, runtime names, and export-module tables file-for-file.
- [x] Stage 3: port annotation, resolver, type environment, and translation
  modules file-for-file.
- [x] Stage 4: port emitters and `GenTypeMain.ml` file-for-file.
- [x] Run the three per-file review passes for the ported files: surface/naming,
  control/data flow, and output-sensitive semantics.

## Integration Phases

- [x] Phase 0: wire `compiler-rust/src/gentype/mod.rs` and make debug compiler
  and rewatch builds pass.
- [x] Phase 1: provide one no-argument output parity harness:
  `./scripts/test_gentype_output_parity.sh`.
- [x] Phase 1: always run the react fixture, stdlib-no-shims, and
  `/Users/jake/dev/tella-fusion`; fail clearly when Tella is missing.
- [x] Phase 1: compare raw `.gen.ts`/`.gen.tsx` files without normalization and
  report counts, changed/missing/extra files, diff hunks, and TypeScript status.
- [x] Phase 1/3: preserve stale CMT error parity through the existing
  stale-artifact diagnostics path.
- [x] Phase 2: carry parsed GenType config through Rust `bsc` and rewatch
  in-process compiler options.
- [x] Phase 2: parse the `-bs-gentype-*` flags emitted by rewatch.
- [x] Phase 3: add `gentype::main::process_typed_artifact`.
- [x] Phase 3: keep compiler module names separate from GenType output-prefix
  file names, matching `compiler/core/js_implementation.ml:72`,
  `compiler/core/js_implementation.ml:170`,
  `compiler/gentype/GenTypeMain.ml:141`, and
  `compiler/gentype/Paths.ml:61-86`.
- [x] Phase 3: invoke Rust GenType from rewatch in-process typed interfaces,
  no-interface implementations, and `.resi + @@genType.ignoreInterface`
  implementations.
- [x] Phase 3: invoke Rust GenType from standalone Rust `bsc -bs-gentype` for
  current-source typed artifacts.
- [x] Phase 4: wire annotation/name/import/resolver behavior for
  `@genType`, `@gentype`, `@genType.as`, `@genType.import`,
  `@genType.opaque`, and `@@genType.ignoreInterface`.
- [x] Phase 4: match React/ReasonReact exclusions from
  `compiler/gentype/GenTypeMain.ml:160-163`.
- [x] Phase 5: integrate typedtree/type-expression translation through
  `TypeContext`, matching direct `Types.type_expr.desc` reads in
  `compiler/ml/types.ml:22`,
  `compiler/gentype/TranslateTypeExprFromTypes.ml:5-12`,
  `compiler/gentype/TranslateTypeExprFromTypes.ml:470-742`, and
  `compiler/gentype/TypeVars.ml:3-16`.
- [x] Phase 5: match `TranslateTypeDeclarations.ml:51` `String.escaped`
  behavior for `@as` record field names.
- [x] Phase 5: reach stdlib-no-shims output parity: `1/1`.
- [x] Phase 6: integrate structure/signature translation, declaration
  filtering, `.resi` selection, and `@@genType.ignoreInterface` behavior.
- [x] Phase 7: integrate code items, translation data, runtime imports,
  emitters, converters, and named arguments.
- [x] Phase 7: reach react fixture output parity: `71/71`.
- [x] Phase 8: finish package-local source-dir lookup, dependency lookup, shim
  resolution, namespace/suffix handling, and import path behavior required by
  the in-repo suites and Tella.
- [x] Phase 9: run the no-argument Tella GenType parity gate and reach zero
  generated-output diffs: `110/110`.
- [x] Phase 10: avoid rereading typed artifacts when the current in-memory
  typedtree is available.
- [x] Phase 10: add a `gentype` timing bucket to the optional compiler phase
  and module timing reports.
- [x] Phase 10: keep JavaScript output, typedtree, lambda, and error-output
  parity at their current green baselines.

## Current Verification

```text
cargo build --quiet --manifest-path compiler-rust/Cargo.toml --bin bsc
cargo build --quiet --manifest-path rewatch/Cargo.toml
make test-gentype
./scripts/test_gentype_output_parity.sh
./scripts/test_typedtree_parity.sh --quick
./scripts/test_lambda_parity.sh --quick
./scripts/test_js_output_parity.sh --quick
./scripts/test_error_output_parity.sh
```

Latest recorded results:

```text
GenType output parity: react 71/71, stdlib-no-shims 1/1, Tella 110/110
typedtree quick:       662/662
lambda quick:          662/662
JS output quick:       fixture parity 344/344, snapshots 662/662
error output parity:   1202/1202
```

The direct `Cmt_format.read_cmt` typedtree decoder remains intentionally
unimplemented outside stale-artifact diagnostics. The supported Rust generation
path uses the current in-memory typed artifact, which is the path required by
the plan unless direct CMT reading becomes necessary for a new CLI parity case.
