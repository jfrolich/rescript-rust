# Rust GenType TODO

Work one phase at a time. Commit after each meaningful change. Every semantic
commit must cite the OCaml/ReScript reference location it ports.

## Phase 0: Harness

- [ ] Add `scripts/test_gentype_output_parity.sh`.
- [ ] Compare raw `.gen.tsx` and `.gen.ts` files without normalization.
- [ ] Support `tests/gentype_tests/typescript-react-example`.
- [ ] Support `tests/gentype_tests/stdlib-no-shims`.
- [ ] Support `/Users/jake/dev/tella-fusion` when present.
- [ ] Report generated file counts, missing files, extra files, changed files,
  diff hunk count, and TypeScript typecheck status.
- [ ] Preserve current stale CMT error parity coverage.
- [ ] Commit the harness with the current baseline in the commit body.

## Phase 1: CLI and Config

- [ ] Replace boolean-only `Options::gentype` in `compiler-rust/src/bin/bsc.rs`.
- [ ] Port `GenTypeConfig.t` from `compiler/gentype/GenTypeConfig.ml`.
- [ ] Parse all `-bs-gentype-*` flags emitted by rewatch.
- [ ] Add unit tests for config combinations used by in-repo suites and Tella.
- [ ] Commit with in-repo and Tella config baseline.

## Phase 2: Input Boundary

- [ ] Add `compiler-rust/src/gentype/mod.rs`.
- [ ] Add `gentype::main::process_typed_artifact`.
- [ ] Add `GentypeInput` carrying module name, source file, output paths,
  annotation source, typedtree payload, and type-error state.
- [ ] Port `Paths.ml`, `ModuleName.ml`, and `GeneratedFiles.ml` behavior needed
  by the entry point.
- [ ] Preserve stale CMT error behavior from `GenTypeMain.ml:85-91`.
- [ ] Commit once no-annotation stale output behavior matches OCaml.

## Phase 3: Annotations and Resolver Skeleton

- [ ] Port `Annotation.ml`.
- [ ] Port `ResolvedName.ml` and `ImportPath.ml`.
- [ ] Add `ModuleResolver` skeleton for source dirs, extensions, shims, and
  dependency paths.
- [ ] Match `@genType`, `@gentype`, `@genType.as`, `@genType.import`,
  `@genType.opaque`, and `@@genType.ignoreInterface`.
- [ ] Match React/ReasonReact exclusion from `GenTypeMain.ml:160-163`.
- [ ] Commit once generated file set detection matches OCaml.

## Phase 4: Type Translation

- [ ] Port `TypeEnv.ml`.
- [ ] Port `TypeVars.ml`.
- [ ] Port `TranslateCoreType.ml`.
- [ ] Port `TranslateTypeExprFromTypes.ml`.
- [ ] Port `TranslateTypeDeclarations.ml`.
- [ ] Reach `stdlib-no-shims` output parity.
- [ ] Commit each type-family improvement atomically with parity status.

## Phase 5: Structure and Signature Translation

- [ ] Port `TranslateStructure.ml`.
- [ ] Port `TranslateSignature.ml`.
- [ ] Port `TranslateSignatureFromTypes.ml`.
- [ ] Match declaration filtering from `GenTypeMain.ml:16-24`.
- [ ] Match `.resi` plus `ignoreInterface` flow from `GenTypeMain.ml:93-134`.
- [ ] Reach parity for interface-driven fixtures.
- [ ] Commit each fixture cluster atomically with parity status.

## Phase 6: Emission

- [ ] Port `CodeItem.ml`.
- [ ] Port `Translation.ml`.
- [ ] Port `Runtime.ml`.
- [ ] Port `EmitText.ml`.
- [ ] Port `EmitType.ml`.
- [ ] Port `EmitJs.ml`.
- [ ] Port `Emitters.ml`.
- [ ] Port `Converter.ml`.
- [ ] Port `NamedArgs.ml`.
- [ ] Reach zero diffs in `typescript-react-example`.
- [ ] Commit each emitter cluster atomically with parity status.

## Phase 7: Cross-File Resolution

- [ ] Finish source-dir lookup.
- [ ] Finish dependency-path lookup.
- [ ] Finish shim resolution.
- [ ] Finish namespace and suffix handling.
- [ ] Finish `node`, `node16`, and `bundler` module-resolution modes.
- [ ] Reach transitive type/import fixture parity.
- [ ] Commit each resolver improvement atomically with parity status.

## Phase 8: Tella

- [ ] Run the Tella GenType parity gate from the Tella repo root.
- [ ] Fix missing generated files.
- [ ] Fix import-path diffs.
- [ ] Fix type conversion diffs.
- [ ] Fix React/component diffs.
- [ ] Fix stale output behavior if Tella exposes it.
- [ ] Reach zero Tella generated-output diffs.
- [ ] Commit each Tella cluster atomically with Tella parity status.

## Phase 9: Regression and Performance

- [ ] Re-run JavaScript output parity.
- [ ] Re-run typedtree parity.
- [ ] Re-run lambda parity.
- [ ] Re-run error parity focused on GenType stale CMT cases.
- [ ] Add GenType timing measurements for Tella.
- [ ] Avoid rereading typed artifacts when in-memory typedtree is available.
- [ ] Commit cleanup and performance improvements separately from parity fixes.
