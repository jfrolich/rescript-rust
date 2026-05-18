# Rust GenType TODO

Work one phase at a time. Commit after each meaningful change. Every semantic
commit must cite the OCaml/ReScript reference location it ports.

## Rewrite Stage 1: Leaf Utilities and Shared Data

These ports do not need to compile yet. Keep function names and file structure
as close to the reference as Rust allows.

- [ ] Port `GenTypeCommon.ml`.
- [ ] Port `Debug.ml`.
- [ ] Port `Log_.ml`.
- [ ] Port `Indent.ml`.
- [ ] Port `GenIdent.ml`.
- [ ] Port `ModuleName.ml` and `ModuleName.mli`.
- [ ] Port `ResolvedName.ml` and `ResolvedName.mli`.
- [ ] Port `TypeVars.ml`.
- [ ] Port `CodeItem.ml`.
- [ ] Port `Translation.ml`.
- [ ] Run the three per-file review passes for every file in this stage.
- [ ] Commit the stage or commit coherent file clusters.

## Rewrite Stage 2: Config, Paths, Imports, and File Effects

These ports do not need to compile yet. Do not introduce integration
abstractions that are not present in the reference.

- [ ] Port `GenTypeConfig.ml`.
- [ ] Port `Paths.ml`.
- [ ] Port `FindSourceFile.ml` and `FindSourceFile.mli`.
- [ ] Port `GeneratedFiles.ml`.
- [ ] Port `ImportPath.ml` and `ImportPath.mli`.
- [ ] Port `ModuleExtension.ml`.
- [ ] Port `Dependencies.ml`.
- [ ] Port `Runtime.ml` and `Runtime.mli`.
- [ ] Port `ExportModule.ml`.
- [ ] Run the three per-file review passes for every file in this stage.
- [ ] Commit the stage or commit coherent file clusters.

## Rewrite Stage 3: Annotation, Resolver, Type Environment, and Translation

These ports do not need to compile yet. Preserve traversal and mutation order
from the reference.

- [ ] Port `Annotation.ml`.
- [ ] Port `ModuleResolver.ml`.
- [ ] Port `TypeEnv.ml` and `TypeEnv.mli`.
- [ ] Port `TranslateCoreType.ml`.
- [ ] Port `TranslateTypeExprFromTypes.ml`.
- [ ] Port `TranslateTypeDeclarations.ml`.
- [ ] Port `TranslateSignatureFromTypes.ml`.
- [ ] Port `TranslateSignature.ml`.
- [ ] Port `TranslateStructure.ml`.
- [ ] Run the three per-file review passes for every file in this stage.
- [ ] Commit the stage or commit coherent file clusters.

## Rewrite Stage 4: Emitters and Entry Point

These ports do not need to compile yet. After this stage the Rust GenType tree
should exist file for file.

- [ ] Port `EmitText.ml`.
- [ ] Port `EmitType.ml`.
- [ ] Port `Emitters.ml` and `Emitters.mli`.
- [ ] Port `EmitJs.ml`.
- [ ] Port `Converter.ml`.
- [ ] Port `NamedArgs.ml`.
- [ ] Port `GenTypeMain.ml`.
- [ ] Run the three per-file review passes for every file in this stage.
- [ ] Commit the stage or commit coherent file clusters.

## Per-File Review Checklist

Run this checklist for each file after its first port and before compile work.

- [ ] Surface review: function names, helper names, type/field names, order,
  module boundary, and reference-location comments match.
- [ ] Control-flow review: match arm order, early returns, error paths,
  fold/map/filter direction, recursion shape, mutation order, lazy resolver
  calls, generated-file actions, and warning/log behavior match.
- [ ] Output-sensitive review: string fragments, whitespace/newlines,
  import/export ordering, helper ordering, file naming, shim/dependency/module
  resolution, and annotation interpretation match.
- [ ] Patch any differences found by review before marking the file ready for
  compilation work.

## Phase 0: Make the Port Compile

- [ ] Wire `compiler-rust/src/gentype/mod.rs`.
- [ ] Replace cross-file placeholders with the Rust types determined by the
  reviewed ports.
- [ ] Fix ownership and borrow errors without changing reference control flow.
- [ ] Keep module and function names stable.
- [ ] Build with `cargo build --manifest-path compiler-rust/Cargo.toml`.
- [ ] Commit compile-fix clusters separately from semantic parity changes.

## Phase 1: Harness

- [ ] Add `scripts/test_gentype_output_parity.sh`.
- [ ] Compare raw `.gen.tsx` and `.gen.ts` files without normalization.
- [ ] Support `tests/gentype_tests/typescript-react-example`.
- [ ] Support `tests/gentype_tests/stdlib-no-shims`.
- [ ] Support `/Users/jake/dev/tella-fusion` when present.
- [ ] Report generated file counts, missing files, extra files, changed files,
  diff hunk count, and TypeScript typecheck status.
- [ ] Preserve current stale CMT error parity coverage.
- [ ] Commit the harness with the current baseline in the commit body.

## Phase 2: CLI and Config

- [ ] Replace boolean-only `Options::gentype` in `compiler-rust/src/bin/bsc.rs`.
- [ ] Wire the reviewed `config.rs` port of `GenTypeConfig.t`.
- [ ] Parse all `-bs-gentype-*` flags emitted by rewatch.
- [ ] Add unit tests for config combinations used by in-repo suites and Tella.
- [ ] Commit with in-repo and Tella config baseline.

## Phase 3: Input Boundary

- [ ] Add `compiler-rust/src/gentype/mod.rs`.
- [ ] Add `gentype::main::process_typed_artifact`.
- [ ] Add `GentypeInput` carrying module name, source file, output paths,
  annotation source, typedtree payload, and type-error state.
- [ ] Wire reviewed `paths.rs`, `module_name.rs`, and `generated_files.rs`
  behavior into the entry point.
- [ ] Preserve stale CMT error behavior from `GenTypeMain.ml:85-91`.
- [ ] Commit once no-annotation stale output behavior matches OCaml.

## Phase 4: Annotations and Resolver Skeleton

- [ ] Wire reviewed `annotation.rs`.
- [ ] Wire reviewed `resolved_name.rs` and `import_path.rs`.
- [ ] Wire reviewed `module_resolver.rs` for source dirs, extensions, shims,
  and dependency paths.
- [ ] Match `@genType`, `@gentype`, `@genType.as`, `@genType.import`,
  `@genType.opaque`, and `@@genType.ignoreInterface`.
- [ ] Match React/ReasonReact exclusion from `GenTypeMain.ml:160-163`.
- [ ] Commit once generated file set detection matches OCaml.

## Phase 5: Type Translation

- [ ] Integrate reviewed `type_env.rs`.
- [ ] Integrate reviewed `type_vars.rs`.
- [ ] Integrate reviewed `translate_core_type.rs`.
- [ ] Integrate reviewed `translate_type_expr_from_types.rs`.
- [ ] Integrate reviewed `translate_type_declarations.rs`.
- [ ] Reach `stdlib-no-shims` output parity.
- [ ] Commit each type-family improvement atomically with parity status.

## Phase 6: Structure and Signature Translation

- [ ] Integrate reviewed `translate_structure.rs`.
- [ ] Integrate reviewed `translate_signature.rs`.
- [ ] Integrate reviewed `translate_signature_from_types.rs`.
- [ ] Match declaration filtering from `GenTypeMain.ml:16-24`.
- [ ] Match `.resi` plus `ignoreInterface` flow from `GenTypeMain.ml:93-134`.
- [ ] Reach parity for interface-driven fixtures.
- [ ] Commit each fixture cluster atomically with parity status.

## Phase 7: Emission

- [ ] Integrate reviewed `code_item.rs`.
- [ ] Integrate reviewed `translation.rs`.
- [ ] Integrate reviewed `runtime.rs`.
- [ ] Integrate reviewed `emit_text.rs`.
- [ ] Integrate reviewed `emit_type.rs`.
- [ ] Integrate reviewed `emit_js.rs`.
- [ ] Integrate reviewed `emitters.rs`.
- [ ] Integrate reviewed `converter.rs`.
- [ ] Integrate reviewed `named_args.rs`.
- [ ] Reach zero diffs in `typescript-react-example`.
- [ ] Commit each emitter cluster atomically with parity status.

## Phase 8: Cross-File Resolution

- [ ] Finish source-dir lookup.
- [ ] Finish dependency-path lookup.
- [ ] Finish shim resolution.
- [ ] Finish namespace and suffix handling.
- [ ] Finish `node`, `node16`, and `bundler` module-resolution modes.
- [ ] Reach transitive type/import fixture parity.
- [ ] Commit each resolver improvement atomically with parity status.

## Phase 9: Tella

- [ ] Run the Tella GenType parity gate from the Tella repo root.
- [ ] Fix missing generated files.
- [ ] Fix import-path diffs.
- [ ] Fix type conversion diffs.
- [ ] Fix React/component diffs.
- [ ] Fix stale output behavior if Tella exposes it.
- [ ] Reach zero Tella generated-output diffs.
- [ ] Commit each Tella cluster atomically with Tella parity status.

## Phase 10: Regression and Performance

- [ ] Re-run JavaScript output parity.
- [ ] Re-run typedtree parity.
- [ ] Re-run lambda parity.
- [ ] Re-run error parity focused on GenType stale CMT cases.
- [ ] Add GenType timing measurements for Tella.
- [ ] Avoid rereading typed artifacts when in-memory typedtree is available.
- [ ] Commit cleanup and performance improvements separately from parity fixes.
