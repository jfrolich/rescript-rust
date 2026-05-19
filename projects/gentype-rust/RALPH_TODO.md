# Rust GenType TODO

Work one phase at a time. Commit after each meaningful change. Every semantic
commit must cite the OCaml/ReScript reference location it ports.

## Rewrite Stage 1: Leaf Utilities and Shared Data

These ports do not need to compile yet. Keep function names and file structure
as close to the reference as Rust allows.

- [x] Port `GenTypeCommon.ml`.
- [x] Port `Debug.ml`.
- [x] Port `Log_.ml`.
- [x] Port `Indent.ml`.
- [x] Port `GenIdent.ml`.
- [x] Port `ModuleName.ml` and `ModuleName.mli`.
- [x] Port `ResolvedName.ml` and `ResolvedName.mli`.
- [x] Port `TypeVars.ml`.
- [x] Port `CodeItem.ml`.
- [x] Port `Translation.ml`.
- [x] Run the three per-file review passes for every file in this stage.
- [x] Commit the stage or commit coherent file clusters.

## Rewrite Stage 2: Config, Paths, Imports, and File Effects

These ports do not need to compile yet. Do not introduce integration
abstractions that are not present in the reference.

- [x] Port `GenTypeConfig.ml`.
- [x] Port `Paths.ml`.
- [x] Port `FindSourceFile.ml` and `FindSourceFile.mli`.
- [x] Port `GeneratedFiles.ml`.
- [x] Port `ImportPath.ml` and `ImportPath.mli`.
- [x] Port `ModuleExtension.ml`.
- [x] Port `Dependencies.ml`.
- [x] Port `Runtime.ml` and `Runtime.mli`.
- [x] Port `ExportModule.ml`.
- [x] Run the three per-file review passes for every file in this stage.
- [x] Commit the stage or commit coherent file clusters.

## Rewrite Stage 3: Annotation, Resolver, Type Environment, and Translation

These ports do not need to compile yet. Preserve traversal and mutation order
from the reference.

- [x] Port `Annotation.ml`.
- [x] Port `ModuleResolver.ml`.
- [x] Port `TypeEnv.ml` and `TypeEnv.mli`.
- [x] Port `TranslateCoreType.ml`.
- [x] Port `TranslateTypeExprFromTypes.ml`.
- [x] Port `TranslateTypeDeclarations.ml`.
- [x] Port `TranslateSignatureFromTypes.ml`.
- [x] Port `TranslateSignature.ml`.
- [x] Port `TranslateStructure.ml`.
- [x] Run the three per-file review passes for every file in this stage.
- [x] Run the three per-file review passes for `Annotation.ml`,
  `ModuleResolver.ml`, `TranslateCoreType.ml`,
  `TranslateTypeDeclarations.ml`,
  `TranslateTypeExprFromTypes.ml`, and
  `TypeEnv.ml`/`.mli`.
- [x] Commit the stage or commit coherent file clusters.

## Rewrite Stage 4: Emitters and Entry Point

These ports do not need to compile yet. After this stage the Rust GenType tree
should exist file for file.

- [x] Port `EmitText.ml`.
- [x] Port `EmitType.ml`.
- [x] Port `Emitters.ml` and `Emitters.mli`.
- [x] Port `EmitJs.ml`.
- [x] Port `Converter.ml`.
- [x] Port `NamedArgs.ml`.
- [x] Port `GenTypeMain.ml`.
- [x] Run the three per-file review passes for every file in this stage.
  `EmitText.ml`, `EmitType.ml`, `Emitters.ml`/`.mli`, `EmitJs.ml`,
  `NamedArgs.ml`, `Converter.ml`, and `GenTypeMain.ml` have passed.
- [x] Commit the stage or commit coherent file clusters.

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

- [x] Wire `compiler-rust/src/gentype/mod.rs`.
- [ ] Replace cross-file placeholders with the Rust types determined by the
  reviewed ports.
- [x] Fix ownership and borrow errors without changing reference control flow.
- [x] Keep module and function names stable.
- [x] Build with `cargo build --manifest-path compiler-rust/Cargo.toml`.
- [x] Commit compile-fix clusters separately from semantic parity changes.

## Phase 1: Harness

- [x] Add `scripts/test_gentype_output_parity.sh`.
- [x] Make it a no-argument script.
- [x] Compare raw `.gen.tsx` and `.gen.ts` files without normalization.
- [x] Always run `tests/gentype_tests/typescript-react-example`.
- [x] Always run `tests/gentype_tests/stdlib-no-shims`.
- [x] Always run `/Users/jake/dev/tella-fusion`.
- [x] Fail clearly if Tella is missing instead of silently skipping it.
- [x] Report generated file counts, missing files, extra files, changed files,
  diff hunk count, and TypeScript typecheck status.
- [ ] Preserve current stale CMT error parity coverage.
- [x] Commit the harness with the current baseline in the commit body.

## Phase 2: CLI and Config

- [x] Keep `Options::gentype` as the enable flag and carry the parsed
  `GenTypeConfig.t` equivalent through `CompilerOptions`.
- [x] Wire the reviewed `config.rs` port of `GenTypeConfig.t`.
- [x] Parse all `-bs-gentype-*` flags emitted by rewatch.
- [x] Add unit tests for config combinations used by in-repo suites and Tella.
- [x] Commit with in-repo and Tella config baseline.

## Phase 3: Input Boundary

- [x] Add `compiler-rust/src/gentype/mod.rs`.
- [x] Add `gentype::main::process_typed_artifact`.
- [x] Add `TypedArtifact` carrying module name, source file, annotation source,
  typedtree payload, and type-error state.
- [x] Wire reviewed `paths.rs`, `module_name.rs`, and `generated_files.rs`
  behavior into the in-process typed-artifact entry point.
- [x] Invoke Rust GenType from rewatch in-process typed interfaces and
  no-interface implementations, matching
  `compiler/core/js_implementation.ml:33-34` / `170` and
  `compiler/gentype/Paths.ml:61-86`.
- [ ] Preserve stale CMT error behavior from `GenTypeMain.ml:85-91`.
- [x] Commit the typed-artifact boundary before wiring compiler call sites.
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
- [x] Strip only the current compilation-unit prefix before dependency/type
  translation, matching CMT-shaped OCaml GenType input from
  `compiler/gentype/GenTypeMain.ml:53-70` and `compiler/gentype/Paths.ml:61-86`
  as it reaches `compiler/gentype/Dependencies.ml:15-38` and
  `compiler/gentype/TranslateTypeExprFromTypes.ml:78-439`.
- [x] Thread `TypeContext` through `type_vars.rs` so
  `extract_from_type_expr_refs` reads actual `Tvar` names like
  `compiler/gentype/TypeVars.ml:3-16`.
- [x] Thread `TypeContext` through `translate_core_type.rs`,
  `translate_type_expr_from_types.rs`, `translate_type_declarations.rs`,
  `translate_signature_from_types.rs`, `translate_signature.rs`,
  `translate_structure.rs`, and `translation.rs` wherever the OCaml reference
  reads `Types.type_expr.desc` directly, especially
  `compiler/gentype/TranslateTypeExprFromTypes.ml:5-12` and
  `compiler/gentype/TranslateTypeExprFromTypes.ml:470-742`.
- [ ] Mirror `TranslateTypeExprFromTypes.ml:560-565` for the
  linked-argument `Tconstr` record-copy branch.
- [ ] Thread `ParseArena` for `TranslateTypeExprFromTypes.ml:639-670` package
  constraint longidents.
- [ ] Integrate reviewed `type_vars.rs` fully.
- [ ] Integrate reviewed `translate_core_type.rs` fully.
- [ ] Integrate reviewed `translate_type_expr_from_types.rs` fully.
- [ ] Integrate reviewed `translate_type_declarations.rs` fully.
- [x] Reach `stdlib-no-shims` output parity: 1/1 with 0 diff hunks.
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
- [x] Match `GenIdent.ml:16-23` anonymous type-variable lookup-then-insert
  mutation without keeping a stale Rust borrow.
- [ ] Integrate reviewed `runtime.rs`.
- [ ] Integrate reviewed `emit_text.rs`.
- [ ] Integrate reviewed `emit_type.rs`.
- [ ] Integrate reviewed `emit_js.rs`.
- [x] Match `EmitJs.ml:662-678` by leaving `inline_one_level` unchanged when
  export type lookup raises `Not_found`.
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
