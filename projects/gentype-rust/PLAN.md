# Rust GenType Implementation Plan

## Goal

Implement GenType inside the Rust compiler so `bsc -bs-gentype` produces the
same generated TypeScript files as the OCaml compiler.

Parity is measured by generated output, not by a normalized representation:

- `tests/gentype_tests/typescript-react-example`
- `tests/gentype_tests/stdlib-no-shims`
- the Tella repo, especially `packages/core/webapp`

Use one repo-local parity command for all of the above:

```sh
./scripts/test_gentype_output_parity.sh
```

The script takes no repo argument and always runs all three scopes. Keep it
that way so baseline reports are comparable across sessions.

The Rust implementation should port the existing GenType algorithm. Do not
shell out to the OCaml compiler, do not add output normalizers, and do not
create compatibility wrappers that hide differences. Keep function and module
names close to the reference implementation so future audits can compare Rust
against OCaml/ReScript source directly.

## Reference Implementation

Use these sources as the reference implementation for every semantic change:

- Entry point: `compiler/gentype/GenTypeMain.ml:136-175`
- Config model and CLI-backed flags: `compiler/gentype/GenTypeConfig.ml`
- Generated-file behavior: `compiler/gentype/GeneratedFiles.ml`
- Path and module resolution: `compiler/gentype/Paths.ml`,
  `compiler/gentype/ModuleResolver.ml`, `compiler/gentype/ImportPath.ml`
- Annotation scanning: `compiler/gentype/Annotation.ml`
- Translation: `compiler/gentype/TranslateStructure.ml`,
  `compiler/gentype/TranslateSignature.ml`,
  `compiler/gentype/TranslateTypeDeclarations.ml`,
  `compiler/gentype/TranslateCoreType.ml`,
  `compiler/gentype/TranslateTypeExprFromTypes.ml`
- Emission: `compiler/gentype/EmitJs.ml`, `compiler/gentype/EmitType.ml`,
  `compiler/gentype/EmitText.ml`, `compiler/gentype/Emitters.ml`
- Shared translation data: `compiler/gentype/Translation.ml`,
  `compiler/gentype/CodeItem.ml`, `compiler/gentype/TypeEnv.ml`,
  `compiler/gentype/TypeVars.ml`, `compiler/gentype/Runtime.ml`
- ReScript source copy used by syntax/idempotency tests:
  `tests/syntax_tests/data/idempotency/genType/src/*.res`

Every implementation commit should cite the exact reference file and line range
that the Rust change follows.

## Existing Rust Surface

Rust already has partial plumbing, but not the generator:

- `rewatch/src/config.rs:286-409` parses `gentypeconfig`.
- `rewatch/src/config.rs:820-899` emits `-bs-gentype-*` flags.
- `rewatch/src/build/compile.rs` passes those flags into `bsc`.
- `compiler-rust/src/driver.rs:13509-13540` accepts GenType flags at the
  driver layer.
- `compiler-rust/src/bin/bsc.rs:111` stores only a boolean `gentype`.
- `compiler-rust/src/bin/bsc.rs:642-690` currently only checks selected CMT
  files for stale-artifact error parity. It does not generate `.gen.tsx` or
  `.gen.ts`.
- `compiler-rust/src/binary_ast/ppx.rs:3763-3765` already rewrites
  `@genType.import` and `@gentype.import` externals.

The first implementation step is not wiring or compilation. First create a
non-compiling, file-for-file Rust port of the GenType sources, then review each
file against its reference until the shape is 1:1. Only after that should the
project start fixing compilation, integration, and parity output.

## Port-First Rule

Port the GenType implementation file by file before trying to make the crate
compile. For each reference `.ml`, `.mli`, `.res`, or `.resi` file, create the
corresponding Rust module with the same public function names, the same helper
function names where practical, the same data-flow shape, and the same
branch/order structure. The port should be idiomatic Rust in ownership and data
representation, but the algorithm must stay visibly traceable to the OCaml code.

During these stages it is acceptable, and expected, that `compiler-rust` does
not compile. Do not add temporary compatibility wrappers just to make an early
build pass. Do not skip functions because their types are inconvenient. Use
`todo!()` only as a typed placeholder for dependencies outside the file being
ported, not as a substitute for porting that file's own logic.

Each file must carry a header or nearby comments referencing the source file and
line ranges it ports. Commit file ports atomically enough that a reviewer can
compare one Rust file to its one reference file without unrelated changes.

## File-For-File Rewrite Stages

### Rewrite Stage 1: Leaf Utilities and Shared Data

Create direct Rust ports for the low-dependency modules first:

- `GenTypeCommon.ml`
- `Debug.ml`
- `Log_.ml`
- `Indent.ml`
- `GenIdent.ml`
- `ModuleName.ml` and `ModuleName.mli`
- `ResolvedName.ml` and `ResolvedName.mli`
- `TypeVars.ml`
- `CodeItem.ml`
- `Translation.ml`

The goal is a readable 1:1 Rust translation, not a compiling integration.

### Rewrite Stage 2: Config, Paths, Imports, and File Effects

Port the modules that define configuration, paths, resolver inputs, and
generated-file side effects:

- `GenTypeConfig.ml`
- `Paths.ml`
- `FindSourceFile.ml` and `FindSourceFile.mli`
- `GeneratedFiles.ml`
- `ImportPath.ml` and `ImportPath.mli`
- `ModuleExtension.ml`
- `Dependencies.ml`
- `Runtime.ml` and `Runtime.mli`
- `ExportModule.ml`

Keep the same function names and field names where practical. Any Rust-side
type introduced here should correspond to a reference type, not an invented
integration abstraction.

### Rewrite Stage 3: Annotation, Resolver, Type Environment, and Translation

Port the modules that inspect typedtree/type information and produce the
intermediate translation:

- `Annotation.ml`
- `ModuleResolver.ml`
- `TypeEnv.ml` and `TypeEnv.mli`
- `TranslateCoreType.ml`
- `TranslateTypeExprFromTypes.ml`
- `TranslateTypeDeclarations.ml`
- `TranslateSignatureFromTypes.ml`
- `TranslateSignature.ml`
- `TranslateStructure.ml`

Preserve traversal order, option/result handling, recursion shape, emitted
warnings, and type-environment mutation order. If Rust typedtree data is
missing, document the exact required field/accessor and keep the port shaped
like the reference.

### Rewrite Stage 4: Emitters and Entry Point

Port the output and top-level orchestration modules last:

- `EmitText.ml`
- `EmitType.ml`
- `Emitters.ml` and `Emitters.mli`
- `EmitJs.ml`
- `Converter.ml`
- `NamedArgs.ml`
- `GenTypeMain.ml`

The result after this stage should be a complete non-compiling Rust GenType
tree that mirrors the source implementation file for file.

## Per-File Review Stages

After each file is ported, run three review passes before considering the file
ready for compilation work. These reviews are still allowed to leave the crate
non-compiling.

### Review Stage 1: Surface and Naming Review

Compare the Rust file against the reference file and patch any differences in:

- function names and helper names
- type/variant/field names
- function order
- module boundaries
- public/private surface
- comments with source locations

The Rust file should look like an idiomatic Rust rendering of the same source,
not a redesigned API.

### Review Stage 2: Control-Flow and Data-Flow Review

Compare every function body and patch any differences in:

- match arm order
- early returns and exception/error paths
- fold/map/filter direction
- recursion shape
- mutable state and side-effect order
- lazy resolver calls and generated-file actions
- warning/log behavior

Do not simplify or combine branches unless the reference does so.

### Review Stage 3: Output-Sensitive Semantics Review

Compare output-facing details and patch any differences in:

- emitted string fragments
- whitespace and newline decisions
- import/export ordering
- generated helper ordering
- source-file and output-file naming
- shim/dependency/module-resolution decisions
- annotation payload interpretation

This stage is about eliminating semantic drift before Rust type errors start
driving the implementation.

## Architecture

Add a Rust module tree under `compiler-rust/src/gentype/` that mirrors the
reference modules:

- `annotation.rs`
- `code_item.rs`
- `config.rs`
- `converter.rs`
- `emit_js.rs`
- `emit_text.rs`
- `emit_type.rs`
- `emitters.rs`
- `generated_files.rs`
- `import_path.rs`
- `main.rs`
- `module_name.rs`
- `module_resolver.rs`
- `named_args.rs`
- `paths.rs`
- `resolved_name.rs`
- `runtime.rs`
- `translate_core_type.rs`
- `translate_signature.rs`
- `translate_signature_from_types.rs`
- `translate_structure.rs`
- `translate_type_declarations.rs`
- `translate_type_expr_from_types.rs`
- `translation.rs`
- `type_env.rs`
- `type_vars.rs`

The Rust data flow should match `GenTypeMain.process_cmt_file`:

1. Parse the full `-bs-gentype-*` CLI state into `gentype::config::Config`.
2. Build a `GentypeInput` from the current Rust typed artifact:
   module name, source file, output file, output-relative path, implementation
   or signature typedtree, optional paired implementation for `.resi`, and
   type-error state.
3. For `.resi`, follow `read_input_cmt` behavior from
   `compiler/gentype/GenTypeMain.ml:93-134`: inspect the interface first,
   inspect the implementation for warnings, and honor `@genType.ignoreInterface`.
4. Scan annotations with the same predicates as `Annotation.ml`.
5. If annotations exist, translate the typed structure/signature, combine
   translations, add type declarations from module equations, emit JS and type
   text, then write only if contents changed.
6. If no annotations exist and the typed artifact has type errors, log the
   `TypeError` generated-file action.
7. If no annotations exist and there are no type errors, log `NoMatch` and
   delete any stale generated file.

Primary execution should be in-process after Rust typechecking. Reading OCaml
Marshal CMT files should remain limited to existing stale-artifact behavior
unless a direct CMT reader becomes necessary for CLI parity.

## Compile and Integration Phases

Start these phases only after the file-for-file rewrite and all three per-file
review stages are complete.

### Phase 0: Make the Port Compile

- Wire `compiler-rust/src/gentype/mod.rs`.
- Replace placeholders with real Rust types only where the reference port
  already determines the shape.
- Fix ownership and borrow errors without changing the reference algorithm.
- Keep function names, module boundaries, and branch structure stable unless a
  review shows the reference requires a different shape.
- Commit compile-fix clusters separately from semantic parity changes.

Acceptance:

- `cargo build --manifest-path compiler-rust/Cargo.toml` succeeds in debug mode.
- The GenType module tree remains visibly file-for-file with the reference.

### Phase 1: Harness and Baseline

- Add `scripts/test_gentype_output_parity.sh`.
- The script must compare raw generated `.gen.tsx` and `.gen.ts` contents from
  OCaml and Rust without sorting or normalization.
- It takes no repo arguments. Every run covers all three GenType parity
  targets: `tests/gentype_tests/typescript-react-example`,
  `tests/gentype_tests/stdlib-no-shims`, and `/Users/jake/dev/tella-fusion`.
- If Tella is missing, fail clearly with the expected path instead of silently
  skipping it.
- Record counts: generated files, diff hunk count, missing files, extra files,
  and TypeScript typecheck result.
- Keep cleanup explicit and narrow. Do not add new `rm -rf` cleanup.

Acceptance:

- Current Rust baseline is recorded as missing generated outputs rather than
  silently passing.
- Existing stale CMT error parity remains covered.

### Phase 2: CLI and Config

- Replace `Options { gentype: bool }` with a full GenType option struct in
  `compiler-rust/src/bin/bsc.rs`.
- Parse every flag emitted by rewatch:
  `-bs-gentype-module`, `-bs-gentype-module-resolution`,
  `-bs-gentype-export-interfaces`, `-bs-gentype-generated-extension`,
  `-bs-gentype-suffix`, `-bs-gentype-shim`, `-bs-gentype-debug`,
  `-bs-gentype-dep`, `-bs-gentype-source-dir`, `-bs-gentype-dep-path`,
  `-bs-gentype-bsb-project-root`.
- Wire the reviewed `config.rs` port of `GenTypeConfig.t` into `bsc` options.
- Keep rewatch's existing config parsing and flag emission stable unless the
  OCaml reference requires a different flag value or order.

Acceptance:

- Rust can round-trip every GenType config used by the test suites and Tella.
- Config debug dumps, if added, match the OCaml field semantics.

### Phase 3: Input and Generated File Boundaries

- Add `gentype::main::process_typed_artifact`, shaped like
  `GenTypeMain.process_cmt_file`.
- Wire the reviewed `paths.rs`, `module_name.rs`, `generated_files.rs`, and
  source-file fallback ports.
- Implement write-if-required and stale-file removal matching
  `GeneratedFiles.ml`.
- Preserve the current stale CMT error behavior from
  `compiler/gentype/GenTypeMain.ml:85-91`.

Acceptance:

- Files with no GenType annotations remove stale generated output.
- Files with type errors follow the OCaml log action.
- No TypeScript output is emitted before translation exists.

### Phase 4: Annotation, Names, and Resolver Basics

- Wire the reviewed `annotation.rs`, `module_name.rs`, `resolved_name.rs`,
  `import_path.rs`, and `module_resolver.rs` ports into the typed artifact
  entry point.
- Support `@genType`, `@gentype`, `@genType.as`, `@genType.import`,
  `@genType.opaque`, `@@genType.ignoreInterface`, and module-level annotations.
- Match React and ReasonReact resolver exclusions from
  `compiler/gentype/GenTypeMain.ml:160-163`.

Acceptance:

- Annotation detection agrees with OCaml on every source file in both in-repo
  GenType suites.
- Missing/extra output file set matches OCaml before content parity is expected.

### Phase 5: Type Translation Core

- Integrate the reviewed `type_env.rs`, `type_vars.rs`,
  `translate_core_type.rs`, `translate_type_expr_from_types.rs`, and
  `translate_type_declarations.rs` ports.
- Cover primitive mappings, abstract/opaque types, aliases, records, objects,
  tuples, arrays, lists, option/null/nullable/undefined, promises, dicts,
  recursive and mutually recursive types, variants, polymorphic variants,
  unboxed types, GADTs, private declarations, and module equations.
- Use the Rust typedtree and type representation directly; fix typedtree gaps in
  the compiler if GenType reveals missing OCaml-equivalent data.

Acceptance:

- `stdlib-no-shims` generated output and TypeScript typecheck pass.
- Type-only generated files in `typescript-react-example` match OCaml.

### Phase 6: Structure and Signature Translation

- Integrate the reviewed `translate_structure.rs`,
  `translate_signature.rs`, and `translate_signature_from_types.rs` ports.
- Match declaration filtering from `GenTypeMain.ml:16-24` and
  `GenTypeMain.ml:26-52`.
- Implement `.resi` selection and `ignoreInterface` behavior exactly.
- Preserve nested module traversal and module alias handling.

Acceptance:

- Interface-driven generated files match OCaml.
- Module alias and nested-module fixtures match OCaml.

### Phase 7: Emitters and Runtime Imports

- Integrate the reviewed `code_item.rs`, `translation.rs`, `runtime.rs`,
  `emit_text.rs`, `emit_type.rs`, `emit_js.rs`, `emitters.rs`,
  `converter.rs`, and `named_args.rs` ports.
- Match wrapper emission, import/export layout, comments/docstrings, conversion
  helpers, curried/uncurried function handling, labelled and optional args,
  React component output, and generated header text.
- Preserve formatting by matching the emitter algorithm, not by post-processing.

Acceptance:

- `tests/gentype_tests/typescript-react-example` has zero generated-output
  diffs and passes `yarn typecheck`.

### Phase 8: Cross-File and Dependency Resolution

- Finish `ModuleResolver` behavior for source dirs, dependency paths, shims,
  namespace, suffix, generated file extension, and module resolution modes
  `node`, `node16`, and `bundler`.
- Use the same import path decisions as `ImportPath.ml`.
- Ensure generated imports reference `.res.js`, `.bs.js`, shims, or generated
  TypeScript files exactly as OCaml does for each config.

Acceptance:

- Transitive type references and imported JS value fixtures match OCaml.
- Tella generated import paths match OCaml.

### Phase 9: Tella Parity Hardening

- Run the Rust compiler through rewatch from the Tella repo root with the
  repo-local compiler and stdlib.
- Compare every Tella `.gen.ts` and `.gen.tsx` against OCaml output.
- Fix differences by porting the corresponding GenType logic or compiler
  typedtree data, never by Tella-specific conditions.

Acceptance:

- Tella generated file set matches OCaml.
- Tella generated file content matches OCaml.
- Tella TypeScript typecheck passes with Rust-generated GenType output.

### Phase 10: In-Process Integration and Performance

- Avoid reparsing or rereading typed artifacts when Rust already has the typed
  structure/signature in memory.
- Keep resolver caches as performance caches only; they must not change visible
  output.
- Add benchmarks for Tella GenType generation after parity is complete.

Acceptance:

- GenType generation does not dominate Tella build time.
- Existing typedtree, lambda, JavaScript, and error-output parity suites stay at
  their pre-project levels.

## Required Gates

Use debug builds for iteration.

During the rewrite and per-file review stages, these gates are informational
only; the Rust crate is expected not to compile. They become required once
Phase 0 of the compile/integration work starts.

```sh
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
make test-gentype
./scripts/test_gentype_output_parity.sh
./scripts/test_output_parity.sh --quick
./scripts/test_typedtree_parity.sh --quick
./scripts/test_lambda_parity.sh --quick
```

Commit messages for implementation commits should include the GenType parity
status for the touched gate, for example:

```text
Gentype parity:
- typescript-react-example: 24/72 generated outputs match, 48 missing/different
- stdlib-no-shims: 1/1
- Tella: not run
```

## Acceptance Criteria

The project is complete when:

- Rust `bsc -bs-gentype` emits GenType files for all annotated sources.
- In-repo GenType suites produce zero generated-output diffs and pass TypeScript
  typecheck.
- Tella GenType output matches OCaml output byte-for-byte and its TypeScript
  gate passes.
- Existing JavaScript output, typedtree, lambda, and error parity gates are not
  regressed.
- The stale CMT artifact errors covered by the current Rust stub still match
  OCaml.
- Every semantic Rust change has a cited OCaml/ReScript reference location.
