# Rust GenType Progress

Last updated: 2026-05-18.

## Current State

The `fuzz-errors` branch has been fast-forward merged into `combined`. GenType
support in Rust is still a stub:

- rewatch parses `gentypeconfig` and forwards GenType flags.
- Rust `bsc` recognizes `-bs-gentype`.
- Rust `bsc` checks selected CMT files enough to preserve stale-artifact error
  output parity.
- Rust `bsc` does not generate `.gen.tsx` or `.gen.ts`.
- Rewrite Stage 1 has an initial file-for-file Rust port under
  `compiler-rust/src/gentype/`. These files are intentionally not wired into
  the crate yet.
- Rewrite Stage 2 now also has an initial file-for-file Rust port for config,
  paths, imports, generated-file effects, dependency helpers, runtime names,
  and export-module tables.
- Rewrite Stage 3 has started with initial file-for-file Rust ports of
  `Annotation.ml`, `ModuleResolver.ml`, `TranslateCoreType.ml`,
  `TranslateSignature.ml`, `TranslateSignatureFromTypes.ml`,
  `TranslateStructure.ml`, `TranslateTypeDeclarations.ml`,
  `TranslateTypeExprFromTypes.ml`, and `TypeEnv.ml`/`.mli`. These files are
  still intentionally not wired into the crate.
- Rewrite Stage 4 has started with initial file-for-file Rust ports of
  `EmitText.ml`, `NamedArgs.ml`, and `Converter.ml`. These files are still
  intentionally not wired into the crate.

## Reference Inventory

Primary OCaml GenType implementation:

- `compiler/gentype/GenTypeMain.ml`
- `compiler/gentype/GenTypeConfig.ml`
- `compiler/gentype/Annotation.ml`
- `compiler/gentype/Paths.ml`
- `compiler/gentype/ModuleResolver.ml`
- `compiler/gentype/ImportPath.ml`
- `compiler/gentype/TranslateStructure.ml`
- `compiler/gentype/TranslateSignature.ml`
- `compiler/gentype/TranslateTypeDeclarations.ml`
- `compiler/gentype/TranslateCoreType.ml`
- `compiler/gentype/TranslateTypeExprFromTypes.ml`
- `compiler/gentype/EmitJs.ml`
- `compiler/gentype/EmitType.ml`
- `compiler/gentype/EmitText.ml`
- `compiler/gentype/Translation.ml`
- `compiler/gentype/CodeItem.ml`
- `compiler/gentype/TypeEnv.ml`
- `compiler/gentype/TypeVars.ml`
- `compiler/gentype/Runtime.ml`

ReScript source copy:

- `tests/syntax_tests/data/idempotency/genType/src/*.res`

Existing tests:

- `tests/gentype_tests/typescript-react-example`
- `tests/gentype_tests/stdlib-no-shims`

## Baseline Counts

Current local counts:

- `tests/gentype_tests/typescript-react-example`: 71 checked-in generated
  `.gen.tsx` or `.gen.ts` files.
- `tests/gentype_tests/stdlib-no-shims`: 1 checked-in generated file.
- `/Users/jake/dev/tella-fusion`: 112 checked-in generated `.gen.tsx` or
  `.gen.ts` files and 253 `@genType` or `@gentype` annotation occurrences.
- Tella webapp uses `.gen.ts` through `generatedFileExtension` and defines
  shims for `Js`, `Pervasives`, and `Spice`.

These counts are a starting point for the parity harness. The harness should
report current counts itself because Tella and fixtures can change.

## Recent Verification

For the Stage 1 port:

- `rustfmt compiler-rust/src/gentype/*.rs` was run on the new files.
- The new files are not wired into the crate, so debug build/parity gates were
  not run for this non-compiling rewrite stage.
- Surface/control/output-sensitive review was performed while porting. The
  known integration gap is exact `Log_.ml` filename rendering:
  `compiler/gentype/Log_.ml:54-77` gets a filename string from
  `Location.get_pos_info`, while Rust `Location` currently stores an interned
  filename id and will need the arena/source resolver when the port is wired.

For the Stage 2 port:

- `rustfmt` was run on the new Stage 2 files.
- Surface/control/output-sensitive review was performed while porting.
- Known integration-sensitive point: `compiler/gentype/ExportModule.ml:3-9`
  uses OCaml `Hashtbl` and `ExportModule.ml:104-106` folds it in hash-table
  order. The Rust draft uses an order-sensitive `IndexMap`, not a sorted map,
  and final integration must verify whether exact OCaml bucket traversal needs
  a dedicated table representation.

For the first Stage 3 chunk:

- `Annotation.ml` was ported to `compiler-rust/src/gentype/annotation.rs`
  against `compiler/gentype/Annotation.ml:1-295`.
- `TypeEnv.ml` and `TypeEnv.mli` were ported to
  `compiler-rust/src/gentype/type_env.rs` against
  `compiler/gentype/TypeEnv.ml:1-204` and
  `compiler/gentype/TypeEnv.mli:1-23`.
- `rustfmt` was run on the new files and `git diff --check` passed.
- The new files are not wired into the crate, so debug build/parity gates were
  not run for this non-compiling rewrite stage.
- Integration-sensitive point: `Annotation.ml` reads payload strings directly
  from Parsetree values, while Rust Parsetree stores interned string and
  longident indices. The Rust draft threads `ParseArena` through annotation
  helpers so payload interpretation can stay source-order equivalent.
- Integration-sensitive point: `TypeEnv.ml:76-94` uses record-copy updates for
  type equations, unlike the mutable map updates earlier in the same file. The
  Rust draft keeps that copy shape with cloned `Rc<RefCell<_>>` environments.

For the resolver Stage 3 chunk:

- `ModuleResolver.ml` was ported to
  `compiler-rust/src/gentype/module_resolver.rs` against
  `compiler/gentype/ModuleResolver.ml:1-201`.
- The Rust draft preserves the OCaml lazy resolver boundary from
  `ModuleResolver.ml:73-106`: source/dependency maps are constructed on first
  `apply`, not during resolver creation.
- The filesystem traversal, uppercase/lowercase fallback, shim branch, and
  relative import path construction were reviewed against
  `ModuleResolver.ml:6-69`, `ModuleResolver.ml:86-105`, and
  `ModuleResolver.ml:111-201`.
- `rustfmt` was run on the new file and `git diff --check` passed.
- The new file is not wired into the crate, so debug build/parity gates were
  not run for this non-compiling rewrite stage.

For the first type-translation Stage 3 chunk:

- `TranslateTypeExprFromTypes.ml` was ported to
  `compiler-rust/src/gentype/translate_type_expr_from_types.rs` against
  `compiler/gentype/TranslateTypeExprFromTypes.ml:1-761`.
- Helper names and flow-sensitive boundaries are preserved, including
  `remove_option`, `path_to_list`, `translate_obj_type`, `translate_constr`,
  `process_variant`, `translate_arrow_type`, `translateTypeExprFromTypes_`,
  `translateTypeExprsFromTypes_`, and
  `signature_to_module_runtime_representation`.
- Surface/control/output-sensitive review checked the constructor-special-case
  order from `TranslateTypeExprFromTypes.ml:78-439`, polymorphic variant
  branches from `TranslateTypeExprFromTypes.ml:447-468` and
  `TranslateTypeExprFromTypes.ml:590-638`, package handling from
  `TranslateTypeExprFromTypes.ml:639-670`, and signature object lowering from
  `TranslateTypeExprFromTypes.ml:679-737`.
- Rust type access still has integration friction: the staged file preserves
  the OCaml control flow but assumes direct `TypeExprRef` descriptor access
  until the compile-wiring phase chooses the final context/arena adapter.
- `rustfmt` was run on the new file and `git diff --check` passed.
- The new file is not wired into the crate, so debug build/parity gates were
  not run for this non-compiling rewrite stage.

For the typedtree core-type Stage 3 chunk:

- `TranslateCoreType.ml` was ported to
  `compiler-rust/src/gentype/translate_core_type.rs` against
  `compiler/gentype/TranslateCoreType.ml:1-295`.
- The port preserves the OCaml helper names and order for `remove_option`,
  `process_variant`, `translate_arrow_type`, `translateCoreType_`,
  `translateCoreTypes_`, and `translate_core_type`.
- Surface/control/output-sensitive review checked arrow argument dependency
  accumulation from `TranslateCoreType.ml:52-120`, typedtree core-type dispatch
  from `TranslateCoreType.ml:122-280`, polymorphic variant label handling from
  `TranslateCoreType.ml:177-249`, and package lowering from
  `TranslateCoreType.ml:250-279`.
- Rust annotation helpers require `ParseArena` to resolve interned attribute
  names, so the staged Rust signatures thread `arena` explicitly while keeping
  the OCaml traversal order.
- `rustfmt` was run on the new file and `git diff --check` passed.
- The new file is not wired into the crate, so debug build/parity gates were
  not run for this non-compiling rewrite stage.

For the type-declaration Stage 3 chunk:

- `TranslateTypeDeclarations.ml` was ported to
  `compiler-rust/src/gentype/translate_type_declarations.rs` against
  `compiler/gentype/TranslateTypeDeclarations.ml:1-373`.
- The port preserves the OCaml declaration-kind shape, including the misspelled
  helper `traslate_declaration_kind`, and keeps the import-type, opaque,
  record, variant, recursive declaration, and type-env update order aligned.
- Surface/control/output-sensitive review checked type export creation from
  `TranslateTypeDeclarations.ml:11-21`, `@as` variant case handling from
  `TranslateTypeDeclarations.ml:23-37`, record field renaming from
  `TranslateTypeDeclarations.ml:39-53`, declaration dispatch from
  `TranslateTypeDeclarations.ml:145-321`, and recursive/nonrecursive type-env
  mutation from `TranslateTypeDeclarations.ml:357-373`.
- Rust still needs compile-wiring review around full `Location` versus
  `LocIdx` boundaries for future `Types.type_declaration` inputs, but the
  typedtree path passes the original `typ_loc` index through annotation checks.
- `rustfmt` was run on the new file and `git diff --check` passed.
- The new file is not wired into the crate, so debug build/parity gates were
  not run for this non-compiling rewrite stage.

For the signature/structure Stage 3 chunk:

- `TranslateSignatureFromTypes.ml`, `TranslateSignature.ml`, and
  `TranslateStructure.ml` were ported to:
  `compiler-rust/src/gentype/translate_signature_from_types.rs`,
  `compiler-rust/src/gentype/translate_signature.rs`, and
  `compiler-rust/src/gentype/translate_structure.rs`.
- References:
  `compiler/gentype/TranslateSignatureFromTypes.ml:1-110`,
  `compiler/gentype/TranslateSignature.ml:1-169`, and
  `compiler/gentype/TranslateStructure.ml:1-366`.
- Surface/control/output-sensitive review checked signature item dispatch and
  module-type filtering from `TranslateSignature.ml:97-169`,
  Types-signature dispatch from `TranslateSignatureFromTypes.ml:51-110`, value
  annotation recovery from `TranslateStructure.ml:3-73`, value-binding
  duplicate filtering from `TranslateStructure.ml:75-159`, module binding
  dispatch from `TranslateStructure.ml:161-270`, and structure item dispatch
  from `TranslateStructure.ml:272-366`.
- Rust typedtree currently has a newer multi-parameter `Texp_function` shape,
  so `translate_structure.rs` preserves the OCaml traversal intent while using
  the first typed function parameter/body path as the staged adapter. Compile
  wiring must revisit this adapter against actual generated output.
- `rustfmt` was run on the new files and `git diff --check` passed.
- The new files are not wired into the crate, so debug build/parity gates were
  not run for this non-compiling rewrite stage.

For the first Stage 4 utility/emitter chunk:

- `EmitText.ml`, `NamedArgs.ml`, and `Converter.ml` were ported to
  `compiler-rust/src/gentype/emit_text.rs`,
  `compiler-rust/src/gentype/named_args.rs`, and
  `compiler-rust/src/gentype/converter.rs`.
- References:
  `compiler/gentype/EmitText.ml:1-13`,
  `compiler/gentype/NamedArgs.ml:1-14`, and
  `compiler/gentype/Converter.ml:1-89`.
- Surface/control/output-sensitive review checked generic string formatting,
  optional argument grouping, unit-argument removal, inline type substitution,
  circular-reference detection, and converter debug logging.
- `rustfmt` was run on the new files and `git diff --check` passed.
- The new files are not wired into the crate, so debug build/parity gates were
  not run for this non-compiling rewrite stage.

Earlier setup note:

The latest debug build attempt after merging `fuzz-errors` failed before code
diagnostics with:

```text
rustc-LLVM ERROR: IO failure on output stream: No space left on device
```

Free disk space before doing implementation work. Do not use `rm -rf`; inspect
large files first and remove only explicit, known-safe files if cleanup is
needed.

## Next Session

Continue with Rewrite Stage 3 from `PLAN.md`:

1. Continue with the remaining translation files from `compiler/gentype`.
2. Keep function names, helper names, data-flow shape, and source-location
   references as close to OCaml as Rust allows.
3. Run the three per-file review passes before marking each file done:
   surface/naming, control/data flow, and output-sensitive semantics.
4. Do not make compilation the goal until all four rewrite stages and their
   reviews are complete.
