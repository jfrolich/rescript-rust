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
- Rewrite Stage 4 has a file-for-file Rust port of
  `EmitText.ml`, `EmitType.ml`, `Emitters.ml`/`.mli`, `EmitJs.ml`,
  `NamedArgs.ml`, `Converter.ml`, and `GenTypeMain.ml`.
- Phase 0 has wired `compiler-rust/src/gentype/mod.rs` into the crate and the
  debug compiler/rewatch builds now complete.
- The project now has a single no-argument GenType output parity harness:
  `./scripts/test_gentype_output_parity.sh`. It always compares raw
  `.gen.ts`/`.gen.tsx` output for the react example, stdlib-no-shims, and
  `/Users/jake/dev/tella-fusion`.

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

## Harness Status

`scripts/test_gentype_output_parity.sh` was added as the sole GenType output
parity entrypoint. It rejects positional arguments, snapshots OCaml-generated
`.gen.ts`/`.gen.tsx` files, runs the Rust in-process build for the same project,
then reports generated parity, changed/missing/extra files, diff hunk count,
and OCaml/Rust TypeScript typecheck status.

The script has only been syntax-checked so far:

```text
bash -n scripts/test_gentype_output_parity.sh
```

Full execution is still blocked until the Phase 0 Rust GenType module wiring
compiles.

Update: Phase 0 module wiring now compiles, so the next useful harness run
should establish the Rust generated-output baseline.

## Phase 0 Compile Wiring

The staged GenType tree is now part of the compiler crate:

- `compiler-rust/src/lib.rs` exports `pub mod gentype`.
- `compiler-rust/src/gentype/mod.rs` mirrors the OCaml GenType module set.
- `TypeEnv.new_module_type` now stores the typed signature plus the decl
  signature derived by `typemod::decl_signature_from_typed_signature`, matching
  OCaml's `Typedtree.signature.sig_type` use in
  `compiler/gentype/TypeEnv.ml:39-45` and package translation in
  `compiler/gentype/TranslateTypeExprFromTypes.ml:639-670`.
- Decl-attribute helpers in `annotation.rs` let Types-signature translation
  read the same annotation tags as `compiler/gentype/Annotation.ml:69-181`
  after Rust typemod has converted parser payloads to `decl::Attribute`.

Known Phase 5 adapters still present:

- `translate_type_expr_from_types::type_expr_desc` still needs a real
  TypeContext-backed descriptor reader for `compiler/ml/types.ml:type_expr.desc`.
- `type_vars::extract_from_type_expr_refs` uses arity placeholders until
  TypeContext is threaded so it can read the actual `Tvar` names from
  `compiler/gentype/TypeVars.ml:3-13`.
- `TranslateTypeExprFromTypes.ml:560-565` has an OCaml record-copy branch for
  `Tconstr(path, [{desc = Tlink te}], r)`; the Rust branch currently relies on
  argument translation following the `Tlink` until TypeContext-backed record
  copy is wired.
- Package `Tpackage` constraint longidents from
  `TranslateTypeExprFromTypes.ml:639-670` still need `ParseArena` threading so
  Rust can flatten the stored `Longident` indices to names.
- Decl-signature type declarations currently use parser-empty top-level
  attributes in `translate_signature_from_types`; constructor/label/value/module
  decl attributes are handled, but top-level type attributes still need a
  direct decl-attribute path before output parity work.

Verification:

```text
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
git diff --check -- compiler-rust/src/lib.rs compiler-rust/src/gentype/mod.rs compiler-rust/src/gentype/annotation.rs compiler-rust/src/gentype/dependencies.rs compiler-rust/src/gentype/export_module.rs compiler-rust/src/gentype/gen_ident.rs compiler-rust/src/gentype/translation.rs compiler-rust/src/gentype/type_env.rs compiler-rust/src/gentype/type_vars.rs compiler-rust/src/gentype/translate_core_type.rs compiler-rust/src/gentype/translate_signature.rs compiler-rust/src/gentype/translate_signature_from_types.rs compiler-rust/src/gentype/translate_structure.rs compiler-rust/src/gentype/translate_type_declarations.rs compiler-rust/src/gentype/translate_type_expr_from_types.rs
```

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

For the `EmitType.ml` Stage 4 chunk:

- `EmitType.ml` was ported to `compiler-rust/src/gentype/emit_type.rs` against
  `compiler/gentype/EmitType.ml:1-455`.
- Surface/control/output-sensitive review checked header/interface/react helper
  emission from `EmitType.ml:3-62`, recursive type rendering and variant union
  formatting from `EmitType.ml:63-253`, object field/function rendering from
  `EmitType.ml:254-329`, and export/import/type-cast helpers from
  `EmitType.ml:331-455`.
- The Rust draft keeps the OCaml helper boundary for `require ~early` from
  `EmitType.ml:419-425` even though Rust emits through a direct function call.
- `rustfmt` was run on the new file and `git diff --check` passed.
- The new file is not wired into the crate, so debug build/parity gates were not
  run for this non-compiling rewrite stage.

For the `Emitters.ml` Stage 4 chunk:

- `Emitters.ml` and `Emitters.mli` were ported to
  `compiler-rust/src/gentype/emitters.rs` against
  `compiler/gentype/Emitters.ml:1-52` and
  `compiler/gentype/Emitters.mli:1-9`.
- Surface/control/output-sensitive review checked the emitter bucket layout from
  `Emitters.ml:1-16`, prepend-style string accumulation from
  `Emitters.ml:18-42`, and final bucket/reverse ordering from
  `Emitters.ml:44-52`.
- The previous `EmitType` draft was corrected to thread `Emitters.t` by value
  and return the updated emitter, matching the OCaml call pattern in
  `EmitType.ml:331-452` and the `Emitters.mli` signatures at
  `Emitters.mli:4-9`.
- `rustfmt` was run on `emitters.rs` and `emit_type.rs`, and `git diff --check`
  passed.
- The new file is not wired into the crate, so debug build/parity gates were not
  run for this non-compiling rewrite stage.

For the `EmitJs.ml` Stage 4 chunk:

- `EmitJs.ml` was ported to `compiler-rust/src/gentype/emit_js.rs` against
  `compiler/gentype/EmitJs.ml:1-711`.
- Surface/control/output-sensitive review checked environment/require map
  updates from `EmitJs.ml:3-24`, type export-map construction from
  `EmitJs.ml:26-61`, type export/interface decisions from `EmitJs.ml:74-137`,
  import/export value emission and React props rewriting from
  `EmitJs.ml:139-389`, require emission from `EmitJs.ml:391-415`, recursive CMT
  import-type loading from `EmitJs.ml:417-511`, annotation propagation from
  `EmitJs.ml:513-602`, and final emission ordering from `EmitJs.ml:604-711`.
- The staged Rust port keeps the same emitter value-threading API as
  `Emitters.mli:4-9` and uses a Rust callback boundary for CMT translation where
  OCaml calls `Cmt_format.read_cmt` at `EmitJs.ml:449-453`.
- `rustfmt` was run on the new file and `git diff --check` passed.
- The new file is not wired into the crate, so debug build/parity gates were not
  run for this non-compiling rewrite stage.

For the `GenTypeMain.ml` Stage 4 chunk:

- `GenTypeMain.ml` was ported to `compiler-rust/src/gentype/main.rs` against
  `compiler/gentype/GenTypeMain.ml:1-175`.
- Surface/control/output-sensitive review checked CMT annotation classification
  from `GenTypeMain.ml:3-24`, declaration-only translation for imported CMTs
  from `GenTypeMain.ml:26-52`, full CMT translation from `GenTypeMain.ml:53-70`,
  generated-file emission from `GenTypeMain.ml:72-83`, stale artifact handling
  from `GenTypeMain.ml:85-91`, interface/implementation selection and
  `@@genType.ignoreInterface` handling from `GenTypeMain.ml:93-134`, and
  `process_cmt_file` orchestration from `GenTypeMain.ml:136-175`.
- The staged Rust port defines the `BinaryAnnots`/`InputCmt` boundary used by
  earlier staged files. Actual CMT decoding remains a Phase 3 wiring task, while
  the stale-artifact logging boundary mirrors `GenTypeMain.ml:85-91`.
- `rustfmt` was run on the new file and `git diff --check` passed.
- The new file is not wired into the crate, so debug build/parity gates were not
  run for this non-compiling rewrite stage.

Resolved setup note:

The latest debug build attempt after merging `fuzz-errors` failed before code
diagnostics with:

```text
rustc-LLVM ERROR: IO failure on output stream: No space left on device
```

The later Phase 0 debug builds listed above completed.

## Next Session

Continue with Phase 2/3 integration from `PLAN.md`:

1. Replace the remaining Phase 5 adapters above with real TypeContext/ParseArena
   access where the OCaml reference reads `type_expr.desc`, `Tvar` names, or
   package constraint longidents.
2. Keep function names, helper names, data-flow shape, and source-location
   references as close to OCaml as Rust allows.
3. Wire `gentype::main` from Rust `bsc`/in-process typed artifacts and run
   `./scripts/test_gentype_output_parity.sh` to get the first generated-output
   baseline.
