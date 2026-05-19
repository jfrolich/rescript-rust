# Rust GenType Progress

Last updated: 2026-05-19.

## Current State

The file-for-file Rust GenType port is integrated and debug builds complete.
Both Rust CLI `bsc -bs-gentype` and the rewatch in-process compiler now emit
`.gen.ts`/`.gen.tsx` files from Rust typed artifacts.

- rewatch parses `gentypeconfig`, forwards the same `-bs-gentype-*` flag stream
  as the OCaml path, and builds the shared Rust GenType config.
- Rust `bsc` recognizes `-bs-gentype`, carries the parsed config, preserves
  selected stale-artifact error behavior, and emits GenType output for
  annotated current-source typed artifacts.
- The in-process driver calls `process_typed_artifact` for typed interfaces,
  no-interface implementations, and `.resi + @@genType.ignoreInterface`
  implementations, matching the observable hooks at
  `compiler/core/js_implementation.ml:33-34`, `compiler/core/js_implementation.ml:170`,
  `compiler/gentype/GenTypeMain.ml:93-134`, and
  `compiler/gentype/GenTypeMain.ml:136-175`.
- The no-interface CLI path registers the current inferred raw signature before
  GenType processing, matching the artifact boundary that OCaml reaches through
  `compiler/ml/typemod.ml:1779-1788` and
  `compiler/gentype/GenTypeMain.ml:136-175`.
- The single no-argument GenType output parity harness is
  `./scripts/test_gentype_output_parity.sh`. It always compares raw
  `.gen.ts`/`.gen.tsx` output for the react example, stdlib-no-shims, and
  `/Users/jake/dev/tella-fusion`.
- Optional compiler timing now has a `gentype` phase bucket. With
  `RESCRIPT_MODULE_TIMINGS`, `RESCRIPT_RUNTIME_TIMINGS`, or
  `RESCRIPT_PHASE_TIMINGS`, GenType generation is reported separately from
  typecheck and JavaScript codegen.
- Rust in-process GenType now carries the current compilation-unit name into
  `TypeEnv` and strips that prefix before dependency/type translation. This
  matches the shape that OCaml GenType sees after reading CMT/CMTI artifacts in
  `compiler/gentype/GenTypeMain.ml:53-70`, selected through
  `compiler/gentype/Paths.ml:61-86`, before the paths reach
  `compiler/gentype/Dependencies.ml:15-38` and
  `compiler/gentype/TranslateTypeExprFromTypes.ml:78-439`.
- Rust in-process GenType now keeps the compiler module name separate from the
  GenType output-prefix file name. The file name follows
  `compiler/core/js_implementation.ml:72`, `compiler/core/js_implementation.ml:170`,
  `compiler/gentype/GenTypeMain.ml:141`, and
  `compiler/gentype/Paths.ml:61-86`, so lowercase source files such as
  `counter.res` emit imports from `counter.res.js` rather than the capitalized
  compiler module path.
- Rust deriving accessors now keep the `@genType` marker on generated accessor
  values/signatures when the source type has `@deriving(accessors)`. This
  follows `compiler/frontend/ast_derive_projector.ml:30-38`,
  `compiler/frontend/ast_derive_projector.ml:124-132`, and
  `compiler/frontend/ast_attributes.ml:285-290`, allowing GenType to see the
  same generated accessor annotations as the OCaml pipeline.
- Rust GenType now maps `ReactDOM.Ref.t` to the same React DOM ref type as
  `ReactDOM.domRef`, matching `compiler/gentype/TranslateTypeExprFromTypes.ml:389-390`.
  This removes the bogus `ReactDOM.gen` import from `Hooks.gen.tsx`.
- Rust in-process GenType now honors `@@genType.ignoreInterface` by skipping the
  interface artifact and selecting the implementation artifact for output,
  matching `compiler/gentype/GenTypeMain.ml:93-134`. The implementation-side
  hook still runs through the same source/output-file setup as
  `compiler/gentype/GenTypeMain.ml:136-175`.
- Rust in-process GenType now caches declaration-only translations for typed
  artifacts under their `.cmt`/`.cmti` paths before `EmitJs` performs recursive
  imported-type lookup. This is the in-memory equivalent of
  `compiler/gentype/GenTypeMain.ml:26-52` feeding
  `compiler/gentype/EmitJs.ml:437-453`, avoiding the staged CMT decoder while
  preserving the same declaration translation boundary.
- Rust GenType export-module object emission now follows OCaml's
  `Hashtbl.create 1` / `Hashtbl.replace` / `Hashtbl.fold ... :: acc` order
  instead of reversing Rust `IndexMap` insertion order. This matches
  `compiler/gentype/ExportModule.ml:41-57`,
  `compiler/gentype/ExportModule.ml:104-125`, and the OCaml stdlib table
  mechanics in `hashtbl.ml:73-78`, `hashtbl.ml:207-223`,
  `hashtbl.ml:505-508`, and `hashtbl.ml:592-598`.
- Rust GenType module translation now handles implicit structural constraints
  around inner structures the same way OCaml does: remove duplicate value
  bindings and translate the inner structure. This matches
  `compiler/gentype/TranslateStructure.ml:248-258` and recovers GenType output
  for JSX component modules whose PPX output contains duplicate `make`
  bindings.
- Rust GenType explicit module-constraint translation now respects OCaml's
  `Tcoerce_none` split before choosing declaration-signature translation. This
  matches `compiler/gentype/TranslateStructure.ml:234-267`: structurally
  coerced explicit signatures fall through to the typed-signature branch so
  attributes from the explicit signature are preserved.
- Rust GenType's Types-based first-class package translator now threads the
  stored `Tpackage(path, ids, types)` Longident list into
  `TypeEnv.add_type_equations`, matching
  `compiler/gentype/TranslateTypeExprFromTypes.ml:639-670` and
  `compiler/gentype/TypeEnv.ml:96-104`.
- Rust GenType module-type signature lookup now strips only the current
  compilation-unit prefix before walking `TypeEnv`, matching the CMT/CMTI
  artifact boundary at `compiler/gentype/GenTypeMain.ml:53-70` before package
  lookup reaches `compiler/gentype/TypeEnv.ml:160-164`. This lets Types-based
  first-class package translation find local module-type declarations through
  the same unqualified path shape that OCaml GenType reads from saved typed
  artifacts.
- Rust GenType's Types-signature declaration path now preserves
  `Types.type_declaration.type_attributes` when translating declarations from
  scraped module signatures, matching
  `compiler/gentype/TranslateSignatureFromTypes.ml:3-29` feeding those
  attributes into `compiler/gentype/TranslateTypeDeclarations.ml:54-321`. This
  keeps `@genType`, `@as`, doc, tag, unboxed, and import metadata visible for
  alias-module declarations instead of replacing them with an empty parser
  attribute list.
- Latest debug verification: `cargo build --quiet --manifest-path
  compiler-rust/Cargo.toml --bin bsc`, `cargo build --quiet --manifest-path
  rewatch/Cargo.toml`, `make test-gentype`,
  `./scripts/test_gentype_output_parity.sh`,
  `./scripts/test_typedtree_parity.sh --quick`,
  `./scripts/test_lambda_parity.sh --quick`,
  `./scripts/test_js_output_parity.sh --quick`, and
  `./scripts/test_error_output_parity.sh`. Results:
  react example `71/71`, stdlib-no-shims `1/1`, Tella `110/110`,
  typedtree quick `662/662`, lambda quick `662/662`, JS fixture parity
  `344/344`, JS snapshots `662/662`, and error parity `1202/1202`.

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

`scripts/test_gentype_output_parity.sh` is the sole GenType output parity
entrypoint. It rejects positional arguments, snapshots OCaml-generated
`.gen.ts`/`.gen.tsx` files, clears only those generated GenType candidates
before the Rust run, runs the Rust in-process build for the same project, then
reports generated parity, changed/missing/extra files, diff hunk count, and
OCaml/Rust TypeScript typecheck status. The script also snapshots and restores
common source-adjacent JS build artifacts (`.res.js`, `.js`, `.mjs`, `.cjs`) so
the parity run does not leave generated files dirty.

Current Rust generated-output parity:

```text
./scripts/test_gentype_output_parity.sh

typescript-react-example: 71/71 generated outputs match, 0 changed, 0 missing, 0 extra, 0 diff hunks; OCaml typecheck 0, Rust typecheck 0
stdlib-no-shims:          1/1 generated outputs match, 0 changed, 0 missing, 0 extra, 0 diff hunks; OCaml typecheck 0, Rust typecheck 0
Tella:                    110/110 generated outputs match, 0 changed, 0 missing, 0 extra, 0 diff hunks; TypeScript typecheck not configured
```

Earlier partial generated-output baselines before the standalone CLI hook and
source-backed Tella candidate filtering are historical and superseded by the
current counts above. Tella has 110 source-backed generated outputs in the
current harness; standalone checked-in shim outputs without local `.res`/`.resi`
sources are intentionally not compiler-output candidates.

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

Historical Phase 5 adapter notes:

- `TranslateTypeExprFromTypes.ml:560-565` has an OCaml record-copy branch for
  `Tconstr(path, [{desc = Tlink te}], r)`; the Rust branch now has the
  TypeContext access needed to mirror it if a future fixture exposes a
  difference.
- Package `Tpackage` constraint longidents from
  `TranslateTypeExprFromTypes.ml:639-670` now flatten stored `Longident`
  indices to names, and the output parity suites no longer show a package
  module-alias diff.
- Decl-signature type declarations now use decl top-level attributes in
  `translate_signature_from_types`; no current output parity suite exposes a
  remaining declaration-attribute diff.

Verification:

```text
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
git diff --check -- compiler-rust/src/lib.rs compiler-rust/src/gentype/mod.rs compiler-rust/src/gentype/annotation.rs compiler-rust/src/gentype/dependencies.rs compiler-rust/src/gentype/export_module.rs compiler-rust/src/gentype/gen_ident.rs compiler-rust/src/gentype/translation.rs compiler-rust/src/gentype/type_env.rs compiler-rust/src/gentype/type_vars.rs compiler-rust/src/gentype/translate_core_type.rs compiler-rust/src/gentype/translate_signature.rs compiler-rust/src/gentype/translate_signature_from_types.rs compiler-rust/src/gentype/translate_structure.rs compiler-rust/src/gentype/translate_type_declarations.rs compiler-rust/src/gentype/translate_type_expr_from_types.rs
```

## Phase 2 Config Wiring

The in-process compiler now receives the same GenType config data that the OCaml
compiler path derives from CLI flags:

- `compiler-rust/src/gentype/config.rs` can build `GenTypeConfig.t` from an
  explicit flag state or from the `-bs-gentype-*` CLI argument stream, matching
  `compiler/gentype/GenTypeConfig.ml:112-177` and
  `compiler/bsc/rescript_compiler_main.ml:300-343`.
- `compiler-rust/src/bin/bsc.rs` parses `-bs-project-root` plus the full
  GenType flag set before storing `CompilerOptions.gentype_config`.
- `rewatch/src/build/compile.rs` materializes the same flags with
  `get_gentype_args` and feeds them through the shared Rust config builder, so
  subprocess and in-process compilation use one config construction path.
- `compiler-rust/src/driver.rs` now carries `Option<gentype::config::T>` in
  `CompilerOptions`. The config is still not consumed by a generator entrypoint,
  so generated-output parity remains at the current missing-output baseline.

Debug verification:

```text
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
git diff --check -- compiler-rust/src/gentype/config.rs compiler-rust/src/driver.rs compiler-rust/src/bin/bsc.rs rewatch/src/build/compile.rs projects/gentype-rust/PROGRESS.md projects/gentype-rust/RALPH_TODO.md
```

The focused unit test
`cargo test --manifest-path compiler-rust/Cargo.toml gentype::config::tests::parses_cli_backed_gentype_config`
is present but currently blocked by unrelated dirty test code in
`compiler-rust/src/cmi/persistent_env.rs`, where `mod tests` is defined twice.
The normal debug builds above still pass.

## Phase 3 Typed-Artifact Boundary

`compiler-rust/src/gentype/main.rs` now has an in-memory
`process_typed_artifact` entrypoint alongside the CMT path. It mirrors the
observable shape of `compiler/gentype/GenTypeMain.ml:136-175` while accepting
the typedtree already available in the Rust compiler. The boundary also keeps
the same annotation scan and type-error branch as
`compiler/gentype/GenTypeMain.ml:3-14`, and documents the OCaml call/save order
from `compiler/core/js_implementation.ml:33-34`,
`compiler/core/js_implementation.ml:170`, and
`compiler/ml/typemod.ml:1763-1764` / `1785-1787`.

This is not wired into `driver.rs` yet. `TypedArtifact` now carries the
`TypeContext`, and the translation modules use it for descriptor reads. The
next step is to call the entry point from the interface and implementation
typecheck paths.

Debug verification:

```text
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
git diff --check -- compiler-rust/src/gentype/main.rs projects/gentype-rust/PROGRESS.md projects/gentype-rust/RALPH_TODO.md
```

## Phase 5 TypeContext Translation

Typedtree/type-signature GenType translation now receives `&TypeContext`
through `main.rs`, `translate_structure.rs`, `translate_signature.rs`,
`translate_signature_from_types.rs`, `translate_type_declarations.rs`,
`translate_core_type.rs`, `translate_type_expr_from_types.rs`,
`translation.rs`, and `type_vars.rs`.

This removes the previous `TypeExprRef` descriptor placeholder and arity-based
type-variable fallback. The Rust descriptor reads now explicitly mirror the
OCaml reference's direct `type_expr.desc` reads at
`compiler/ml/types.ml:22`, `compiler/gentype/TranslateTypeExprFromTypes.ml:5-12`,
`compiler/gentype/TranslateTypeExprFromTypes.ml:470-742`, and
`compiler/gentype/TypeVars.ml:3-16`.

Generated-output parity at the time of this TypeContext-only step was still the
old missing-output baseline:

```text
typescript-react-example: 0/71 generated outputs match, 71 missing
stdlib-no-shims:          0/1 generated outputs match, 1 missing
Tella:                    0/112 generated outputs match, 112 missing
```

The later in-process generation hook supersedes this baseline.

Debug verification:

```text
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
git diff --check -- compiler-rust/src/gentype/main.rs compiler-rust/src/gentype/translate_core_type.rs compiler-rust/src/gentype/translate_signature.rs compiler-rust/src/gentype/translate_signature_from_types.rs compiler-rust/src/gentype/translate_structure.rs compiler-rust/src/gentype/translate_type_declarations.rs compiler-rust/src/gentype/translate_type_expr_from_types.rs compiler-rust/src/gentype/translation.rs compiler-rust/src/gentype/type_vars.rs projects/gentype-rust/PROGRESS.md projects/gentype-rust/RALPH_TODO.md
```

## Phase 3/7 In-Process Generation Hook

The rewatch in-process compiler now calls Rust GenType directly from typed
artifacts instead of waiting for serialized CMT files. This mirrors
`compiler/core/js_implementation.ml:33-34` / `170`, with the typed artifacts
that `compiler/ml/typemod.ml:1763-1764` and `1785-1787` would have saved in
the OCaml path. For `.resi + .res`, implementation processing is left to the
interface artifact because `compiler/gentype/Paths.ml:61-86` selects `.cmti`
before `.cmt` for the implementation output prefix.

Two small emission fixes were needed once generation ran:

- `gen_ident.rs` now drops the immutable map borrow before inserting a fresh
  anonymous type variable, matching `compiler/gentype/GenIdent.ml:16-23`.
- `emit_js.rs` keeps `inline_one_level` missing-type lookup non-fatal, matching
  the `Not_found` handler in `compiler/gentype/EmitJs.ml:662-678`.

Current generated-output parity:

```text
./scripts/test_gentype_output_parity.sh

typescript-react-example: 64/71 generated outputs match, 7 changed, 0 missing, 0 extra, 9 diff hunks; OCaml typecheck 0, Rust typecheck 0
stdlib-no-shims:          1/1 generated outputs match, 0 changed, 0 missing, 0 extra, 0 diff hunks; OCaml typecheck 0, Rust typecheck 0
Tella:                    107/112 generated outputs match, 3 changed, 2 missing, 0 extra, 3 diff hunks; TypeScript typecheck not configured
```

This improvement comes from aligning Rust's in-process typed artifact with the
CMT-shaped input that OCaml GenType reads. `main.rs` records the current module
name selected by `compiler/gentype/Paths.ml:61-86`; `type_env.rs` strips exactly
that compilation-unit prefix before the reference dependency/type translation
paths in `compiler/gentype/Dependencies.ml:15-38` and
`compiler/gentype/TranslateTypeExprFromTypes.ml:78-439`. That removes self
imports and lets local `Core.Map.t`/`Core.Set.t` paths hit the same special
cases as OCaml.

The Tella import-path improvement comes from passing the same package-root flag
into the rewatch in-process GenType config that the OCaml bsc CLI path sees:
`compiler/bsc/rescript_compiler_main.ml:266-269` sets
`GenTypeConfig.project_root`, `compiler/gentype/GenTypeConfig.ml:124-131`
builds `Config.t` from it, and `compiler/gentype/Paths.ml:48-56` plus
`compiler/gentype/ModuleResolver.ml:111-164` use it for relative output/source
resolution.

The record-field quote improvement comes from mirroring OCaml's
`String.escaped` call in `compiler/gentype/TranslateTypeDeclarations.ml:51`.
Rust now preserves apostrophes inside double-quoted TypeScript property names
instead of using `escape_default`'s Rust literal escaping.

The lowercase source import improvement comes from deriving the in-process
GenType `file_name` from the CMT/output-prefix shape rather than from the
capitalized compiler module name. This follows the OCaml call chain from
`compiler/core/js_implementation.ml:72` / `170` into
`compiler/gentype/GenTypeMain.ml:141` and `compiler/gentype/Paths.ml:61-86`.
The compiler module name is still threaded separately for current-unit type
path stripping.

Debug verification:

```text
cargo build --manifest-path compiler-rust/Cargo.toml
cargo build --manifest-path rewatch/Cargo.toml
./scripts/test_gentype_output_parity.sh
git diff --check -- compiler-rust/src/driver.rs compiler-rust/src/gentype/emit_js.rs compiler-rust/src/gentype/gen_ident.rs compiler-rust/src/gentype/main.rs compiler-rust/src/gentype/paths.rs projects/gentype-rust/PROGRESS.md projects/gentype-rust/RALPH_TODO.md
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

## Persistent Alias Scrape

- `compiler-rust/src/gentype/translate_structure.rs` now mirrors the
  persistent-module branch of `Env.scrape_alias` for `module M = N` aliases.
  The reference path is `compiler/gentype/TranslateStructure.ml:174-183`,
  `compiler/ml/env.ml:1435-1449`, and the persistent `find_module` branch at
  `compiler/ml/env.ml:865-875`.
- The Rust implementation first uses the typed `mod_env` lookup when available,
  then falls back to `TypeContext::get_or_load_raw_module_sig` for persistent
  `Pident` aliases that are available through the in-process persistent
  environment but not installed as root module bindings in the local `Env`.
- This is intentionally not a generated-output normalization. The remaining
  `Wrapper.gen.tsx` diff shows the next real issue: the fallback signature is
  already persistent-path substituted, so value types still print through
  `MyModule_t` instead of OCaml's `MyModuleAlias_t`. A naive cross-file
  typed-signature cache was tested and rejected because `TypeExprRef` values are
  scoped to each file's `TypeContext`.
- Debug verification: `cargo build --quiet --manifest-path
  compiler-rust/Cargo.toml`, `cargo build --quiet --manifest-path
  rewatch/Cargo.toml`, and `./scripts/test_gentype_output_parity.sh`.
  Results: React `64/71`, 7 changed, 0 missing, 0 extra, 9 hunks, OCaml/Rust
  typecheck `0/0`; stdlib-no-shims `1/1`, OCaml/Rust typecheck `0/0`; Tella
  `107/112`, 3 changed, 2 missing, 0 extra, 3 hunks, TypeScript typecheck not
  configured.

## Completion Audit

The implementation goal from `PLAN.md` is satisfied for the active supported
path: Rust generates GenType from current typed artifacts, the no-argument
parity harness reports zero generated-output diffs for all three scopes, and
the normal compiler parity gates remain green.

The direct `Cmt_format.read_cmt` typedtree decoder in
`compiler-rust/src/gentype/main.rs` remains intentionally limited to the
existing stale-artifact diagnostics path. The primary Rust compiler path uses
the in-memory typedtree after typechecking, matching the plan's architecture
note that direct CMT reading should remain limited unless necessary for CLI
parity. Standalone CLI parity for current sources is covered by
`bsc -bs-gentype` emitting from the current typed artifact.
