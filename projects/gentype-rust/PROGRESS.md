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
- Rewrite Stage 1 now has an initial file-for-file Rust port under
  `compiler-rust/src/gentype/`. These files are intentionally not wired into
  the crate yet.

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

Continue with Rewrite Stage 2 from `PLAN.md`:

1. Port one config/path/import/file-effect file at a time from
   `compiler/gentype`.
2. Keep function names, helper names, data-flow shape, and source-location
   references as close to OCaml as Rust allows.
3. Run the three per-file review passes before marking each file done:
   surface/naming, control/data flow, and output-sensitive semantics.
4. Do not make compilation the goal until all four rewrite stages and their
   reviews are complete.
