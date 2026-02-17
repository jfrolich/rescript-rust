# Parser Strict Side Tables Plan

## Goal

Make the parser AST strictly side-table based for attributes and sparse payloads, with no runtime location-based stashing.

This means:

1. No inline `Attributes` payloads in `compiler-rust/src/parser/ast.rs` node shapes (including declaration/module-related nodes still carrying inline attributes).
2. No `stash_*`/`pending_*` flow in `ParseArena`; all sparse/attribute data is written directly by stable owner index/ID at construction time.
3. No runtime stripping fallback as correctness mechanism. The representation itself must already be strict.

---

## Non-Goals

1. Redesigning typedtree representation in `compiler-rust/src/types/typedtree.rs`.
2. Changing OCaml frozen `parsetree0` wire-format semantics.
3. Broad parser algorithm changes unrelated to ownership/data layout.

---

## Hard Constraints

1. Preserve parser/binary parity behavior:
   - `scripts/test_parser_ast_parity.sh` must stay green.
2. Preserve PPX behavior (`jsx_ppx`, built-in `ppx`, internal `spice_ppx`).
3. Keep changes atomic and bisectable.
4. No new unsafe parser/compiler memory logic unless absolutely unavoidable.

---

## Baseline (February 17, 2026)

From code scan:

1. Remaining inline AST attribute fields in `compiler-rust/src/parser/ast.rs`: `13` named `...attributes` fields.
2. Additional inline attribute carriers in parser AST shape:
   - `TypeArg.attrs`
   - `RowField::Rtag(..., Attributes, ...)`
   - `ObjectField::Otag(..., Attributes, ...)`
   - `Pstr_eval(..., Attributes)`
   - `Pstr_extension(..., Attributes)`
   - `Psig_extension(..., Attributes)`
3. `stash_*` call sites across `compiler-rust/src`: `119`.
4. `pending_*` usage concentrated in `compiler-rust/src/parse_arena.rs`.

---

## Target Architecture

## A. Owner-Indexed Side Tables Only

All sparse/attribute data must be stored by stable owner key:

1. Arena-indexed owners (already present):
   - `ExprIdx`, `PatIdx`, `CoreTypeIdx`, `ModExprIdx`, `ModTypeIdx`
2. New typed IDs for by-value AST nodes that currently carry inline attributes:
   - `ValueBindingAttrIdx`
   - `ValueDescriptionAttrIdx`
   - `TypeDeclarationAttrIdx`
   - `ConstructorDeclarationAttrIdx`
   - `LabelDeclarationAttrIdx`
   - `TypeExtensionAttrIdx`
   - `ExtensionConstructorAttrIdx`
   - `ModuleBindingAttrIdx`
   - `ModuleDeclarationAttrIdx`
   - `ModuleTypeDeclarationAttrIdx`
   - `OpenDescriptionAttrIdx`
   - `IncludeDeclarationAttrIdx`
   - `IncludeDescriptionAttrIdx`
   - plus IDs for `TypeArg`, row-tag field, object-tag field, and extension/eval tuple payload sites.

Each owner ID gets a dedicated side table (`Vec<Attributes>`), defaulting to empty.

## B. Immediate Allocation/Registration

Remove location-based pending state:

1. No `pending_*` maps.
2. No `stash_*_for_loc` APIs.
3. Node construction APIs must either:
   - allocate owner index first, then write sparse data immediately, or
   - construct node via helper that writes side tables in one step.

## C. Read Paths Use Owner Keys Only

Attribute/sparse getters should rely on owner key directly, not location fallback.

---

## Execution Plan

## Phase 0: Safety Rails and Inventory Freeze

1. Freeze initial inventory in `INVENTORY.md`.
2. Add grep-based guards (CI/local script section):
   - fail on `stash_` usage
   - fail on `pending_` usage
   - fail on inline `...attributes: Attributes` in parser AST target nodes
3. Record baseline parity and benchmark numbers in `PROGRESS.md`.

Exit criteria:

1. Inventory complete and source-linked.
2. Guard commands documented and reproducible.

## Phase 1: Strict API for Existing Arena-Indexed Kinds

1. Introduce strict write APIs for existing side-table-managed kinds:
   - expression sparse fields
   - expr/pat/core-type/mod-expr/mod-type attributes
2. Add helper constructors that take sparse payload/attributes explicitly and register immediately.
3. Keep compatibility shims temporarily while call sites are migrated.

Exit criteria:

1. All new call sites can avoid stash/pending.
2. `cargo check` and parity green.

## Phase 2: Remove Pending/Stash for Existing Arena Kinds

1. Migrate parser/PPX/mapper paths from `stash_*` to direct owner-index writes.
2. Remove pending maps for expression/pattern/core-type/module arena kinds.
3. Remove location fallback from `*_by_ref` reads where owner can be determined.

Exit criteria:

1. `rg "stash_|pending_" compiler-rust/src/parse_arena.rs` no matches for removed flows.
2. Existing parity suites green.

## Phase 3: Side Tables for Declaration/Module Nodes

1. Add typed attr-ID fields to by-value nodes that currently carry inline attrs.
2. Add corresponding side tables in `ParseArena`.
3. Create constructors/builders to allocate ID + write attributes in one place.
4. Remove inline `...attributes` fields from these structs.

Exit criteria:

1. No declaration/module node stores `Attributes` inline.
2. All creation paths compile without field initializers for removed inline attrs.

## Phase 4: TypeArg/RowField/ObjectField Attribute Migration

1. Replace inline `TypeArg.attrs` with side-table owner key.
2. Split `RowField::Rtag` and `ObjectField::Otag` into owned structs carrying side-table owner keys.
3. Update parser/typecore/printers/sexp/mappers accordingly.

Exit criteria:

1. No inline `Attributes` in these variants/structs.
2. Type-checker and printer paths preserve behavior.

## Phase 5: Structure/Signature Eval/Extension Payload Attribute Migration

1. Replace tuple forms carrying inline `Attributes`:
   - `Pstr_eval`
   - `Pstr_extension`
   - `Psig_extension`
2. Use side-table owner keys attached to dedicated wrapper structs.

Exit criteria:

1. No inline tuple `Attributes` carriers remain in parser AST.

## Phase 6: Delete Legacy Stash/Pending Infrastructure

1. Remove:
   - `stash_pending_value`, `take_pending_value`
   - `stash_pending_attrs`, `take_pending_attrs`
   - all `stash_*_for_loc` APIs
   - all `pending_*_by_loc` maps
2. Remove any fallback reads that depend on pending state.

Exit criteria:

1. `rg "stash_|pending_" compiler-rust/src` returns zero relevant matches.
2. `ParseArena` has strict direct owner-based semantics only.

## Phase 7: Validation and Performance Gates

Required validation after each sub-phase and at phase completion:

1. `cargo check --manifest-path compiler-rust/Cargo.toml -q`
2. `scripts/test_parser_ast_parity.sh`
3. Single-thread in-process benchmark:
   - `RAYON_NUM_THREADS=1 PARSER_BENCH_WARMUP=2 PARSER_BENCH_RUNS=10 cargo test --manifest-path compiler-rust/Cargo.toml --release --lib -- benchmark_cold_repeat --ignored --nocapture`

Acceptance threshold:

1. Zero parity regressions.
2. No benchmark panic/crash.
3. Performance non-regression within agreed noise envelope.

---

## Commit Strategy

Use one commit per mechanical concern:

1. infra: add owner-ID side-table scaffolding
2. migrate: expression/pattern/core/module call sites off stash
3. migrate: declaration/module attr fields to side tables
4. migrate: typearg/row/object attrs to side tables
5. migrate: structure/signature eval/extension attrs
6. cleanup: delete pending/stash APIs and dead code
7. docs: update project progress and final summary

Every commit:

1. compiles
2. keeps parity green (or only temporary branch-local state before immediate fix in same task commit)

---

## Risks and Mitigations

1. Risk: owner identity collisions for by-value nodes.
   - Mitigation: typed monotonic IDs per node kind, allocated centrally.
2. Risk: behavior drift in PPX rewrite code.
   - Mitigation: parity script and targeted fixture checks after each migration chunk.
3. Risk: large mechanical churn and borrow-checker fallout.
   - Mitigation: phase-by-phase migration with helper constructors and narrow diffs.
4. Risk: hidden dependency on location-based pending behavior.
   - Mitigation: explicit inventory of stash call sites, then zero-match enforcement.

---

## Definition of Done

All must be true:

1. Parser AST no longer stores inline attributes in any node shape listed in inventory.
2. `stash_*` and `pending_*` infrastructure is removed (not just unused).
3. All sparse/attribute writes happen by owner index/ID at construction.
4. `scripts/test_parser_ast_parity.sh` reports full success.
5. Benchmark command above runs successfully without panic.

