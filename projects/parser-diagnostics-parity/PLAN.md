# Parser Diagnostics Parity Plan

## Goal

Achieve **diagnostic parity** between OCaml parser tooling and Rust parser tooling:

1. Same warnings and syntax-error coverage
2. Same error-recovery reporting behavior (count/order/locations)
3. Same diagnostic text and formatting (including code-frame highlights)
4. No Rust parser panics while printing diagnostics

This project is separate from binary AST parity. It covers user-facing parser diagnostics.

## Scope

### In scope

- `res_parser` vs `res_parser_rust` diagnostic output (`-print ml`, warning paths)
- Parser-path diagnostics surfaced via `bsc` parser frontend
- JSX/PPX parser warnings and parser-time errors
- Diagnostic renderer parity (warning header, colors, highlighted span, code-frame)
- External corpus validation (`TELLA_DIR` when available)

### Out of scope

- Type-checker errors (non-parser stage)
- Byte-level `-bs-ast` output parity (tracked elsewhere)
- Printer roundtrip formatting parity (tracked elsewhere)

## Source Inventory Baseline (OCaml)

Static scan completed on **February 10, 2026**.

- Canonical parser diagnostic categories are defined in
  `compiler/syntax/src/res_diagnostics.ml` (`Unexpected`, `Expected`, `Message`, `Uident`, `Lident`, `UnclosedString`, `UnclosedTemplate`, `UnclosedComment`, `UnknownUchar`).
- Scanner lexical diagnostics are emitted in `compiler/syntax/src/res_scanner.ml`.
- Parser grammar diagnostics are emitted via `Parser.err` + `Diagnostics.*` in `compiler/syntax/src/res_core.ml`.
- JSX parser warning surface has one explicit warning emission site in
  `compiler/syntax/src/jsx_v4.ml` (`Location.prerr_warning`, Warning 22 path).
- Warning/error formatting surface is in `compiler/ml/location.ml` (warning intro, color tags, code-frame highlighting).

Detailed inventory: `projects/parser-diagnostics-parity/INVENTORY.md`.

## Runtime Baseline (Current Gaps)

Latest external-corpus scan baseline (February 10, 2026):

- In-repo syntax corpus diagnostics parity: **507/507 match**
- TELLA corpus diagnostics parity: **2310/2320 match**
- Remaining mismatches: **10 files**
  - message text mismatch class (example: JSX tag-name message wording)
  - extra/recovery diagnostic count mismatch class (example: spice parser file)
  - Rust panic in diagnostic code-frame rendering on binary-like UTF-8-invalid input class (`code_frame.rs` char-boundary panic)

Representative files:

- `.../validate.res`: message text mismatch (`A jsx name must...` vs `Expected JSX tag name`)
- `.../Spice.res`: extra Rust syntax diagnostic at same recovery region
- `.../metaZones.res`: Rust panic while rendering diagnostics

## Plan

## Phase 0: Lock Coverage Surface

1. Keep `INVENTORY.md` authoritative and source-linked.
2. Add/maintain fixture buckets by diagnostic class:
   - parser warnings (existing snapshot tests)
   - parser syntax errors
   - parser recovery multi-error sequences
   - crash-hardening pathological inputs
3. Ensure `scripts/test_parser_ast_parity.sh` reports parser diagnostics metrics as parser parity, not binary AST parity.

Exit criteria:

- Every OCaml parser diagnostic emitter has at least one mapped test fixture.

## Phase 1: Crash-Hardening in Rust Diagnostics

1. Fix diagnostic rendering paths to never panic on non-UTF8 boundary slicing.
2. Keep location formatting behavior equivalent to OCaml when source text is malformed/binary-like.
3. Add regression fixtures for panic-inducing files or reduced reproductions.

Exit criteria:

- No panic for known pathological TELLA files.
- Parser exits cleanly with diagnostics instead of aborting.

## Phase 2: Warning Surface Parity

1. Verify warning 22 emission conditions match OCaml exactly.
2. Verify warning header text, numbering, coloring, and highlighted expression range.
3. Snapshot-test warning output from both parsers and expected baseline.

Exit criteria:

- Warning fixtures pass with exact textual parity.

## Phase 3: Error Text + Recovery Parity

1. Align message wording for all parser-time diagnostics (including JSX-specific text).
2. Align recovery behavior so both parsers emit same error count/order/locations for same input.
3. Fix known mismatch clusters (`@spice` parser files, router test file, large invalid corpus files).

Exit criteria:

- Zero mismatches in in-repo parser diagnostic corpus.
- Zero mismatches in TELLA corpus except explicitly OCaml-failing out-of-scope files.

## Phase 4: Structural Regression Guardrails

1. Add script mode that compares diagnostics-only output independently from AST parity.
2. Add CI-friendly summary counters:
   - warning snapshot diffs
   - syntax-error output diffs
   - panic count
3. Preserve append-only baseline behavior for non-regression.

Exit criteria:

- Diagnostics parity regressions are surfaced as first-class failures.

## Acceptance Criteria

All of the following must hold:

1. No Rust parser diagnostic panics on covered corpora.
2. Warning fixtures: exact parity (`warning number`, message body, highlight/code-frame shape).
3. Error fixtures: exact parity (`Syntax error!` sections, count/order/location/message).
4. External corpus scan reports zero Rust-only diagnostic divergences for in-scope files.
5. Any remaining exclusions are documented with explicit file list + reason.

