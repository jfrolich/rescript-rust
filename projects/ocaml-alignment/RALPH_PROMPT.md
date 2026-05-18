# Ralph Loop: OCaml Alignment

You are working on `projects/ocaml-alignment`.

## Mission

Make Rust typechecker and module-environment behavior a direct port of the OCaml
compiler, excluding intentional in-process and performance differences.

This is a correctness project, not a local parity-score project. If OCaml uses a
lazy thunk, a substitution table, a definition-level boundary, or a specific
state-restore point, Rust should model that mechanism directly.

## Required Reading

Before editing Rust for a task, read the relevant OCaml source:

- `compiler/ml/env.ml`
- `compiler/ml/subst.ml`
- `compiler/ml/ctype.ml`
- `compiler/ml/typecore.ml`
- `compiler/ml/typemod.ml`
- `compiler/ml/typedecl.ml`
- `compiler/ml/mtype.ml`
- `compiler/ml/includemod.ml`
- `compiler/ext/ident.ml`

Then inspect the Rust implementation files named in
[RALPH_TODO.md](./RALPH_TODO.md).

## Working Rules

1. Open [RALPH_TODO.md](./RALPH_TODO.md).
2. Pick one unchecked top-level task, preferably the highest-impact one.
3. Read OCaml first and record exact functions/line ranges.
4. Implement a Rust change that follows the OCaml mechanism.
5. Do not add string/path-spelling heuristics, output-mode branches, or
   serializer normalizations.
6. Run focused checks, then full relevant parity gates.
7. Update [PROGRESS.md](./PROGRESS.md) and check off completed TODOs only with
   evidence.
8. Commit atomically and stop.

## Non-Negotiable Constraints

- Do not revert verified OCaml-aligned changes because they regress a local
  metric.
- Do not use Rust-only force suppression or alias equivalence to improve parity.
- Do not move on to another root-cause area in the same session.
- Do not edit generated JS artifacts as part of this project.
- Do not modify serializer output to hide typechecker sharing differences.

## Exit Condition

Output `OCAML_ALIGNMENT_COMPLETE` only when:

- every TODO item is checked or explicitly transferred to another accepted
  project
- typedtree parity is green
- lambda parity is green for touched layers
- every remaining Rust/OCaml difference in this area is intentional and
  documented

