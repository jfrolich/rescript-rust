# OCaml Alignment Plan

## Goal

Bring the Rust compiler implementation into closer 1:1 alignment with the OCaml
reference compiler for type checking and module/type environment behavior,
excluding intentional in-process and performance-engineering differences.

The project goal is not to improve parity with compatibility hacks. The target
is to make Rust produce the same behavior because it follows the same OCaml
algorithms, force boundaries, substitution order, sharing model, and definition
level transitions.

## Scope

Primary Rust areas:

- `compiler-rust/src/types/env_lazy.rs`
- `compiler-rust/src/types/env.rs`
- `compiler-rust/src/types/typecore.rs`
- `compiler-rust/src/types/ctype.rs`
- `compiler-rust/src/types/typemod.rs`
- `compiler-rust/src/types/includemod.rs`
- `compiler-rust/src/cmi/persistent_env.rs`

Primary OCaml references:

- `compiler/ml/env.ml`
- `compiler/ml/ctype.ml`
- `compiler/ml/typecore.ml`
- `compiler/ml/typemod.ml`
- `compiler/ml/typedecl.ml`
- `compiler/ml/mtype.ml`
- `compiler/ml/includemod.ml`
- `compiler/ml/subst.ml`
- `compiler/ext/ident.ml`

## Guardrails

- Read OCaml first, then edit Rust.
- Cite exact OCaml source locations in code comments or commit notes for every
  semantic change.
- Do not add Rust-only compatibility layers, output-mode branches, path-spelling
  equivalence, or signature-content guesses to improve local parity.
- Do not revert verified OCaml-aligned changes because they temporarily regress
  a parity score.
- Keep each session to one root-cause area, commit, then stop.
- Run focused parity before full parity when changing typechecker behavior.
- Preserve existing generated-file and dirty-worktree changes that are unrelated
  to the task.

## Top-Level Workstreams

1. Finish the lazy Env component port.
2. Audit and reduce `ComponentLookupCacheMode`.
3. Remove flattened-alias side-channel dependence.
4. Eliminate signature-content inference paths.
5. Align abbreviation expansion caching with `ctype.ml`.
6. Verify copy / instantiation sharing.
7. Tighten pattern backtracking and GADT state restoration.
8. Audit let/match definition-level boundaries.
9. Bring type declaration group handling closer to `typedecl.ml`.
10. Re-check module type algorithms against `mtype.ml` / `includemod.ml`.

The detailed checklist lives in [RALPH_TODO.md](./RALPH_TODO.md).

## Acceptance Criteria

This project is complete only when:

- every checklist item in [RALPH_TODO.md](./RALPH_TODO.md) is either completed
  or explicitly moved to a separate accepted project
- typedtree parity remains green on the canonical tests corpus
- lambda and JS parity gates relevant to changed layers remain green
- all remaining intentional Rust/OCaml differences are documented and are not
  typechecker semantic differences
- known Rust-only lazy/typechecker compensation mechanisms have either been
  removed or justified as exact translations of OCaml API boundaries

