# Verification (proposed)

Three proposals that let a ReScript program state what must hold and have
tools check it. They build on each other, and each is useful alone.

| RFC | Adds | Checked |
| --- | --- | --- |
| [Purity](pure.md) | `@pure`, `@mutates` | by the compiler, in every build |
| [Laws](law.md) | `@law`, `rescript verify` | by running each law on generated values: all of them, or a thousand |
| [Proofs](proof.md) | `@law(proved)`; no new syntax for a proof | by the compiler in `rescript verify`: cases, induction, earlier laws |
| [Specs](spec.md) | `@spec`, `Spec.t` | by going through every state a reducer can get into |

The idea they share: the program says what must hold in ReScript itself, next
to the code, and the build reports how strongly each statement was checked.
Nothing here adds a proof language, a solver or a new kind of type.

All of them are implemented in the Rust compiler only. The OCaml compiler
ignores the attributes.
