# Verification (proposed)

Three proposals that let a ReScript program state what must hold and have
tools check it. They build on each other, and each is useful alone.

| RFC | Adds | Checked |
| --- | --- | --- |
| [Purity](pure.md) | `@pure`, `@mutates` | by the compiler, in every build |

The idea they share: the program says what must hold in ReScript itself, next
to the code, and the build reports how strongly each statement was checked.
Nothing here adds a proof language, a solver or a new kind of type.

All three are implemented in the Rust compiler only. The OCaml compiler
ignores the attributes.
