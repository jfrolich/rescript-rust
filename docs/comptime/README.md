# Comptime (proposed)

Compile-time metaprogramming for ReScript, modelled on Zig's `comptime`:
regular ReScript functions that run during compilation, introspect types, and
specialize code. It is meant to replace most PPX use cases.

This is a design proposal. The compiler does not implement it. An early
prototype in the Rust compiler was removed before the first Rust release, so
the feature can be rebuilt on top of the released architecture.

| Document | Contents |
|----------|----------|
| [DESIGN.md](DESIGN.md) | Proposed architecture: goals, `@typeInfo`, execution model, in-process compilation, derive attributes, PPX replacement |
| [EXAMPLES.md](EXAMPLES.md) | Worked examples (JSON codecs, DSL parsing, derive) |
| [BUILDERS.md](BUILDERS.md) | `typeInfo` shape and the record/variant builder builtins |
| [PROTOTYPE_NOTES.md](PROTOTYPE_NOTES.md) | Lessons from the removed prototype (inlining strategy, `@typeInfo` on concrete types, optimizer reuse) |
