# Raw-signature storage schedule

`cmi::portable_types::identity_tests::gentype_alias_declarations_ignore_storage_schedule`
compiles these sources through `compile_source_in_process`, with a `Schedule`
namespace registered through `ModuleRegistry`. There are no interfaces. Only
`Output` is annotated. `Dependency.u` referring to `Dependency.t` is essential:
a record containing only a primitive does not expose the bug.

## Cause

`PortablePersStruct::decoded` retains a shared main signature and a raw
signature. `encoded()` fills the encoded `OnceLock` for storage and releases
the raw graph under the decoded mutex. Previously, it replaced the raw graph
with `None`, the same representation used for a genuinely absent raw signature.
Both `has_raw_signature()` and `raw_signature()` inspect the encoded slot
*before* acquiring that mutex. Storage can run between those two operations.
The reader then interprets the released raw graph as absent, even though its
bytes are available (or being published).

`internalize_pers_struct` uses `has_raw_signature` to populate the current
`TypeContext`'s `gentype_portable_raw_module_sigs`. Later,
`persistent_alias_module_type` first asks `get_gentype_raw_module_sig` and then
falls back to the component signature. The race either prevents registration
or loses the raw read itself. Component signatures have namespace-qualified
paths; raw signatures retain local type references. Thus alias translation
adds different identifiers/imports to the stored declarations. This is a
publication-state race, not hash ordering or the declaration registry's order.

The test-only schedule point invokes storage on another thread after the
encoded-slot check and before taking the decoded lock. Both presence and
payload reads are tested, and the unforced order supplies the expected bytes.
No timing, repeated parallel build, or production environment flag is used.

## Correct result

The raw-signature variant is correct: the aliased `u` refers to `Alias_t`,
not an import of `Dependency_t`. OCaml's `translate_structure.ml` resolves
`module Alias = Dependency` with `Env.scrape_alias` and translates its signature
as an include. Making that alias annotated in an otherwise identical probe
produces:

```typescript
export type Alias_t = { readonly value: number };
export type Alias_u = { readonly item: Alias_t };
```

The unannotated fixture itself emits only `Output.gen.tsx`, importing `Use_t`;
stored declarations must nevertheless retain the same alias-local references
when another annotated consumer reads them. The output parity suite remains
the reference for generated TypeScript.

## Fix contract

Distinguish `Decoded(None)` (no raw signature was published) from `Encoded`
(storage released it). A reader observing `Encoded` drops the decoded mutex
and reads the already-published bytes, waiting for their publication if needed.
There is no new lock, sorting pass, or eager encoding in the normal genType
read path. The on-disk representation does not change.
