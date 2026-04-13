# Import.res Typechecking Performance Handoff

## Problem

`tests/tests/src/Import.res` compiles in roughly:

- OCaml: about `70ms`
- Rust: about `8.7s`

on the same exact `.ast` input and compiler arguments.

This is not a JS printer/backend cost. The output diff is small. The time is
going into the Rust typechecker.

## Repro

Get the exact compiler args:

```bash
cd tests/tests
../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/Import.res
```

Then compile from `tests/tests/lib/bs`:

```bash
ARGS=(
  -I ../ocaml
  -runtime-path /Users/jake/dev/workspaces/rescript-rust/parity-stamp/node_modules/@rescript/runtime
  -w -3-6-26-27-29-30-32..40-44-45-52-60-9-106+104
  -warn-error A
  -bs-package-name rescript-tests
  -bs-package-output esmodule:src:.mjs
  src/Import.ast
)

/usr/bin/time -lp ../../../../_build/install/default/bin/bsc "${ARGS[@]}" -o /tmp/Import.ocaml.mjs
/usr/bin/time -lp ../../../../compiler-rust/target/release/bsc "${ARGS[@]}" -o /tmp/Import.rust.mjs
```

Observed on this machine:

- OCaml: `real 0.07`
- Rust: `real 8.69`
- Rust peak footprint: about `5.7GB`

## Why Import.res Is A Good Stress Test

[Import.res](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/tests/tests/src/Import.res:1) heavily exercises:

- `module type of Belt.List`
- repeated `module M = await Belt.List`
- repeated constrained awaited modules like `await (Belt.List: BeltList)`
- nested modules and nested awaited module bindings

That pushes exactly the code paths that resolve module signatures, qualify them
for an access path, and then look up value/type/module members through them.

## What The Profiler Showed

Sampling the Rust compiler during `Import.res` shows the hot path is in typing:

- `typemod::type_structure`
- `typecore::type_let_bindings`
- `typecore::type_letmodule`
- `typemod::lookup_module_type_from_unpack_expr`
- `typemod::wrap_constraint_with_decl_mty`
- `includemod::modtypes_inner`
- `ctype::unify`
- `ctype::expand_head`
- `ctype::resolve_type_item_through_env`
- `typecore::copy_lookup_signature_for_subst`
- `typecore::copy_lookup_type_expr`

String-counting the sample report gave:

- `copy_lookup_signature_for_subst`: `441`
- `copy_lookup_type_expr`: `3467`
- `resolve_type_item_through_env`: `699`
- `lookup_module_type_from_unpack_expr`: `4`

That is the key result:

- there is some re-typing of unpack payload expressions
- but the dominant cost is repeated deep-copy of module signatures and type
  graphs during module inclusion / type lookup

## Root Cause

Rust is much more eager than OCaml about materializing path-qualified module
signatures.

The current Rust code repeatedly does this:

1. resolve a module type to a signature
2. deep-copy the entire signature
3. deep-copy all nested type expressions
4. rewrite paths in the copied signature
5. search one type or one member inside that fresh copy
6. throw the copy away

The central deep-copy path is:

- [copy_lookup_type_expr](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:14601)
- [copy_lookup_signature_for_subst](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:15169)

Two especially expensive consumers are:

- [resolve_module_signature_for_path](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:18761)
- [resolve_type_item_through_env](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1387)

`resolve_type_item_through_env` is particularly bad because it bypasses the more
useful path-based cache and does:

1. `resolve_module_type_through_env_path`
2. `resolve_signature_through_env_module_type`
3. `copy_lookup_signature_for_subst`
4. `substitute_type_paths_in_sig`
5. linear search for one `SigType`

See:

- [resolve_module_type_through_env_path](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1009)
- [resolve_signature_through_env_module_type](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1146)
- [resolve_type_item_through_env](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1387)

That means Rust keeps cloning the same `Belt.*` signatures just to answer type
expansion and inclusion queries.

## Why OCaml Is Fast

OCaml does not rebuild these access-path-qualified views from scratch on every
lookup.

The important pieces are:

- persistent signatures are renamed lazily once:
  [env.ml `ps_sig = lazy (Subst.signature Subst.identity sign)`](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/env.ml:677)
- prefixed signature path maps are cached:
  [env.ml `prefix_idents` and `prefixed_sg`](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/env.ml:1454)
- module components are built lazily from `(env, sub, path, mty)`:
  [env.ml `components_of_module_maker`](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/env.ml:1516)
- substitution preserves sharing through `Tsubst` / memoized copy:
  [subst.ml `typexp`](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/subst.ml:129)
- non-dependent type rewriting also preserves sharing through hash tables:
  [ctype.ml `nondep_type_rec`](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/ctype.ml:4307)

The important point is not just "OCaml caches":

- it caches the right abstraction
- it operates on lazy component views
- it preserves type-node sharing during substitution

Rust currently has some caches, but they are not aligned with that structure
well enough. The expensive env/type-expansion path still falls back to fresh
whole-signature copies.

## Existing Rust Cache That Helps, But Not Enough

Rust already has:

- [PersistentEnv::get_renamed_sig](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/cmi/persistent_env.rs:469)
- [TypeContext::resolved_module_sig_cache](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/context.rs:186)
- [path_cache_key](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:18748)

But the hot `ctype` path does not consistently reuse the path-qualified cache.
Instead it keeps re-resolving module types, then re-copying signatures.

## The Fix Direction

The fix should make Rust much closer to OCaml's `components_of_module_maker`
model.

The right target is:

- resolve and rename a module signature once
- build a path-qualified view lazily once per access path
- answer repeated value/type/module lookups from that cached qualified view
- avoid deep-copying the full signature on every individual lookup

The performance target is not "better than today." It is "at least as good as
OCaml." A solution that is still materially slower than OCaml is not done.

## Concrete Plan

### 1. Introduce A Single Qualified-Module-Signature Pipeline

Right now there are multiple partially overlapping ways to get a module
signature:

- `Env::resolve_module_lid_impl`
- `resolve_module_signature_for_path`
- `resolve_module_type_through_env_path`
- `resolve_signature_through_env_module_type`

They should converge on one helper that does:

1. start from an access path like `Belt.List` or local `M`
2. resolve the underlying module/module-type once
3. apply alias following / strengthening / parent-child substitution once
4. cache the final qualified signature by access path

That helper should own the expensive path rewriting.

Do not let `ctype` build its own throwaway copies outside this pipeline.

### 2. Make `resolve_type_item_through_env` Use The Qualified-Signature Cache

This is the first high-value change.

Current behavior in
[resolve_type_item_through_env](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1387):

- resolve module type
- resolve raw signature
- deep-copy signature
- rewrite it
- search for one type

That should change to:

1. ask for the already-qualified signature for `module_path`
2. search that cached signature
3. only clone the specific declaration if needed by the caller

This one change should remove a large fraction of the `copy_lookup_signature_for_subst`
traffic seen in the profile.

### 3. Cache Qualified Signatures By Access Path, Not Just Module Name

The cache key must include the access path semantics, not just the underlying
module name.

Examples:

- `Belt.List`
- local alias `M`
- nested alias path `N.N1.O`
- opened/local modules with different local stamps

The current `path_cache_key` helper in
[typecore.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:18748)
is a reasonable starting point.

The critical rule is:

- different access paths that imply different rewritten internal type paths
  cannot share the same qualified signature entry

But repeated lookups of the same access path absolutely should.

### 4. Cache The Fully Qualified View, Not Just The Raw Signature

Caching only the raw signature is not enough. The expensive work is mostly in:

- `copy_lookup_signature_for_subst`
- `substitute_type_paths_in_sig`
- child-signature substitution
- alias prefix rewriting
- strengthening

The cache entry should be the final path-qualified signature, after those
transformations.

That is the closest analogue to OCaml's cached prefixed/components view.

### 5. Stop Deep-Copying Whole Signatures For Single-Type Expansion

`resolve_type_item_through_env` is often called because type expansion wants one
type declaration from a module path.

It should not require cloning the entire enclosing signature graph.

There are two acceptable directions:

- preferred: query the cached qualified signature and then take the one
  `SigType` item needed
- stronger OCaml-like direction: build cached component tables for values,
  types, modules, and modtypes, like `components_of_module_maker`

If the second path is chosen, model it explicitly on OCaml:

- a qualified module view owns:
  - `comp_values`
  - `comp_types`
  - `comp_modules`
  - `comp_modtypes`
  - runtime-slot accounting where needed

That avoids repeated linear scans too.

### 6. Reuse Sharing During Substitution Instead Of Starting Fresh Each Time

Every top-level call to
[copy_lookup_signature_for_subst](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:15169)
creates a fresh `HashMap<TypeExprRef, TypeExprRef>`.

That preserves sharing only inside one copy operation, not across repeated
lookups of the same signature.

The fix is not to globally reuse mutable type nodes. That would be dangerous.
The fix is to reuse the already-built qualified signature/components object so
its copied type graph is shared by all later lookups through that same access
path.

This matches the OCaml shape much better than repeatedly rebuilding the copied
graph.

### 7. Unify The `typecore` And `ctype` Lookup Paths

Right now:

- `typecore.rs` has one path-qualified signature helper:
  [resolve_module_signature_for_path](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:18761)
- `ctype.rs` has another env-only resolution path:
  [resolve_module_type_through_env_path](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1009)

That split is a major source of duplicate work.

The agent working on this should aim to make `ctype` consume the same qualified
module-resolution service used by `typecore`, or extract both into one shared
module.

As long as they stay separate, one path will keep bypassing the other's cache.

### 8. Only After That, Clean Up The Smaller `Pmod_unpack` Retyping Cost

[lookup_module_type_from_unpack_expr](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typemod.rs:4821)
calls `type_expression` again just to recover the package type from an unpack
payload.

That is real work, but it is not the main cliff.

After the signature-copy problem is fixed, this smaller inefficiency can be
cleaned up by:

- caching the semantic module type for `Pmod_unpack`
- or threading the already-typed payload expression/module type through the
  caller instead of retyping the parser expression

Do not start here. It is not the main reason for the 8.7s compile time.

## Suggested Implementation Order

### Phase A: First Structural Win

1. Add a shared helper that returns a cached qualified signature for an access path.
2. Move `resolve_type_item_through_env` onto it.
3. Move `resolve_signature_through_env_module_type` callers onto it where possible.
4. Re-measure `Import.res`.

If this is implemented correctly, `Import.res` should drop by orders of
magnitude and memory should stop exploding into multi-GB.

### Phase B: OCaml-Shaped Lazy Components Layer

If Phase A still leaves Rust slower than OCaml:

1. add a proper cached "module components" structure
2. populate it lazily from `(env, path, mty)` like OCaml
3. store type/value/module/modtype lookup tables there
4. have env/type-expansion logic query components instead of scanning signatures

This is the proper fix direction. Prefer it over piling up local memoization
layers that still do not match OCaml's lazy structure.

## What Not To Do

- Do not add ad hoc special cases for `Import.res` or `Belt.List`.
- Do not cache only by module name when access path matters.
- Do not mutate shared original signatures in place.
- Do not solve this by weakening type expansion or skipping substitutions.
- Do not start by optimizing `lookup_module_type_from_unpack_expr`; it is not
  the dominant cost.

## Expected Acceptance Signals

After the right fix:

- `Import.res` should no longer allocate multi-GB
- `Import.res` should match or beat OCaml on the same machine, allowing only
  normal timing noise
- sample output should stop being dominated by
  `copy_lookup_signature_for_subst` / `copy_lookup_type_expr`
- the remaining top stacks, if any, should be regular type inclusion/unify
  work, not repeated whole-signature rebuilding

## Fast Validation Loop

Use:

```bash
cd tests/tests
../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/Import.res
```

Then from `tests/tests/lib/bs`:

```bash
timeout 20 ../../../../compiler-rust/target/release/bsc <args...> -o /tmp/Import.rust.mjs
```

and:

```bash
/usr/bin/time -lp ../../../../compiler-rust/target/release/bsc <args...> -o /tmp/Import.rust.mjs
```

If needed, sample the process again:

```bash
/usr/bin/sample <pid> 3 -file /tmp/import.sample.txt
```

## Best First Code To Read

Rust:

- [compiler-rust/src/types/typecore.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:14601)
- [compiler-rust/src/types/typecore.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:15169)
- [compiler-rust/src/types/typecore.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/typecore.rs:18761)
- [compiler-rust/src/types/ctype.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1009)
- [compiler-rust/src/types/ctype.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1146)
- [compiler-rust/src/types/ctype.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/ctype.rs:1387)
- [compiler-rust/src/types/context.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/types/context.rs:186)
- [compiler-rust/src/cmi/persistent_env.rs](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler-rust/src/cmi/persistent_env.rs:469)

OCaml:

- [compiler/ml/env.ml](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/env.ml:1454)
- [compiler/ml/env.ml](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/env.ml:1516)
- [compiler/ml/env.ml](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/env.ml:677)
- [compiler/ml/subst.ml](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/subst.ml:129)
- [compiler/ml/ctype.ml](/Users/jake/dev/workspaces/rescript-rust/parity-stamp/compiler/ml/ctype.ml:4307)

## Bottom Line

The performance cliff is not "Rust is slower than OCaml."

It is:

- OCaml builds and caches lazy path-qualified module views
- Rust repeatedly rebuilds fresh path-qualified whole-signature copies

Make Rust reuse a cached qualified module view for repeated lookups, and this
file should get dramatically faster.
