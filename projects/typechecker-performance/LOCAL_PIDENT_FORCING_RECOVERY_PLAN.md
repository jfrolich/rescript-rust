# Local Pident EnvLazy Forcing Recovery Plan

## Problem

The current local-`Pident` env-lazy rollout memoizes the wrong thing.

Rust currently stores a lazy wrapper for local module bindings, but forcing that
wrapper builds a fully qualified signature via the eager
`build_qualified_signature_for_access_path` path. That changes forcing order,
sharing, and stamp allocation compared with OCaml's
`Env.components_of_module_maker`.

The parity regressions seen in the import-family files are consistent with this:

- earlier local `Pident` module forcing
- different identifier/stamp allocation order
- different sharing boundaries for child modules and nested type declarations

## Reference Behavior

OCaml:

- stores a lazy module descriptor in `env.modules`
- stores a lazy components thunk in `env.components`
- forces `components_of_module_maker (env, sub, path, mty)` only when callers
  ask for components
- inside that force:
  - computes `prefix_idents` once
  - iterates the raw signature left-to-right
  - extends a local env as each item is processed
  - records separate entries for child modules vs child components
  - does not force child components just to observe a child module binding

Rust must match that shape for local `Pident` paths.

## Current Risky Rust Path

- `Env::add_module` stores `StoredModuleComponents`
- `StoredModuleComponents::with_components` forces by calling
  `build_qualified_module_components_for_access_path`
- that path resolves, rewrites, substitutes, and generalizes the whole
  signature before any specific lookup needs it
- `with_resolved_module_components_for_path` consults this local cache first for
  `Pident` paths

This is the wrong forcing boundary.

## Recovery Strategy

### Phase 1: Return To Last Parity-Safe Forcing Model

1. Remove the local `Pident` fast path that consults `Env::module_components`
   from `with_resolved_module_components_for_path`.
2. Remove the temporary local `StoredModuleComponents` storage from `Env`.
3. Keep the parity-safe dotted/persistent env-lazy work that already improved
   performance without worsening typedtree parity.
4. Re-run focused import parity and full typedtree parity to confirm we are
   back at the last safe checkpoint.

### Phase 2: Add Force-Order Instrumentation

Before rebuilding the local path, add temporary tracing for:

- Rust `Env::add_module`
- Rust local component force entrypoints
- Rust `resolve_letmodule_direct_type_family_root`
- Rust `typemod` local `Pident` module-signature scraping
- OCaml `get_components`
- OCaml `components_of_module_maker`

Target files:

- `Import.res`
- `ImportAttributes.res`
- `DynamicImportModuleWithAlias.res`
- `stdlib/Stdlib_ImportTests.res`

Goal:

- find the first place where Rust forces a local module/components thunk earlier
  than OCaml

### Phase 3: Implement An OCaml-Shaped Local Components Builder

Replace the current local thunk body with a real component builder.

It must:

1. take `(env, sub, path, mty)` as the lazy payload
2. call an equivalent of `prefix_idents` once
3. iterate the raw signature left-to-right
4. extend a local env as each type/module/modtype is processed
5. populate component tables incrementally
6. keep module declarations separate from child component thunks
7. avoid forcing child components unless the caller actually asks for them

### Phase 4: Reintroduce Local Pident Consumers Incrementally

Re-enable local env-lazy consumers one at a time:

1. read-only local type lookup
2. `resolve_letmodule_direct_type_family_root`
3. `typemod` local signature scraping

Do not reroute broad inclusion paths until parity stays stable.

## Hard Requirements

- no eager whole-signature qualification for local `Pident` forcing
- no child-component forcing when only child module presence/path is needed
- preserve left-to-right env mutation during one component build
- preserve OCaml-style runtime position accounting
- preserve typedtree parity before keeping a performance win

## Validation

Required after each phase:

```bash
./scripts/test_typedtree_parity.sh Import
./scripts/test_typedtree_parity.sh
```

Then performance checks:

```bash
python3 scripts/benchmark_typechecker_performance.py Import.res
python3 scripts/benchmark_typechecker_performance.py --warmup 0 --runs 1 --limit 40
```

## First Concrete Step

Back out the current local-`Pident` env-lazy shortcut and confirm parity
returns to the prior checkpoint before implementing the OCaml-shaped builder.
