# OCaml Alignment TODO

## Goal

Align Rust typechecker/module-environment behavior with the OCaml compiler,
excluding intentional in-process and performance differences.

The standard for completion is OCaml algorithmic parity: same lookup API
boundary, same lazy force point, same substitution scope, same freshening order,
same type graph sharing behavior, and same definition-level transitions.

## Instructions For Agents

1. Pick one unchecked top-level task.
2. Read the OCaml reference files listed for that task before editing Rust.
3. Write down the exact OCaml functions and line ranges used.
4. Implement the Rust change as a translation of the OCaml behavior.
5. Run focused tests first, then full parity gates as appropriate.
6. Update this TODO or [PROGRESS.md](./PROGRESS.md) with evidence.
7. Commit the change atomically and stop.

Do not start with easy one-off diffs. The remaining work is architectural.

## P0 Checklist

### 1. Finish the lazy Env component port

Files:

- `compiler-rust/src/types/env_lazy.rs`
- `compiler-rust/src/types/env.rs`
- `compiler-rust/src/types/typecore.rs`
- OCaml: `compiler/ml/env.ml`, especially `EnvLazy`,
  `components_of_module_maker`, `find_module_descr`, `find_module`,
  `add_components`

Tasks:

- [x] Audit `StoredModuleComponents::with_components` against
      `env.ml:components_of_module_maker`.
- [x] Replace Rust-specific parent/sibling/alias reconstruction with direct
      OCaml-shaped thunk arguments where possible.
- [x] Ensure child `comp_modules` and `comp_components` share the same forced
      thunks as OCaml.
- [x] Ensure component module declarations are forced exactly where OCaml calls
      `EnvLazy.force subst_modtype_maker`.
- [x] Keep module signature freshening and stamp consumption at the OCaml force
      point, not earlier.

Acceptance:

- The implementation can be explained as a direct Rust port of
  `components_of_module_maker`, not as post-hoc cache repair.

### 2. Audit and reduce `ComponentLookupCacheMode`

Files:

- `compiler-rust/src/types/typecore.rs`
- `compiler-rust/src/types/env_lazy.rs`
- OCaml: `compiler/ml/env.ml`

Tasks:

- [x] Inventory every `ComponentLookupCacheMode::FindModule` call site.
- [x] Inventory every `ComponentLookupCacheMode::ProbeModuleDescr` call site.
- [x] Map each call site to the exact OCaml API: `find_module`,
      `find_module_descr`, `find_type`, `find_modtype`, or component lookup.
- [x] Rename or split Rust APIs so the force behavior follows the API boundary
      rather than a generic mode flag.
- [x] Remove any mode usage that exists only to preserve a local parity score.

Acceptance:

- Each mode boundary has a one-line OCaml source citation.

### 3. Remove flattened-alias side-channel dependence

Files:

- `compiler-rust/src/types/context.rs`
- `compiler-rust/src/types/env_lazy.rs`
- `compiler-rust/src/types/typecore.rs`
- `compiler-rust/src/types/typemod.rs`
- OCaml: `compiler/ml/env.ml`, `compiler/ml/subst.ml`

Tasks:

- [x] Inventory `flattened_alias_component_paths` producers and consumers.
- [x] Replace path-spelling alias facts with data produced by alias scraping,
      substitution, and shared component thunks.
- [x] Remove fallback success based on flattened/unflattened spelling when
      declaration lookup fails.
- [x] Add tests that prove alias identity comes from declarations, not names.

Acceptance:

- Flattened module naming can affect file lookup, but not semantic alias
  identity by string equivalence.

### 4. Eliminate signature-content inference paths

Files:

- `compiler-rust/src/types/typecore.rs`
- OCaml: `compiler/ml/typecore.ml`, `compiler/ml/env.ml`

Tasks:

- [x] Find helpers that scan signatures to infer/rebind type-family paths.
- [x] Find branches based on shape guesses such as "only values" or
      self-manifest signatures.
- [x] Replace those branches with the same lookup/substitution path OCaml uses.
- [x] Remove output-mode or observed-diff guards that change typechecker
      semantics.

Acceptance:

- Forcing is driven by lookups and normalization, not by scanning a signature and
  deciding what it probably means.

### 5. Align abbreviation expansion caching with `ctype.ml`

Files:

- `compiler-rust/src/types/ctype.rs`
- OCaml: `compiler/ml/ctype.ml`

Tasks:

- [x] Audit Rust expansion caches against OCaml `simple_abbrevs`,
      `proper_abbrevs`, and `check_abbrev_env`.
- [x] Verify cache lifetime across environment changes.
- [x] Verify cache effects on allocation, sharing, and force order.
- [x] Add focused tests for repeated expansion through changing module envs.

Acceptance:

- Abbreviation expansion and cache invalidation are explainable through OCaml's
  `ctype.ml`, not through Rust-specific memoization.

### 6. Verify copy / instantiation sharing

Files:

- `compiler-rust/src/types/ctype.rs`
- `compiler-rust/src/types/type_expr.rs`
- OCaml: `compiler/ml/ctype.ml`, `compiler/ml/btype.ml`

Tasks:

- [ ] Audit `instance`, `copy`, and generic/non-generic sharing behavior.
- [ ] Verify temporary `Tsubst`-style behavior or its Rust equivalent.
- [ ] Verify row-copy behavior, including polymorphic variants and object rows.
- [ ] Verify when non-generic nodes are shared versus copied.

Acceptance:

- Typedtree sexp identity/cycle behavior follows from OCaml-equivalent type node
  sharing, not serializer normalization.

### 7. Tighten pattern backtracking and GADT state restoration

Files:

- `compiler-rust/src/types/typecore.rs`
- OCaml: `compiler/ml/typecore.ml`, `compiler/ml/parmatch.ml`,
  `compiler/ml/ctype.ml`

Tasks:

- [ ] Audit or-pattern splitting state snapshots.
- [ ] Audit GADT constraint introduction and restoration.
- [ ] Audit Parmatch retry/backtracking restore points.
- [ ] Ensure type graph, levels, delayed forces, and Env state are restored at
      the same points as OCaml.

Acceptance:

- Equivalent final types are not enough; intermediate mutation and restore order
  must match OCaml.

### 8. Audit let/match definition-level boundaries

Files:

- `compiler-rust/src/types/typecore.rs`
- OCaml: `compiler/ml/typecore.ml`, `compiler/ml/ctype.ml`

Tasks:

- [ ] Trace let-binding order: pattern typing, delayed forces, expression
      typing, partiality, close level, value restriction, generalization.
- [ ] Trace match/case order and definition levels.
- [ ] Verify local abstract type and existential handling around patterns.
- [ ] Add focused tests for ordering-sensitive sharing and diagnostics.

Acceptance:

- The ordering of definition-level changes and generalization matches OCaml.

### 9. Bring type declaration group handling closer to `typedecl.ml`

Files:

- `compiler-rust/src/types/typedecl.rs` if present
- `compiler-rust/src/types/typemod.rs`
- OCaml: `compiler/ml/typedecl.ml`, `compiler/ml/typemod.ml`

Tasks:

- [ ] Audit recursive stubs and declaration-group environment staging.
- [ ] Audit fixed private rows.
- [ ] Audit variance and immediacy fixpoints.
- [ ] Audit constraint timing and extension constructors.
- [ ] Split Rust code toward a dedicated `typedecl.rs` shape if that better
      mirrors OCaml.

Acceptance:

- Type declaration group checking follows `typedecl.ml` phases and environment
  staging.

### 10. Re-check module type algorithms against `mtype.ml` / `includemod.ml`

Files:

- `compiler-rust/src/types/typemod.rs`
- `compiler-rust/src/types/mtype.rs` if present
- `compiler-rust/src/types/includemod.rs`
- OCaml: `compiler/ml/mtype.ml`, `compiler/ml/includemod.ml`

Tasks:

- [ ] Audit strengthening.
- [ ] Audit `nondep_supertype`.
- [ ] Audit alias removal.
- [ ] Audit `lower_nongen`.
- [ ] Audit inclusion substitutions and runtime coercion positions.
- [ ] Remove path-spelling repair code when the algorithm should produce the
      right path directly.

Acceptance:

- Module type behavior produces correct paths and coercions through OCaml's
  algorithms, not later repair helpers.

## Validation Gates

Use these gates after any semantic change in this project:

```bash
cargo build --release --manifest-path compiler-rust/Cargo.toml
cargo build --release --manifest-path rewatch/Cargo.toml
./scripts/test_typedtree_parity.sh --release
./scripts/test_lambda_parity.sh --release
```

For authoritative typedtree runs, clear parity cache files first as described in
the root `AGENTS.md`.
