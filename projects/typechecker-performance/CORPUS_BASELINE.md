# Canonical Corpus Baseline

## Scope

This is the project-wide baseline for the canonical recursive
`tests/tests/src/**/*.res` corpus.

- Canonical source universe: `657` `.res` files
- Parser is excluded by using checked-in `.ast` inputs
- Typechecking and downstream compilation are both included
- The benchmark is authoritative for "Rust must be at least as fast as OCaml"
  on the in-repo corpus

Command:

```bash
python3 scripts/benchmark_typechecker_performance.py --warmup 0 --runs 1 --limit 40
```

Artifacts:

- `.performance-cache/typechecker/latest.csv`
- `.performance-cache/typechecker/latest.json`

## Baseline

Corrected canonical run on 2026-04-13:

- Files tested: `657`
- Comparable files: `657`
- Rust faster or equal: `2`
- Rust slower: `655`
- Materially slower: `252`
- OCaml failures: `0`
- Rust failures: `0`
- Aggregate OCaml total: `6171.5ms`
- Aggregate Rust total: `26467.1ms`
- Aggregate Rust / OCaml ratio: `4.29x`

Files where Rust was not slower:

- `src/and_or_tailcall_test.res`: Rust `10.7ms`, OCaml `10.8ms`
- `src/inner_define.res`: Rust `11.1ms`, OCaml `12.1ms`

The earlier `31` "OCaml failures" were a harness artifact. The benchmark
flattened temp output paths to names like `src_a_recursive_type.res.ocaml.mjs`;
that changes the output basename away from the module stem, and OCaml `bsc`
then fails interface `.cmi` lookup for `.resi`-backed modules. Preserving the
original basename fixes the issue.

## Top Slower Files

- `src/Import.res`: Rust `188.13x` slower (`+8810.5ms`; OCaml `47.1ms`, Rust `8857.5ms`)
- `src/global_module_alias_test.res`: Rust `75.78x` slower (`+1386.4ms`; OCaml `18.5ms`, Rust `1404.9ms`)
- `src/mario_game.res`: Rust `13.27x` slower (`+568.9ms`; OCaml `46.3ms`, Rust `615.2ms`)
- `src/jsx_preserve_test.res`: Rust `11.07x` slower (`+404.2ms`; OCaml `40.1ms`, Rust `444.3ms`)
- `src/bs_poly_set_test.res`: Rust `17.78x` slower (`+270.4ms`; OCaml `16.1ms`, Rust `286.5ms`)
- `src/bs_poly_map_test.res`: Rust `15.69x` slower (`+246.2ms`; OCaml `16.8ms`, Rust `263.0ms`)
- `src/bs_poly_mutable_set_test.res`: Rust `17.32x` slower (`+239.8ms`; OCaml `14.7ms`, Rust `254.5ms`)
- `src/gpr_1150.res`: Rust `25.12x` slower (`+205.7ms`; OCaml `8.5ms`, Rust `214.2ms`)
- `src/bs_mutable_set_test.res`: Rust `12.30x` slower (`+205.7ms`; OCaml `18.2ms`, Rust `223.9ms`)
- `src/belt_list_test.res`: Rust `9.21x` slower (`+201.5ms`; OCaml `24.5ms`, Rust `226.1ms`)
- `src/string_set.res`: Rust `16.21x` slower (`+177.6ms`; OCaml `11.7ms`, Rust `189.3ms`)
- `src/test_include.res`: Rust `21.14x` slower (`+169.7ms`; OCaml `8.4ms`, Rust `178.2ms`)
- `src/module_alias_test.res`: Rust `18.52x` slower (`+169.0ms`; OCaml `9.6ms`, Rust `178.7ms`)
- `src/bs_array_test.res`: Rust `8.05x` slower (`+139.4ms`; OCaml `19.8ms`, Rust `159.2ms`)
- `src/stdlib/intl/Stdlib_Intl_DateTimeFormatTest.res`: Rust `16.85x` slower (`+126.8ms`; OCaml `8.0ms`, Rust `134.8ms`)
- `src/big_polyvar_test.res`: Rust `3.63x` slower (`+122.2ms`; OCaml `46.5ms`, Rust `168.7ms`)
- `src/bs_set_int_test.res`: Rust `9.57x` slower (`+116.6ms`; OCaml `13.6ms`, Rust `130.2ms`)
- `src/bs_map_set_dict_test.res`: Rust `9.69x` slower (`+116.6ms`; OCaml `13.4ms`, Rust `130.0ms`)
- `src/ticker.res`: Rust `9.63x` slower (`+101.2ms`; OCaml `11.7ms`, Rust `112.9ms`)
- `src/belt_sortarray_test.res`: Rust `7.56x` slower (`+83.6ms`; OCaml `12.7ms`, Rust `96.3ms`)
- `src/js_json_test.res`: Rust `5.29x` slower (`+82.9ms`; OCaml `19.3ms`, Rust `102.2ms`)
- `src/js_date_test.res`: Rust `6.36x` slower (`+82.5ms`; OCaml `15.4ms`, Rust `97.9ms`)
- `src/bs_queue_test.res`: Rust `6.66x` slower (`+80.9ms`; OCaml `14.3ms`, Rust `95.2ms`)
- `src/test_set.res`: Rust `6.65x` slower (`+80.8ms`; OCaml `14.3ms`, Rust `95.1ms`)
- `src/stdlib/intl/Stdlib_Intl_NumberFormatTest.res`: Rust `11.46x` slower (`+77.4ms`; OCaml `7.4ms`, Rust `84.8ms`)

The full file-by-file list lives in `latest.csv` and `latest.json`.

## Root-Cause Clusters

### Cluster 1: Module Signature / Alias / Include / `module type of` / `unpack`

Confidence: high.

Representative files:

- `src/Import.res`
- `src/global_module_alias_test.res`
- `src/module_alias_test.res`
- `src/test_include.res`
- `src/bs_poly_set_test.res`
- `src/bs_poly_map_test.res`
- `src/bs_poly_mutable_set_test.res`
- `src/bs_mutable_set_test.res`
- `src/string_set.res`
- `src/belt_list_test.res`
- `src/bs_set_int_test.res`
- `src/bs_map_set_dict_test.res`

Evidence:

- `Import.res` investigation already showed the hot path is repeated
  `copy_lookup_signature_for_subst`, `copy_lookup_type_expr`,
  `resolve_type_item_through_env`, and `resolve_module_signature_for_path`.
- `global_module_alias_test.res` sample still shows the same shape:
  `copy_lookup_signature_for_subst` `217`, `copy_lookup_type_expr` `1383`,
  `resolve_type_item_through_env` `340`.
- `bs_poly_set_test.res` and related Belt tests are structurally similar:
  repeated `Belt.*` module aliases, `Belt.Set.Dict`, `Belt.SortArray`,
  `unpack(Belt.Id.comparable(...))`, and repeated `module(IntCmp)` use.

Fix direction:

1. Port OCaml's lazy module-components model into Rust.
2. Stop doing eager whole-signature deep-copy for repeated member lookups.
3. Cache the fully path-qualified view per access path, not just raw signatures.
4. Make `ctype.rs` and `typecore.rs` share one qualified-resolution path.
5. Preserve sharing inside substituted type expressions instead of materializing
   fresh deep copies for each lookup.

This is the primary root cause. Do this first.

### Cluster 2: JSX / React / DOM Typing Still Hits The Same Signature-Copy Path

Confidence: medium-high.

Representative files:

- `src/jsx_preserve_test.res`
- `src/mario_game.res`
- `src/async_jsx.res`

Evidence:

- `jsx_preserve_test.res` sample still contains
  `copy_lookup_signature_for_subst` `46`, `copy_lookup_type_expr` `136`,
  `resolve_type_item_through_env` `43`.
- `mario_game.res` sample still contains
  `copy_lookup_signature_for_subst` `21`, `copy_lookup_type_expr` `40`,
  `resolve_type_item_through_env` `23`.
- These files also spend time in `type_expect` and `type_application`, so the
  module-view fix is likely necessary but may not be sufficient.

Fix direction:

1. Apply the OCaml lazy module-components fix first.
2. Re-profile JSX-heavy files after that lands.
3. If they remain slow, compare Rust vs OCaml behavior in labeled/optional
   argument typing, React props typing, and object/row-type instantiation.
4. Check whether Rust is over-instantiating expected types or rebuilding prop
   types across repeated JSX nodes.

Do not optimize this cluster before the module-view fix, because the sample
already shows the same root path.

### Cluster 3: Deep Pattern-Matching / Branch Typing

Confidence: medium.

Representative files:

- `src/gpr_1150.res`
- likely other large nested-match files such as `src/ticker.res`

Evidence:

- `gpr_1150.res` is a deeply nested list-pattern switch and does not look like
  a module-alias stress case.
- Its current compile time is still `25.12x` slower than OCaml.
- A short sample did not capture a stable hot symbol because the file compiles
  too quickly for the current sampling setup.

Fix direction:

1. Re-profile this file after Cluster 1 is fixed to see if the gap remains.
2. If it does, compare Rust vs OCaml in deep `type_cases` / pattern typing.
3. Look for repeated reconstruction of identical expected list types across
   nested branches.
4. Check constructor lookup reuse and type-expression sharing in nested pattern
   descent.

This cluster is real, but it should be investigated after the module-view cliff
is removed so the remaining signal is cleaner.

### Cluster 4: Polyvariant / Intl / Rich Object-Typing Files

Confidence: medium.

Representative files:

- `src/stdlib/intl/Stdlib_Intl_DateTimeFormatTest.res`
- `src/stdlib/intl/Stdlib_Intl_NumberFormatTest.res`
- `src/big_polyvar_test.res`
- `src/js_json_test.res`
- `src/js_date_test.res`

Evidence:

- These files are still materially slower even when they are not obvious
  module-alias microbenchmarks.
- They contain rich option-object, row, polyvariant, and JS interop typing.

Fix direction:

1. Re-benchmark after Cluster 1 is fixed.
2. If still slow, compare Rust vs OCaml in row/object/polyvariant expansion and
   instantiation paths.
3. Check whether Rust is creating excess copies while expanding rows or looking
   up fields/labels.

## Required End State

This project is done only when:

- Rust is no slower than OCaml on every comparable file in the canonical corpus
- `Import.res` matches or beats OCaml and no longer allocates multi-GB
- the remaining slower-than-OCaml clusters, if any, are explained and fixed by
  OCaml-shaped changes rather than file-specific bandaids
