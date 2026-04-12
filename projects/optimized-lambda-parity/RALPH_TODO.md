# Ralph TODO: Optimized Lambda Parity

**Last Updated:** 2026-04-12
**Status:** 632/657 (96.2%), 25 parity failures, 91 hunks

## Goal

Achieve **100% optimized lambda parity** between the Rust compiler and the OCaml reference implementation using:

```bash
./scripts/test_lambda_parity.sh -j1
```

Execution order and phase gates live in `PLAN.md`.

## Current Baseline

Authoritative run:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **632/657**
- Parity hunks: **91**
- Stamp-canonicalized parity: not re-baselined in this rerun
- Stamp-canonicalized hunks: not re-baselined in this rerun
- Largest current exact diffs:
  - `record_extension_test.res`: **11** hunks
  - `exception_raise_test.res`: **11** hunks
  - `js_exception_catch_test.res`: **9** hunks
  - `Stdlib_DictTests.res`: **8** hunks
  - `large_record_duplication_test.res`: **7** hunks
  - `UntaggedVariants.res`: **4** hunks
  - `Stdlib_IntlTests.res`: **4** hunks
  - `Stdlib_TempTests.res`: **4** hunks
  - `inline_const.res`: **4** hunks

## Working Rules

1. **Read the OCaml source first.** Do not invent optimized-lambda behavior from the diff output.
2. **Keep verified OCaml-aligned changes.** Temporary parity regressions are acceptable if the port is correct.
3. **Commit immediately after each verified improvement.** Do not accumulate uncommitted work.
4. **Use hunk count as a navigation signal.** File count alone hides structural progress.
5. **Fix lowering, not the sexp printer.** `sexp_lambda.rs` should reflect produced lambda, not normalize it.
6. **Optimized work is still mostly post-raw.** Keep `-drawlambda` as a guardrail when changing raw-lambda construction; the end-of-session raw rerun below surfaced one residual exact raw failure outside this slice.
7. **Do not confuse `-dlambda-sexp` with later backend passes.** The parity target is the output printed immediately after `Lam_convert.convert`.

## Remaining Parity Failures

There are **25** remaining optimized-lambda failures after this slice. The dominant frontier is still post-raw lowering, but raw construction order and external-call metadata can still move whole control-flow clusters.

Current frontier characteristics:
- `-dlambda-sexp` and `-dlambda-sexp-locs` now route through raw lambda plus `raw_lambda::lower`.
- `raw_lambda/lower.rs` is no longer an identity shim.
- Small structural sanity checks now pass exactly:
  - `AsInUncurriedExternals.res`
  - `DerivingAccessorsCurried.res`
  - `DerivingAccessorsUncurried.res`
  - `DictInternalRepresentation.res`
  - `DictInference.res`
  - `DictPatternMatchingOptimization.res`
  - `DynamicImportModuleWithAlias.res`
  - `ExternalExtension.res`
  - `Import.res`
  - `VariantCoercion.res`
  - `minimal_test.res`
- `conditional/cond_a.res` now also passes exactly as a minimal assert-failure guard.
- `js_array_test.res` now also passes exactly as a large-file guard.
- nullary `CstrUnboxed` constructor metadata is now preserved in raw lambda, which removed the hidden `OnlyOne` constructor-vs-unit mismatch in `UntaggedVariants.res`; that file is now down to **4** hunks, all in the existing static-exit numbering cluster.
- `big_polyvar_test.res` now also passes exactly on the current authoritative baseline.
- `alias_default_value_test.res`, `function_directives.res`, `function_directives_async.res`, `function_directives_no_inline.res`, and `adt_optimize_test.res` now also pass exactly on the current authoritative baseline.
- `js_json_test.res` now also passes exactly on the current authoritative baseline.
- `LetUnwrap.res` now also passes exactly after preserving named polyvariant hash metadata in raw match tests.
- `polyvar_test.res` now also passes exactly on the current authoritative baseline.
- `set_gen.res` now also passes exactly on the current authoritative baseline.
- `ari_regress_test.res`, `big_enum.res`, `equal_test.res`, `reasonReact.res`, and `reasonReactOptimizedCreateClass.res` now also pass exactly on the current authoritative baseline.
- the optimized sexp printer now emits OCaml-style byte escapes for Latin-1 strings, which removed the remaining Unicode/raw-string formatting cluster:
  - `Stdlib_Intl_CollatorTest.res`: **exact parity**
  - `chn_test.res`: **exact parity**
  - `exotic_labels_test.res`: **exact parity**
  - `gbk.res`: **exact parity**
  - `gpr_3142_test.res`: **exact parity**
  - `poly_variant_test.res`: **exact parity**
  - `raw_pure_test.res`: **exact parity**
  - `res_debug.res`: **exact parity**
  - `string_unicode_test.res`: **exact parity**
  - `switch_string.res`: **exact parity**
  - `tagged_template_test.res`: **exact parity**
  - `test_regex.res`: **exact parity**
- the constant `Blk_poly_var` conversion slice is now landed:
  - `bs_unwrap_test.res`: **exact parity**
  - `gpr_4280_test.res`: **exact parity**
  - `gpr_5218_test.res`: **exact parity**
  - `hash_collision_test.res`: **exact parity**
  - `pipe_syntax.res`: **exact parity**
  - `record_debug_test.res`: **exact parity**
  - `record_type_spread.res`: **exact parity**
  - `unboxed_use_case.res`: **exact parity**
  - `poly_variant_test.res`: **2 hunks** on the current authoritative baseline
- export-aware alias retention now keeps OCaml's module-export alias lets, which removed both accessor-file failures.
- the `Pisout` switch-normalization slice is now landed:
  - `arity_infer.res`: **exact parity**
  - `complete_parmatch_test.res`: **exact parity**
  - `gpr_1438.res`: **exact parity**
  - `gpr_4069_test.res`: **exact parity**
  - `int_switch_test.res`: **exact parity**
  - `mario_game.res`: **2 hunks** on the current authoritative baseline (down from **36** across later slices)
- the focused `Lam.if_` assert-failure rewrite is now landed:
  - `stringmatch_test.res`: **exact parity** (down from **1 hunk** on the prior baseline)
- the external-return-wrapper slice is now landed:
  - `bs_splice_partial.res`: **exact parity**
  - `js_nullable_test.res`: **exact parity**
  - `js_re_test.res`: **exact parity**
  - `js_string_test.res`: **exact parity**
  - `reactDOM.res`: **exact parity**
  - `return_check.res`: **exact parity**
  - `Stdlib_TempTests.res`: **4 hunks**, so its remaining diffs are now in static-exit numbering rather than nullable/unit FFI wrapping
- the recursive-module init-shape metadata slices are now mostly landed:
  - focused raw guardrail for `recursive_module.res`, `recursive_module_test.res`, `rec_module_test.res`, `rec_module_opt.res`, and `recmodule.res`: **5/5 exact**
  - the function-slot metadata slice kept OCaml's `Pt_constructor("Function", 3, 2)` behavior from `transl_recmodule.ml`
  - the recursive-module shape-name delimiter slice now also matches OCaml's `Const_base (Const_string (_, None)) -> Some DNone` lowering path
  - focused optimized recursive-module diffs are now down to **1** hunk total, all in `recmodule.res`, and that remaining hunk is identifier-stamp drift rather than shape construction
- the next visible optimized frontier is the current exact-diff leaders (`record_extension_test.res`, `exception_raise_test.res`, `js_exception_catch_test.res`, `Stdlib_DictTests.res`, `large_record_duplication_test.res`) plus the remaining switch-facing files (`variant.res`, `UntaggedVariants.res`, `switch_string.res`) and the stamp-heavy exception / `recmodule.res` residuals.
- the next visible optimized frontier is the current exact-diff leaders (`record_extension_test.res`, `exception_raise_test.res`, `js_exception_catch_test.res`, `Stdlib_DictTests.res`, `large_record_duplication_test.res`) plus the remaining raw-upstream exit-number files (`coercion_module_alias_test.res`, `exception_raise_test.res`, `js_exception_catch_test.res`, `record_extension_test.res`, `variant.res`) and the stamp-heavy exception / `recmodule.res` residuals.
- a fresh full raw `-drawlambda` rerun after this slice reported **654/657** with **4** hunks across `coercion_module_alias_test.res`, `record_extension_test.res`, and `variant.res`; the focused recursive-module raw slice still stayed exact, so those raw failures look separate from this metadata change and need their own session.
- Stamp canonicalization needs a fresh dedicated rerun; this slice was verified against exact parity output.

## Key Findings from Session 2026-04-12

### lowerer-generated ids now continue from the raw-lambda stamp stream
Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::renames_optional_parameter_guards_from_prefix_lets -- --exact
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 300 ./scripts/test_lambda_parity.sh -j1 'option_repr_test|inline_const_test|inline_const|Stdlib_TempTests'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- Optimized lambda:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Optimized lambda parity: **632/657**
  - Exact hunks: **91**

Key checkpoints:

- authoritative optimized baseline stayed flat at **632/657**, **91** hunks
- the new lowerer unit test locks OCaml's reverse-prefix optional-param rename allocation order
- direct per-file repro now matters more than the raw parity script for the stamp-heavy guard files:
  - `option_repr_test.res`: direct `-drawlambda` still shows Rust raw exits at `1` where OCaml has `3`
  - `gpr_5557.res`: direct `-drawlambda` still shows Rust raw exit `1` where OCaml has `2`

`compiler/core/lam_convert.ml` uses the current global `Ident` stamp after
raw-lambda construction when it synthesizes ids for optional-parameter renames
and wrapped exception handlers. Rust `compiler-rust/src/raw_lambda/lower.rs`
was still allocating those ids from `Ident::create_local`, which does not
continue from `RawLambdaConverter`'s internal `IdGenerator`. The lowerer now
receives the raw converter's current stamp from `driver.rs` and allocates its
fresh ids from a dedicated lowering `IdGenerator`, matching OCaml's phase
boundary semantics instead of the unrelated global local-id counter.

This slice is source-aligned and non-regressing, but it did **not** move the
authoritative optimized baseline on its own. The practical outcome is that the
remaining drift in files like `option_repr_test.res` is now clearly a raw/static
exit numbering problem rather than another lowerer stamp-allocation bug. One
important caveat from this session: for these files, direct `bsc -drawlambda`
repros currently disagree with the raw parity script's reported "exact" status,
so trust the direct repro when debugging the remaining exit-number mismatch.

### function directives and dense tag switches now lower like OCaml
Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::convert::tests::function_expression_preserves_directive_attribute -- --exact
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::marks_dense_const_only_switch_full_without_names -- --exact
timeout 300 ./scripts/test_lambda_parity.sh -j1 'alias_default_value_test|function_directives|function_directives_async|function_directives_no_inline|adt_optimize_test'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
timeout 1800 ./scripts/test_lambda_parity.sh -j1 --raw
```

Result:

- Optimized lambda:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Optimized lambda parity: **632/657**
  - Exact hunks: **91**
- Raw lambda:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Raw lambda parity: **654/657**
  - Exact hunks: **4**

Key checkpoints:

- focused optimized slice: **5/5 exact**
- dropped exact failures:
  - `alias_default_value_test.res`
  - `function_directives.res`
  - `function_directives_async.res`
  - `function_directives_no_inline.res`
  - `adt_optimize_test.res`

OCaml `compiler/ml/translcore.ml` extracts `@directive("...")` from function
expression attributes before building lambda function metadata. Rust
`compiler-rust/src/raw_lambda/convert.rs` was still leaving
`FunctionAttribute.directive` as `None`, so the raw function metadata diverged
before lowering and every directive-bearing function printed the wrong
optimized-lambda shape.

Rust now mirrors OCaml's attribute walk directly by reading the parser
attribute payload and threading the recovered directive string into
`convert_function_raw`. The new unit test locks that behavior to a concrete
`@directive("'use memo'")` example.

`compiler/core/lam_convert.ml` also treats dense constant-only tag switches as
full even when there is no explicit `sw_names` table. Rust
`compiler-rust/src/raw_lambda/lower.rs` was only marking `sw_consts_full` from
names or an already-set raw flag, which left `adt_optimize_test.res` with the
wrong lowered switch metadata. The lowerer now recognizes the dense `0..n-1`
const-only case directly, and the new unit test locks that shape in place.

This slice improved the fresh authoritative optimized baseline from
**627/657**, **97** hunks to **632/657**, **91** hunks, while keeping the full
raw baseline at **654/657**, **4** hunks across the existing
`coercion_module_alias_test.res`, `record_extension_test.res`, and
`variant.res` failures.

### nullary `CstrUnboxed` constructors now keep constructor metadata
Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::convert::tests::nullary_unboxed_constructor_keeps_constructor_metadata_in_raw_lambda -- --exact
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 300 ./scripts/test_lambda_parity.sh -j1 UntaggedVariants
timeout 300 ./scripts/test_lambda_parity.sh -j1 --raw UntaggedVariants
timeout 300 ./scripts/test_lambda_parity.sh -j1 js_array_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **625/657**
- Exact hunks: **99**

Key checkpoints:

- `UntaggedVariants.res`: **4 hunks** (down from **5**)
- focused raw `UntaggedVariants.res`: **exact parity**
- `js_array_test.res`: **exact parity**

`compiler/ml/translcore.ml` does not collapse a nullary unboxed constructor to
unit. It still carries constructor-pointer metadata into
`lam_constant_convert.ml`, and the raw printer only hides that detail because
both constructor pointers and unit print as `0a`.

Rust `compiler-rust/src/raw_lambda/convert.rs` was still treating zero-argument
`ConstructorTag::CstrUnboxed` values as `RawLambda::unit()`. That kept
`-drawlambda` looking fine but lost the constructor metadata that
`Lam_convert.convert` needs, which is why optimized lambda printed
`Const_js_undefined true` instead of
`Const_int 0 (Pt_constructor "OnlyOne" 1 0)` in `UntaggedVariants.res`.

`raw_lambda::convert` now preserves the constructor constant for nullary
`CstrUnboxed` values the same way it already preserved the recursive-module
`Function` shape constant. The new unit test locks that metadata in place. The
remaining `UntaggedVariants.res` diffs are now only the pre-existing
static-exit-numbering drift, so this slice reduced the authoritative baseline
from **100** to **99** hunks without regressing the raw or large-file guards.

### optimized sexp strings now use OCaml byte escapes
Ran:

```bash
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 180 ./scripts/test_lambda_parity.sh -j1 gpr_3142_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 'string_unicode_test|tagged_template_test|switch_string|gbk|test_regex|raw_pure_test'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **625/657**
- Exact hunks: **100**

Key checkpoints:

- `gpr_3142_test.res`: passes
- `string_unicode_test.res`: passes
- `tagged_template_test.res`: passes
- `switch_string.res`: passes
- `gbk.res`: passes
- `test_regex.res`: passes
- `raw_pure_test.res`: passes

`compiler/core/sexp_lambda.ml` uses OCaml string escaping, which prints lambda
strings as Latin-1 byte strings and emits decimal `\NNN` escapes for non-ASCII
bytes. Rust `compiler-rust/src/lambda/sexp_lambda.rs` was still delegating to
Rust `escape_default()`, so optimized sexps printed `\u{...}` escapes that do
not match either OCaml `String.escaped` output or the existing raw-lambda
printer.

Rust now mirrors the OCaml/raw-printer behavior directly:

- `escape_ocaml_string` emits `\"`, `\\`, `\n`, `\r`, `\t` for the standard
  control escapes
- non-printable and non-ASCII Latin-1 bytes now print as decimal `\NNN`
- the new unit tests lock both the non-ASCII byte case and the control-escape
  case into the optimized sexp printer

Authoritative repo-wide baseline moved from:

- **613/657**, **132** hunks

to:

- **625/657**, **100** hunks

That is a gain of **12 files** and **32 hunks**. The dropped exact failures were:
`Stdlib_Intl_CollatorTest.res`, `chn_test.res`, `exotic_labels_test.res`,
`gbk.res`, `gpr_3142_test.res`, `poly_variant_test.res`, `raw_pure_test.res`,
`res_debug.res`, `string_unicode_test.res`, `switch_string.res`,
`tagged_template_test.res`, and `test_regex.res`.

### recursive-module init-shape names now preserve `Some DNone`
Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::convert::tests::recmodule_function_init_shape_keeps_function_constructor_metadata -- --exact
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 600 ./scripts/test_lambda_parity.sh -j1 'recursive_module|recursive_module_test|rec_module_test|rec_module_opt|recmodule'
timeout 600 ./scripts/test_lambda_parity.sh -j1 --raw 'recursive_module|recursive_module_test|rec_module_test|rec_module_opt|recmodule'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- Optimized lambda:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Optimized lambda parity: **613/657**
  - Exact hunks: **132**
- Focused recursive-module optimized slice:
  - `recursive_module.res`: **exact parity**
  - `recursive_module_test.res`: **exact parity**
  - `rec_module_test.res`: **exact parity**
  - `rec_module_opt.res`: **exact parity**
  - `recmodule.res`: **1 hunk**
- Focused recursive-module raw slice: **5/5 exact**

`compiler/ml/transl_recmodule.ml` builds recursive-module init-shape names as
`Const_base (Const_string (Ident.name id, None))`. `compiler/core/lam_constant_convert.ml`
then lowers those names through `parse_processed_delim`, so the optimized sexp
printer sees `Const_string ... (Some DNone)`.

Rust `compiler-rust/src/raw_lambda/convert.rs` was still constructing those
shape-name strings with `Constant::string(id.name())`, which preserved `delim:
None` all the way into the optimized lambda dump. Raw `-drawlambda` stayed exact
because the raw printer ignores delimiter metadata, but optimized sexps kept
showing the whole recursive-module cluster as mismatched.

Rust now mirrors the OCaml path directly for recursive-module shape names:

- function-value shape tuples use `Constant::string_with_delim(..., StringDelim::Plain)`
- submodule shape tuples use the same `StringDelim::Plain` construction
- the existing raw unit test now locks that init-shape metadata to `Some(StringDelim::Plain)`

Authoritative repo-wide baseline moved from:

- **606/657**, **174** hunks

to:

- **613/657**, **132** hunks

This removed the focused failures in `recursive_module.res`,
`recursive_module_test.res`, `rec_module_test.res`, and `rec_module_opt.res`.
`recmodule.res` is now down to a single exact hunk that is only identifier-stamp
drift, so the remaining recursive-module work is no longer shape construction.

### recursive-module init shapes now keep `Function` constructor metadata
Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::convert::tests::recmodule_function_init_shape_keeps_function_constructor_metadata -- --exact
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 600 ./scripts/test_lambda_parity.sh -j1 'recursive_module|recursive_module_test|rec_module_test|rec_module_opt|recmodule'
timeout 600 ./scripts/test_lambda_parity.sh -j1 --raw 'recursive_module|recursive_module_test|rec_module_test|rec_module_opt|recmodule'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
timeout 1800 ./scripts/test_lambda_parity.sh -j1 --raw
```

Result:

- Optimized lambda:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Optimized lambda parity: **606/657**
  - Exact hunks: **174**
- Raw lambda guardrail:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Raw lambda parity: **654/657**
  - Raw parity hunks: **4**
- Focused recursive-module optimized slice:
  - `recursive_module.res`: **2 hunks**
  - `recursive_module_test.res`: **4 hunks**
  - `rec_module_test.res`: **12 hunks**
  - `rec_module_opt.res`: **6 hunks**
  - `recmodule.res`: **11 hunks**
- Focused recursive-module raw slice: **5/5 exact**

`compiler/ml/transl_recmodule.ml` does not encode function-valued recursive
module slots as `Pt_module_alias`. It builds the init-shape with
`Const_pointer (0, Pt_constructor {name = "Function"; const = 3; non_const = 2})`
and then attaches the field name in the surrounding tuple.

Rust `compiler-rust/src/raw_lambda/convert.rs` was still using
`Constant::ModuleAlias` for those function slots because raw printing also
renders both shapes as `0a`. That kept focused `-drawlambda` parity green, but
it meant the optimized sexp dump lost the constructor metadata that OCaml keeps.

Rust now mirrors `transl_recmodule.init_shape` directly:

- recursive-module function slots use constructor-tagged `Constant::Int { i: 0, ... }`
  with `PointerInfo::Constructor { name = "Function", const_ = 3, non_const = 2 }`
- raw printing still stays exact because constructor-tagged pointer ints continue
  to print as `0a`
- the new unit test locks that metadata into the raw init-shape builder

This is a verified OCaml-aligned change that should stay even though the current
exact full baseline regressed from **166** to **174** hunks. The recursive-module
cluster is no longer missing the `Function` shape metadata; the visible remaining
drift in focused diffs is now stamp numbering. The full raw rerun's remaining
failures (`coercion_module_alias_test.res`, `record_extension_test.res`,
`variant.res`) do not touch this recursive-module init-shape path.

### native-int lowering now matches `lam_constant_convert.ml`
Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::lowers_native_int_constants_to_wrapped_int32 -- --exact
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 300 ./scripts/test_lambda_parity.sh -j1 js_json_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **606/657**
- Stamp-canonicalized parity: not re-baselined in this rerun
- Exact hunks: **166**
- Stamp-canonicalized hunks: not re-baselined in this rerun

Key checkpoints:

- `js_json_test.res`: passes
- next visible frontier remains the exception / recursive-module / switch clusters at the top of the current exact-diff table

`compiler/core/lam_constant_convert.ml` converts `Const_base (Const_int i)` with
`Int32.of_int i`, so OCaml's optimized-lambda dump wraps wide source ints to signed
32-bit values at the raw-to-lowered boundary.

Rust `compiler-rust/src/raw_lambda/lower.rs` was still forwarding those values as
`Constant::NativeInt`, which left optimized-lambda sexps printing unsigned-looking
large positives like `2947526575` where OCaml printed the wrapped `-1347440721`.

Rust now mirrors the OCaml boundary rule directly:

- `Constant::NativeInt` lowers to `Constant::Int { i: i as i32, ... }`
- the new unit test covers the representative `0xAFAFAFAF` case from `js_json_test.res`

Authoritative repo-wide baseline moved from:

- **602/657**, **172** hunks

to:

- **606/657**, **166** hunks

This confirms the remaining `js_json_test.res` drift was not a printer problem or a
later-pass issue. It was one more missing `Lam_convert.convert` constant-lowering
rule at the optimized boundary.

### constant `Blk_poly_var` conversion moved the polyvariant frontier again
Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::lowers_polyvariant_block_payload_tag_from_name -- --exact
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::lowers_constant_polyvariant_block_payload_tag_from_name -- --exact
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 600 ./scripts/test_lambda_parity.sh -j1 'bs_unwrap_test|big_polyvar_test'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **602/657**
- Stamp-canonicalized parity: not re-baselined in this rerun
- Exact hunks: **172**
- Stamp-canonicalized hunks: not re-baselined in this rerun

Key checkpoints:

- `bs_unwrap_test.res`: passes
- `big_polyvar_test.res`: passes
- `poly_variant_test.res`: **2 hunks**
- `UntaggedVariants.res`: **5 hunks**
- next visible frontier from this slice: the remaining polyvariant/unit frontier in `poly_variant_test.res` / `UntaggedVariants.res`, plus the existing exception and recursive-module clusters

`compiler/core/lam_constant_convert.ml` does the `Blk_poly_var` payload rewrite
for constants as well as for `Pmakeblock`: it discards the hashed raw first field
and rebuilds the block payload from the symbolic tag name, using `Const_string`
unless the tag is already a valid hash-number literal.

Rust `compiler-rust/src/raw_lambda/lower.rs` already mirrored that rule for
`Primitive::Pmakeblock(_, TagInfo::PolyVar(_), _)`, but it was still forwarding
raw constant polyvariant blocks unchanged. That left optimized lambda dumps full
of hashed `Const_int` payload tags in places where OCaml had already recovered
the source-level names.

Rust now mirrors the OCaml constant branch too:

- `Constant::Block { tag_info: TagInfo::PolyVar(name), ... }` now rebuilds its
  first element from `name` during optimized lowering
- the value payload is still recursively lowered the same way as before
- the new unit test covers the constant-form path directly, alongside the
  existing primitive-form test

Authoritative repo-wide baseline moved from:

- **594/657**, **206** hunks

to:

- **602/657**, **172** hunks

That is a gain of **8 files** and **34 hunks**. The dropped exact failures were:
`bs_unwrap_test.res`, `gpr_4280_test.res`, `gpr_5218_test.res`,
`hash_collision_test.res`, `pipe_syntax.res`, `record_debug_test.res`,
`record_type_spread.res`, and `unboxed_use_case.res`.

### external-call return wrappers and CMI byte preservation moved the FFI frontier
Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::convert::tests::ffi_spec_reads_null_to_opt_return_wrapper
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::wraps_null_to_opt_return_wrapper_around_js_call
cargo test --release --manifest-path compiler-rust/Cargo.toml lambda::convert::tests::decoded_external_ffi_spec_reads_null_to_opt_wrapper
cargo test --release --manifest-path compiler-rust/Cargo.toml cmi::marshal_reader::tests::test_read_small_string_preserves_non_utf8_bytes
cargo build --release --manifest-path compiler-rust/Cargo.toml
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **594/657**
- Stamp-canonicalized parity: not re-baselined in this rerun
- Exact hunks: **206**
- Stamp-canonicalized hunks: not re-baselined in this rerun

Key checkpoints:

- `bs_splice_partial.res`: passes
- `js_nullable_test.res`: passes
- `js_re_test.res`: passes
- `js_string_test.res`: passes
- `reactDOM.res`: passes
- `return_check.res`: passes
- `mario_game.res`: **2 hunks**
- `Stdlib_TempTests.res`: **4 hunks**
- next visible frontier from this slice: `sw_consts_full` lowering in `mario_game.res` plus static-exit numbering in `Stdlib_TempTests.res`

`compiler/core/lam_convert.ml` does not leave JS externals as bare `Pjs_call`
nodes when the FFI metadata says the result must be wrapped. It threads the
marshaled external-return wrapper through lowering and applies `Lam.result_wrap`
to produce `Pnull_to_opt`, `Pnull_undefined_to_opt`, or `Lsequence(call, ())`
for replaced-unit returns.

Rust had two distinct gaps:

- `compiler-rust/src/raw_lambda/convert.rs` and the legacy fallback in
  `compiler-rust/src/lambda/convert.rs` were discarding the marshaled wrapper
  metadata carried in `primitive.prim_native_name`
- `compiler-rust/src/cmi/marshal_reader.rs` was decoding OCaml strings with
  UTF-8 lossiness, which corrupted the raw marshaled byte payload for stdlib
  externals loaded from `.cmi` files

Rust now:

- records explicit `ExternalReturnWrapper` metadata in
  `compiler-rust/src/lambda/primitive.rs`
- decodes the marshaled FFI payload in both raw-lambda and legacy-lambda
  primitive conversion, including object-create classification and nullable/unit
  return wrappers
- applies the wrapper in `compiler-rust/src/raw_lambda/lower.rs` the same way
  OCaml `Lam.result_wrap` does
- preserves OCaml string bytes exactly in
  `compiler-rust/src/cmi/marshal_reader.rs`, so non-UTF-8 marshaled metadata
  survives `.cmi` loading intact

Representative `-drawlambda` checks for `js_nullable_test.res` and
`mario_game.res` stayed exact, which kept this session scoped to optimized
lowering and FFI metadata rather than upstream raw-lambda construction.

Authoritative repo-wide baseline moved from:

- **587/657**, **225** hunks

to:

- **594/657**, **206** hunks

That is a gain of **7 files** and **19 hunks**. The wrapper-related external
frontier is materially smaller now; the remaining failures on those code paths
are no longer about nullable/unit result wrapping itself.

### `Lam.apply` smart constructors, `Lam.prim` folding, and builtin-object classification moved the baseline again
`compiler/core/lam_convert.ml` does not lower applications and primitives by
blindly rebuilding the raw node. It routes them through the same smart
constructors OCaml uses for optimized lambda:

- `Lam.apply` eta-reduces wrappers like `fun x -> prim x`
- `Lam.prim` folds small constant cases instead of preserving the unfused
  primitive node
- blank JS externals returning builtin object types become
  `Pjs_object_create`, not a generic `Pjs_call`

Rust `compiler-rust/src/raw_lambda/lower.rs` was still constructing `Lapply`
and most `Lprim` nodes directly, and `compiler-rust/src/raw_lambda/typeopt.rs`
only recognized dict paths as builtin object results. That left several
structurally small but high-signal files on the board even when `-drawlambda`
already matched:

- `ari_regress_test.res`
- `equal_test.res`
- `big_enum.res`
- `reasonReact.res`
- `reasonReactOptimizedCreateClass.res`

Rust now:

- lowers applications through `make_apply`/`make_lapply`, including the
  `Lam.apply` eta-reduction path
- ports the missing `Lam.prim` folding cases needed by this slice and keeps
  named switches out of the `happens_to_be_diff` collapse path
- classifies `TypeDesc::Tobject` as a builtin object result, which lets
  `Js.Obj.empty()` lower to `Pjs_object_create` instead of `Pjs_call`
- covers the slice with focused unit tests:
  - `raw_lambda::lower::tests::eta_reduces_primitive_wrapper_application`
  - `raw_lambda::lower::tests::folds_integer_comparison_constants_to_boolean_constant`
  - `raw_lambda::lower::tests::keeps_named_linear_switches_instead_of_collapsing_to_scrutinee`
  - `raw_lambda::lower::tests::lowers_labeled_blank_js_call_to_object_create_without_objcreate_kind`
  - `raw_lambda::typeopt::tests::builtin_object_recognizes_object_types`

Verified focused checks:

- `ari_regress_test.res`: **exact parity**
- `equal_test.res`: **exact parity**
- `big_enum.res`: **exact parity**
- `reasonReact.res`: **exact parity**
- `reasonReactOptimizedCreateClass.res`: **exact parity**

A focused raw `-drawlambda` rerun for the two `reasonReact` files also stayed
exact, confirming that this slice was in `Lam_convert.convert` lowering rather
than upstream raw-lambda construction.

Authoritative repo-wide baseline moved from:

- **567/657**, **264** hunks

to:

- **587/657**, **225** hunks

That is a gain of **20 files** and **39 hunks**. The remaining frontier is
smaller now and more concentrated in exception, recursive-module, record-spread,
and module-alias clusters.

### polyvariant block-tag lowering plus OCaml string escaping moved the set frontier
`compiler/core/lam_convert.ml` special-cases `Pmakeblock` for `Blk_poly_var s`:
it discards the raw hash payload and rebuilds the first block field from `s`
itself, using `Const_string` unless `s` is already a valid hash number. Rust
`compiler-rust/src/raw_lambda/lower.rs` was still forwarding the lowered raw
hash (`86` for `` `V ``), so optimized lambda kept emitting the wrong block
payload even when the raw lambda already matched structurally.

At the same time, `compiler-rust/src/lambda/sexp_lambda.rs` was still rendering
quoted atoms with `escape_default()`, which escaped apostrophes and produced
printer-only diffs like `"l\\'"` where OCaml prints `"l'"`.

Rust now:

- ports the `Blk_poly_var` `Pmakeblock` rewrite in `raw_lambda/lower.rs`
- preserves apostrophes in quoted sexp atoms while keeping the existing escapes
- covers both slices with focused unit tests:
  - `raw_lambda::lower::tests::lowers_polyvariant_block_payload_tag_from_name`
  - `lambda::sexp_lambda::tests::does_not_escape_apostrophes_in_strings`

Verified focused check:

- `set_gen.res`: **exact parity** (down from **8 hunks**)

Authoritative repo-wide baseline moved from:

- **537/657**, **425** hunks

to:

- **567/657**, **264** hunks

That is a gain of **30 files** and **161 hunks**. The polyvariant/set frontier
is materially smaller now; the remaining optimized work is concentrated in the
current leaders (`bs_unwrap_test.res`, `record_extension_test.res`,
`exception_raise_test.res`, `js_exception_catch_test.res`, `Stdlib_DictTests.res`)
plus the recursive-module cluster and the raw-parity outlier
`coercion_module_alias_test.res`.

### raw sequence traversal order moved the exception frontier
`compiler/ml/translcore.ml` builds sequences as:

```text
Lsequence (transl_exp expr1, transl_exp expr2)
```

That matters because OCaml evaluates constructor arguments right-to-left. Rust
`compiler-rust/src/raw_lambda/convert.rs` was still converting `Texp_sequence`
left-to-right, so later sequence elements consumed lower `next_raise_count()`
ids and earlier `try ... catch` expressions ended up with the wrong static-exit
numbering.

`compiler-rust/src/raw_lambda/convert.rs` now converts the RHS before the LHS
when lowering `Texp_sequence`, and it covers that OCaml-aligned traversal with:

- `raw_lambda::convert::tests::raw_sequence_converts_rhs_before_lhs_for_raise_counts`

Verified focused checks:

- `test_trywith.res`: **exact parity** (down from **10 hunks**)
- `exception_raise_test.res`: **10 hunks** on the authoritative baseline (down from **12**)

Authoritative repo-wide baseline moved from:

- **533/657**, **515** hunks

to:

- **537/657**, **425** hunks

That is a gain of **4 files** and **90 hunks**. The previous exception static-exit
cluster is smaller now: `test_trywith.res` is gone, and the remaining exception
work is concentrated in `exception_raise_test.res` plus the raw-parity outlier
`coercion_module_alias_test.res`.

### optional-parameter renaming moved the uncurry frontier
`compiler/core/lam_convert.ml` runs `rename_optional_parameters` before lowering
function bodies. That pass rewrites leading optional-argument guard lets from the
hidden `*opt*` parameter name to fresh names derived from the bound value id
(`xOpt`, `zOpt`, and so on), and then updates the function parameter list to
match.

Rust `raw_lambda/lower.rs` was still lowering `RawLambda::Lfunction` bodies
directly, so `-dlambda-sexp` kept printing raw `*opt*` names even when
`-drawlambda` already matched OCaml.

`compiler-rust/src/raw_lambda/lower.rs` now ports that OCaml prefix-only rewrite
for function bodies and covers it with:

- `raw_lambda::lower::tests::renames_optional_parameter_guards_from_prefix_lets`

Verified focused checks:

- `uncurried_default.args.res`: **exact parity** (down from **16 hunks**)
- `test_case_opt_collision.res`: **exact parity**
- `uncurried_cast.res`: **exact parity**
- `more_uncurry.res`: **exact parity**
- `mario_game.res`: still failing on the authoritative baseline, so its remaining
  diffs are no longer explained by hidden optional-parameter naming alone

Authoritative repo-wide baseline moved from:

- **530/657**, **569** hunks

to:

- **533/657**, **515** hunks

That is a gain of **3 files** and **54 hunks**. The `*opt*`-naming cluster is
smaller now; the remaining uncurry-heavy frontier is the larger files that still
fail after this pass (`UncurriedAlways.res`, `option_repr_test.res`,
`reasonReact.res`, `mario_game.res`).

### `Pisout` normalization plus const-only switch fullness moved the switch frontier
`compiler/core/lam_convert.ml` emits `Pisout` in lowered lambda as the OCaml
two-argument form:

- primitive payload = offset
- arguments = `[range; scrutinee]`

Rust raw matching was still baking the range into `Primitive::Pisout(range)` and
carrying only the scrutinee expression as the argument list. That meant the
existing `Lam.if_` switch-failaction rewrite in `compiler-rust/src/lambda/mod.rs`
never matched the lowered shape, even when the raw lambda already matched OCaml.

`compiler-rust/src/raw_lambda/lower.rs` now fixes both parts of the lowering:

- one-argument raw `Pisout(range)` forms are normalized into the OCaml lowered
  representation, preserving `Poffsetint` as the primitive offset when present
- const-only switches with no failaction now lower with `sw_blocks_full = true`,
  matching the simple `convert_switch` branch in `lam_convert.ml`

That slice is covered by the new focused unit test:

- `raw_lambda::lower::tests::lowers_const_only_switch_with_full_blocks_for_if_rewrite`

Verified focused checks:

- `arity_infer.res`: **exact parity**
- `complete_parmatch_test.res`: **exact parity**
- `mario_game.res`: **21 hunks** (down from **36**)

Authoritative repo-wide baseline moved from:

- **514/657**, **610** hunks

to:

- **530/657**, **569** hunks

That is a gain of **16 files** and **41 hunks**. The remaining switch frontier is
smaller and more specific now: the files still left in that family are
`set_gen.res`, `test_set.res`, `variant.res`, plus the non-switch residuals in
`mario_game.res`.

### `Pextension_slot_eq` lowering moved the exception frontier
`compiler/core/lam_convert.ml` lowers `Pextension_slot_eq` by comparing the
exception id field (`RE_EXN_ID`) with `Pstringcomp Ceq`; Rust was still leaking
the raw primitive into optimized lambda dumps.

`compiler-rust/src/raw_lambda/lower.rs` now mirrors that `lam_prim` rule and has
a unit test covering the lowered `Pfield(0, Fld_record "RE_EXN_ID")` shape.

Verified focused checks:

- `test_trywith.res`: still failing, but now only **10 hunks**, all from static-exit numbering
- `exception_raise_test.res`: still failing, but now only **12 hunks**, again from static-exit numbering

Authoritative repo-wide baseline moved from:

- **501/657**, **680** hunks

to:

- **514/657**, **610** hunks

That is a gain of **13 files** and **70 hunks**. The next exception-oriented
lowering frontier is no longer slot comparison shape; it is static-catch /
static-raise numbering and aliasing.

### polyvariant constant-match metadata moved the frontier again
`compiler-rust/src/raw_lambda/convert.rs` and `compiler-rust/src/raw_lambda/matching.rs`
now keep `PointerInfo::PolyVariant` on hashed constant polyvariant equality tests
instead of degrading them to raw `"123a"` pointer strings too early.

That keeps `-drawlambda` parity intact while allowing `raw_lambda/lower.rs` to recover
OCaml's symbolic `Const_pointer "Tag"` form during optimized-lambda lowering.

Verified focused checks:

- `LetUnwrap.res`: **exact parity** (down from **1 hunk**)
- `more_poly_variant_test.res`: **3 hunks** (down from **9**)

Authoritative repo-wide baseline moved from:

- **496/657**, **724** hunks

to:

- **501/657**, **679** hunks

This confirms the remaining polyvariant frontier is no longer the simple constant-hash
comparison path. The next visible cluster is the broader `more_poly_variant_test.res` /
`poly_variant_test.res` family plus the existing large-file leaders.

### `Lam.if_` smart-constructor parity moved again
`compiler-rust/src/lambda/mod.rs` now mirrors the OCaml `Lam.seq` / `Lam.if_`
smart-constructor branches that were still missing for:

- `Pt_assertfalse` branches lowering to `seq`
- boolean `if a then true else false` / `if a then false else true`
- raise-then / non-constant-else lowering to `seq (if ... raise ... ()) else_`
- `Pisout` switch-failaction folding
- `Pisint` rewrites that reuse or invert nested integer predicates

That slice is covered by new unit tests in `lambda::tests` for:

- assert-false sequencing
- boolean-condition reuse and negation
- raise-then sequencing
- `Pisint` branch reuse

Verified focused checks:

- `stringmatch_test.res`: **exact parity**
- `js_json_test.res`: **45 hunks** unchanged

Authoritative repo-wide baseline moved from:

- **493/657**, **733** hunks

to:

- **496/657**, **724** hunks

This confirms the OCaml-aligned `Lam.if_` slice was real and useful, but also
confirms the remaining `js_json_test.res` / exception-control-flow cluster is no
longer explained by this single smart-constructor gap.

### dump routing is now correct
`compiler-rust/src/driver.rs` no longer prints `-dlambda-sexp` from the legacy typedtree-to-lambda shortcut.
The dump path now does:

```text
typedtree -> raw_lambda::convert -> raw_lambda::lower -> sexp_lambda
```

The JS backend path remains unchanged for now.

### the first real `Lam_convert.convert` slice is landed
`compiler-rust/src/raw_lambda/lower.rs` now performs real lowering work instead of
`raw.into_lowered()`.

Implemented slices include:
- alias-following through a lowering context
- application status lowering to `App_uncurry`
- constructor/pointer normalization needed by optimized lambda
- let/letrec rebuilding, including splitting non-recursive bindings out of `letrec`
- switch lowering, including offset-switch folding
- try/with lowering with `PwrapExn`
- initial primitive/module-lowering cases used by the small parity files

### constructor metadata had to survive the raw stage
To keep raw parity intact while enabling optimized lowering:
- `raw_lambda/convert.rs` now preserves constructor information on integer constants
- `raw_lambda/print.rs` prints constructor-tagged ints back as raw `0a`-style pointers
- lambda string-delimiter handling was extended for `*j` / `js` / `json` / backtick forms

### switch names and JS FFI lowering moved the frontier again
`compiler-rust/src/raw_lambda/matching.rs` now preserves constructor names for optimized
switch printing, and `compiler-rust/src/raw_lambda/convert.rs` now threads enough FFI
metadata into lowering to distinguish:

- blank JS calls that should become `Pjs_object_create`
- unit-returning JS calls that must lower as `seq(Pjs_call ..., ())`

That same slice is consumed in `compiler-rust/src/raw_lambda/lower.rs`, so the lambda
printer can stay dumb while the lowerer makes the OCaml-aligned constructor choice.

### the repo-wide baseline moved materially again
Verified focused checks:

- `AsInUncurriedExternals.res`: **exact parity**
- `DictInference.res`: **exact parity**
- `DictPatternMatchingOptimization.res`: **exact parity**
- `js_array_test.res`: **exact parity**

Authoritative repo-wide baseline moved from:

- **208/657**, **7862** hunks

to:

- **377/657**, **3723** hunks

This drop confirms the next `Lam_convert.convert` slice is landing in the right place:
constructor-name preservation plus JS-call result-kind lowering removed both small-file
structural mismatches and one of the major large-file guards.

### constructor runtime metadata now survives lowering
The next slice had to preserve more raw-stage detail without breaking `-drawlambda` parity:

- typed string constants now keep OCaml's plain-string delimiter as `DNone`
- constructor `@as(...)` payloads now survive typing and raw conversion for int/string/float/bigint/bool/null/undefined cases
- constant polymorphic variants now keep their source tag names alongside the hashed raw representation
- optimized lowering now uses that metadata to recover OCaml-aligned pointer, constructor, and switch shapes

This is what made `DictInternalRepresentation.res` and `VariantCoercion.res` drop out while
cutting `big_polyvar_test.res` roughly in half.

### primitive folding needs to match OCaml, but must stay crash-free
`raw_lambda/lower.rs` now folds the small set of binary integer primitives that OCaml's
`Lam_convert.convert` folds after constructor runtime tags have been resolved.

That slice initially introduced a divide-by-zero crash because `then_some(...)` eagerly
evaluated `wrapping_div` / `wrapping_rem`. The authoritative rerun is only valid after
switching those guards to lazy `then(|| ...)`, which restored Rust compile coverage to
**657/657**.

### the repo-wide baseline moved materially again
Verified focused checks:

- `DictInternalRepresentation.res`: **exact parity**
- `VariantCoercion.res`: **exact parity**
- `big_polyvar_test.res`: **602 hunks** (down from **1202**)

Authoritative repo-wide baseline moved from:

- **377/657**, **3723** hunks

to:

- **426/657**, **2006** hunks

This slice confirms the next broad lowering frontier is no longer constructor runtime tags.
The biggest remaining cluster is now the `big_polyvar_test.res` family around `Praw_js_code_exp`
argument shape and `Lglobal_module`/exception payload construction.

### imported-module and raw-js-code lowering moved the frontier again
`compiler-rust/src/raw_lambda/lower.rs` now mirrors the `Lam_convert.convert`
branches that were still missing for:

- `Pimport` argument lowering with OCaml's `~dynamic_import` scoping rules
- collapsing imported `let global-module = ... in ...` bundles back to a single
  `Lglobal_module ... true`
- `Praw_js_code_exp` / `Praw_js_code_stmt` payload recovery from raw string
  arguments into the primitive payload itself

That slice is covered by new lowerer unit tests for:

- imported field access becoming `Lglobal_module ... true`
- alias-wrapped module imports staying `false`
- imported let-bound global-module bundles collapsing correctly
- raw JS code primitives lowering to zero-arg payload forms

Verified focused checks:

- `DynamicImportModuleWithAlias.res`: **exact parity**
- `ExternalExtension.res`: **exact parity**
- `Import.res`: **1 hunk** remaining
- `big_polyvar_test.res`: **601 hunks** (down from **602**)

Authoritative repo-wide baseline moved from:

- **426/657**, **2006** hunks

to:

- **460/657**, **1859** hunks

This confirms the import/raw-JS slice is now mostly complete. The next visible
frontier in this area is the missing `Lam.if_` smart-constructor behavior that
still leaves `Import.res` with a constant-condition branch.

### constant-condition folding in `Lam.if_` moved the baseline again
`compiler-rust/src/lambda/mod.rs` now matches the first OCaml `Lam.if_` branch:
when the condition is a constant, the smart constructor returns the selected
branch instead of preserving `Lifthenelse`.

That is deliberately limited to the constant-condition case. The remaining
`Lam.if_` parity work is still in the smarter non-constant rewrites from
`compiler/core/lam.ml`.

Verified focused checks:

- `Import.res`: **exact parity**
- `LetUnwrap.res`: **19 hunks**
- `DerivingAccessorsCurried.res`: **1 hunk**
- `DerivingAccessorsUncurried.res`: **1 hunk**
- `big_polyvar_test.res`: **601 hunks**

Authoritative repo-wide baseline moved from:

- **460/657**, **1859** hunks

to:

- **461/657**, **1855** hunks

This confirms the constant-condition branch was the last blocker for
`Import.res`. The next structural frontier is the remaining `Lam.if_`
smart-constructor rewrites plus the alias/module-export shape still showing up
in the accessor files.

### direct-ident constructor switch names now honor `pat_env`
`compiler-rust/src/raw_lambda/matching.rs` now mirrors the OCaml
`matching_polyfill.ml` rule for direct constructor-type identifiers: recover
switch names from the typed pattern environment instead of resolving against an
empty environment.

That slice is intentionally narrow:

- direct `Path::Pident` constructor types now use `pat.pat_env`
- qualified paths still fall back to the old resolver for now because a broad
  `env.lookup_type` path introduced a `string_set.res` stack overflow
- a new unit test covers `result` constructor-name recovery through `pat_env`

Verified focused checks:

- `LetUnwrap.res`: **1 hunk** remaining (down from **19**)
- `string_set.res`: direct repro no longer crashes after narrowing lookup back
  away from `Pdot` resolution

Authoritative repo-wide baseline moved from:

- **461/657**, **1855** hunks

to:

- **461/657**, **1858** hunks

This is a correctness-aligned change, not a local parity win yet. The direct
`pat_env` recovery is still worth keeping because it matches OCaml for the
`Pident` case and removes the wrong switch-metadata shape from `LetUnwrap.res`;
the remaining work is to port the qualified-path lookup safely enough to avoid
reintroducing the `string_set.res` recursion and then clean up the constructor
literal / exception-tail regressions it exposes.

## Root-Cause Frontiers

1. **Continue porting `Lam_convert.convert`**
   - remaining JS-call primitive lowering
   - directive threading on lowered function attributes (`'use memo'`, async/no-inline variants)
   - remaining exception/module lowering forms
   - module/coercion lowering forms that are still truly post-raw
2. **Keep raw-stage blockers separate from optimized work**
   - `coercion_module_alias_test.res` still differs under `-drawlambda`
   - do not treat that file as an optimized-lambda target until the raw shape is fixed
3. **Use smallest optimized-only failures for quick structural validation**
   - `adt_optimize_test.res`
   - `alias_default_value_test.res`
   - `function_directives.res`
   - `function_directives_async.res`
   - `function_directives_no_inline.res`
4. **Use larger files to validate that a rule generalizes**
   - `mario_game.res`
   - `record_extension_test.res`
   - `variant.res`
   - `stdlib/Stdlib_IteratorTests.res`
   - `stdlib/intl/Stdlib_IntlTests.res`
5. **Treat later `lam_pass_*` work as out of direct parity scope**
   - only touch those passes if a shared infrastructure change requires it
   - do not spend cycles there while `raw_lambda/lower.rs` is still incomplete

## Immediate Next Milestone

1. Finish the next focused optimized-only directive / function-attribute gaps:
   - `alias_default_value_test.res`
   - `function_directives.res`
   - `function_directives_async.res`
   - `function_directives_no_inline.res`
2. Keep raw-stage coercion drift out of optimized slices for now:
   - `coercion_module_alias_test.res`
3. Validate the same rule on broader files that still exercise lowered JS-call and function metadata:
   - `mario_game.res`
   - `record_extension_test.res`
   - `variant.res`
   - `stdlib/Stdlib_IteratorTests.res`
4. Re-run:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

5. Commit immediately after the next verified OCaml-aligned improvement.

## Session Log

### 2026-04-12 (dynamic-import scope propagation into nested JS calls)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::marks_imported_js_call_as_dynamic -- --exact
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 300 ./scripts/test_lambda_parity.sh -j1 import2
timeout 300 ./scripts/test_lambda_parity.sh -j1 --raw import2
timeout 300 ./scripts/test_lambda_parity.sh -j1 import_external
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **627/657**
- Stamp-canonicalized parity: **627/657**
- Exact hunks: **97**
- Stamp-canonicalized hunks: **97**

Key checkpoints:

- `import2.res`: passes
- `import_external.res`: passes
- focused `--raw import2`: passes
- `coercion_module_alias_test.res`: still a raw-stage failure and remains outside the optimized frontier

Authoritative repo-wide baseline moved from:

- **625/657**, **99** hunks

to:

- **627/657**, **97** hunks

This slice fixes the `Lam_convert.convert` dynamic-import scoping rule for nested
JS calls under `Pimport`. Rust was already lowering imported module fields as
dynamic, but it was preserving the raw `PjsCall.dynamic_import` bit for nested
calls like `default` access instead of forcing the enclosing `Pimport` scope
through. OCaml threads `~dynamic_import:true` through that subtree, so the Rust
lowerer now ORs the surrounding import scope into lowered `PjsCall` nodes.

That removes both `import2.res` and `import_external.res` from the optimized
failure list with no raw regression on the focused import repro.

### 2026-04-12 (predef-exception lowering and plain loc strings)

Ran:

```bash
cargo build --release --manifest-path compiler-rust/Cargo.toml
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::lowers_predef_exception_global_module_to_string_constant -- --exact
timeout 300 ./scripts/test_lambda_parity.sh -j1 tests/tests/src/conditional/cond_a.res
timeout 300 ./scripts/test_lambda_parity.sh -j1 stringmatch_test
timeout 300 ./scripts/test_lambda_parity.sh -j1 --raw tests/tests/src/conditional/cond_a.res
timeout 1800 ./scripts/test_lambda_parity.sh -j1
timeout 1800 ./scripts/test_lambda_parity.sh -j1 --raw
```

Result:

- Optimized lambda:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Optimized lambda parity: **493/657**
  - Stamp-canonicalized parity: **493/657**
  - Exact hunks: **733**
  - Stamp-canonicalized hunks: **733**
- Raw lambda guardrail:
  - OCaml compile coverage: **657/657**
  - Rust compile coverage: **657/657**
  - Raw lambda parity: **656/657**
  - Raw parity hunks: **2**

Key checkpoints:

- `conditional/cond_a.res`: passes
- `stringmatch_test.res`: **1 hunk** remaining
- focused `--raw tests/tests/src/conditional/cond_a.res`: passes
- `js_json_test.res`: **8 hunks**
- `big_polyvar_test.res`: **2 hunks**

This slice ports the `Lam_convert.convert` rule that treats predefined exceptions
like `Assert_failure` as string constants at the optimized-lambda boundary instead
of leaving them as `Lglobal_module`. The same pass also now preserves OCaml's plain
`DNone` delimiter on file-name strings threaded through assert-failure, match-failure,
and recursive-module location payloads. That combination removed the broad
`Assert_failure` / location-string shape mismatch across the suite and collapsed
`stringmatch_test.res` to a single remaining `Lam.if_` hunk.

The end-of-session full raw rerun reported one exact raw failure in
`coercion_module_alias_test.res`. The saved diff does not touch the new
predef-exception or location-string branches, so this commit keeps the session
scoped to the verified optimized-lambda improvement and leaves that raw exact-diff
drift for a separate follow-up.

### 2026-04-12 (export-aware alias retention for module exports)

Ran:

```bash
cargo test --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests -- --nocapture
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 600 ./scripts/test_lambda_parity.sh -j1 'DerivingAccessorsCurried|DerivingAccessorsUncurried|coercion_module_alias_test|LetUnwrap'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **463/657**
- Stamp-canonicalized parity: **463/657**
- Exact hunks: **1853**
- Stamp-canonicalized hunks: **1853**

Key checkpoints:

- `DerivingAccessorsCurried.res`: passes
- `DerivingAccessorsUncurried.res`: passes
- `LetUnwrap.res`: **1 hunk**
- `coercion_module_alias_test.res`: **40** hunks
- next visible frontier: `LetUnwrap` constructor-literal recovery plus the quoted-identifier output mismatch in `coercion_module_alias_test.res`

This slice ports the `Lam_convert.convert` rule that keeps `Alias = Lvar`
bindings when the alias identifier is exported. Rust now discovers exported
idents from `Blk_module_export` metadata before lowering, keeps those alias lets,
and still rewrites downstream uses through the alias table the same way OCaml does.
That is what removed the accessor-file module-export tail mismatch.

### 2026-04-12 (constant-condition folding in `Lam.if_`)

Ran:

```bash
cargo test --manifest-path compiler-rust/Cargo.toml test_if_then_else_constant_fold
cargo test --manifest-path compiler-rust/Cargo.toml test_print_if
cargo build --release --manifest-path compiler-rust/Cargo.toml
timeout 600 ./scripts/test_lambda_parity.sh -j1 'Import.res|LetUnwrap.res|DerivingAccessorsCurried.res|DerivingAccessorsUncurried.res|big_polyvar_test.res'
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **461/657**
- Stamp-canonicalized parity: **461/657**
- Exact hunks: **1855**
- Stamp-canonicalized hunks: **1855**

Key checkpoints:

- `Import.res`: passes
- `LetUnwrap.res`: **19 hunks**
- `DerivingAccessorsCurried.res`: **1 hunk**
- `DerivingAccessorsUncurried.res`: **1 hunk**
- `big_polyvar_test.res`: **601 hunks**
- next visible frontier: non-constant `Lam.if_` rewrites and the accessor alias/module-export shape

### 2026-04-12 (dynamic import scoping and raw JS code payload lowering)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests -- --nocapture
cargo build --release --manifest-path compiler-rust/Cargo.toml --bin bsc
timeout 180 ./scripts/test_lambda_parity.sh -j1 DynamicImportModuleWithAlias
timeout 180 ./scripts/test_lambda_parity.sh -j1 ExternalExtension
timeout 180 ./scripts/test_lambda_parity.sh -j1 Import
timeout 300 ./scripts/test_lambda_parity.sh -j1 big_polyvar_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **460/657**
- Stamp-canonicalized parity: **460/657**
- Exact hunks: **1859**
- Stamp-canonicalized hunks: **1859**

Key checkpoints:

- `DynamicImportModuleWithAlias.res`: passes
- `ExternalExtension.res`: passes
- `Import.res`: **1 hunk**
- `big_polyvar_test.res`: **601 hunks**
- next visible frontier: `Lam.if_` smart-constructor behavior

### 2026-04-12 (constructor runtime tags, DNone strings, polyvariant names, integer folding)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml lambda::sexp_lambda::tests -- --nocapture
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests -- --nocapture
timeout 180 ./scripts/test_lambda_parity.sh -j1 DictInternalRepresentation
timeout 180 ./scripts/test_lambda_parity.sh -j1 VariantCoercion
timeout 180 ./scripts/test_lambda_parity.sh -j1 big_polyvar_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 div_by_zero_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 gpr_1760_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 jsoo_400_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **426/657**
- Stamp-canonicalized parity: **426/657**
- Exact hunks: **2006**
- Stamp-canonicalized hunks: **2006**

Key checkpoints:

- `DictInternalRepresentation.res`: passes
- `VariantCoercion.res`: passes
- `big_polyvar_test.res`: **602 hunks** (down from **1202**)
- `div_by_zero_test.res`: passes after the lazy divide/mod guard fix
- `gpr_1760_test.res`: passes after the lazy divide/mod guard fix
- `jsoo_400_test.res`: passes after the lazy divide/mod guard fix

### 2026-04-12 (switch names and JS FFI result kinds)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::lowers_blank_js_call_to_object_create -- --exact
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests::keeps_unlabeled_blank_js_call_as_call -- --exact
cargo test --release --manifest-path compiler-rust/Cargo.toml lambda::sexp_lambda::tests::prints_switch_names_consts_and_blocks -- --exact
timeout 180 ./scripts/test_lambda_parity.sh -j1 DictInference
timeout 180 ./scripts/test_lambda_parity.sh -j1 js_array_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **377/657**
- Stamp-canonicalized parity: **377/657**
- Exact hunks: **3723**
- Stamp-canonicalized hunks: **3723**

Key checkpoints:

- `AsInUncurriedExternals.res`: passes
- `DictInference.res`: passes
- `DictPatternMatchingOptimization.res`: passes
- `js_array_test.res`: passes

### 2026-04-12 (routing fixed, first lowerer slice landed)

Ran:

```bash
cargo test --release --manifest-path compiler-rust/Cargo.toml raw_lambda::lower::tests
timeout 180 ./scripts/test_lambda_parity.sh -j1 AsInUncurriedExternals
timeout 180 ./scripts/test_lambda_parity.sh -j1 minimal_test
timeout 180 ./scripts/test_lambda_parity.sh -j1 js_array_test
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **208/657**
- Stamp-canonicalized parity: **208/657**
- Exact hunks: **7862**
- Stamp-canonicalized hunks: **7862**

Key checkpoints:

- `AsInUncurriedExternals.res`: passes
- `minimal_test.res`: passes
- `js_array_test.res`: 207 hunks

### 2026-04-11 (project created from first optimized baseline)

Ran:

```bash
timeout 1800 ./scripts/test_lambda_parity.sh -j1
```

Result:

- OCaml compile coverage: **657/657**
- Rust compile coverage: **657/657**
- Optimized lambda parity: **0/657**
- Parity hunks: **1631**

The script-generated normalized diffs matched the exact baseline exactly, so stamp
canonicalization did not reduce a single failure. This was the starting point for the
optimized-lambda project.
