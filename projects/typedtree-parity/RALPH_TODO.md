# Ralph TODO: Typed Tree Parity (with Locations)

## Goal

Achieve 100% parity on the typed tree S-expression output (with locations) between the OCaml and Rust compilers. The test compares `-dtyped-sexp-locs` output from both compilers on all files in `tests/tests/src/`.

## Instructions for Agents

1. **NEVER revert commits made by other agents or humans** - If you think a commit is wrong, document your concerns but DO NOT revert it.
2. **Commit your changes frequently** - Follow the instructions in CLAUDE.md about committing.
3. **Follow the OCaml reference implementation exactly** - This is a 1:1 port. Do not invent new approaches. Read the OCaml code first, then replicate in Rust.
4. **GET TO THE ROOT CAUSE - DO NOT GIVE UP** - When investigating an issue, go deep. Do not stop at surface-level symptoms.
5. **Update this TODO when you discover work is already done** - Before starting a task, verify its current state.
6. **One task per session** - Complete one task, commit, stop. Each new task should start with a fresh context.

---

## ⚠️ ALWAYS USE TIMEOUTS — THE RUST COMPILER WILL INFINITE LOOP

The Rust type checker is incomplete and **WILL hang/infinite loop** on many inputs. You MUST wrap every invocation of the Rust compiler (`bsc`, test scripts, cargo test) with a timeout. **No exceptions.**

- **Single file tests:** `timeout 10 ./compiler-rust/target/release/bsc ...`
- **Test scripts:** `timeout 300 ./scripts/test_typedtree_parity.sh ...`
- **Cargo tests:** `timeout 120 cargo test ...`

If you run the Rust compiler without a timeout, it WILL hang indefinitely and block your entire session. The OCaml compiler does NOT have this problem — only the Rust compiler needs timeouts.

---

## How to Test

```bash
# Build the Rust compiler
cargo build --manifest-path compiler-rust/Cargo.toml --release

# Run the typed tree parity test suite (compares -dtyped-sexp output)
timeout 300 ./scripts/test_typedtree_parity.sh

# Test a single file (fastest for iteration — always use timeout!)
timeout 10 ./scripts/test_typedtree_parity.sh tests/tests/src/a.res

# Test files matching a pattern
timeout 60 ./scripts/test_typedtree_parity.sh "Core_Array"

# Quick mode (stop on first failure, show diff)
timeout 300 ./scripts/test_typedtree_parity.sh --quick

# Skip rewatch build (if already built)
timeout 300 ./scripts/test_typedtree_parity.sh --no-build

# With locations (ultimate goal)
timeout 300 ./scripts/test_typedtree_parity.sh --with-locs

# Manual comparison of a single file (ALWAYS use timeout on the Rust compiler)
echo 'let x = 1' > /tmp/test.res
./_build/install/default/bin/bsc -dtyped-sexp-locs /tmp/test.res 2>/tmp/ocaml.sexp
timeout 10 ./compiler-rust/target/release/bsc -dtyped-sexp-locs /tmp/test.res 2>/tmp/rust.sexp
diff /tmp/ocaml.sexp /tmp/rust.sexp
```

The test script:
1. Builds the test project with `rewatch` (using the OCaml compiler)
2. Gets compiler args for each file via `rescript compiler-args`
3. Runs both OCaml and Rust `bsc -dtyped-sexp` on each file
4. Diffs the stderr output (sexp goes to stderr)
5. Reports pass/fail counts

The `-dtyped-sexp` flag outputs the typed tree without locations. The `-dtyped-sexp-locs` flag includes locations. Our goal is parity on the **with-locs** variant.

---

## Current Status

**Last Updated:** 2026-02-09

|  | Status |
|--|--------|
| OCaml compiles | 657/657 |
| Rust compiles | 651/657 (6 fail) |
| Parity match (-dtyped-sexp-locs) | 317/651 (48.7%) |

**Task Progress:** 39/39 complete

**Task Checklist:**
- [x] Match OCaml `Mtype.nondep_supertype` non-path functor-application specialization for type components, not just values: when specializing functor results with argument manifest aliases, also rewrite `Sig_type` declarations (`type_params`, `type_kind`, `type_manifest`, and `type_inlined_types`) plus `Sig_typext` payload types. This ports the missing `Ctype.nondep_type_decl`/`nondep_extension_constructor` effect in the Rust non-path specialization path, fixing aliases like `type key = Ord.t` so calls such as `IntMap.add(k, v, acc)` can unify `int` with `IntMap.key`. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 650 -> 651 (failures 7 -> 6), `Parity` 317 -> 317 (with one additional compiled file: `inline_map2_test.res` moved from Rust failure to parity-only diff).
- [x] Match OCaml `typedecl.transl_constructor_arguments` spread handling for variant constructor record args (`Pcstr_record`): when spread labels resolve to record types, expand them before building constructor declarations; and when a single spread label (`...t`) does not resolve to a record, reinterpret it as an object-typed tuple argument (`Ptyp_object [Oinherit t]`) instead of keeping a synthetic `"..."` inline-record label. This ports the OCaml object-spread fallback used for ambiguous constructor spreads and avoids treating object spreads as inline records in Rust. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 649 -> 650 (failures 8 -> 7), `Parity` 317 -> 317 (with one additional compiled file; `object_type_spreads.res` now parity-only diff).
- [x] Match OCaml `ctype.copy_type_desc` instantiation behavior for object/package descriptors by extending Rust `copy_type_cached` to copy `Tobject`, `Tfield`, `Tnil`, and `Tpackage` nodes instead of returning shared references. This prevents object-typed external function schemas (notably `Js.Obj.keys`) from being specialized in-place across call sites and removes the `ExprTypeClash` compile failures in `gpr_1409_test.res` and `stdlib/Stdlib_ObjectTests.res` (now both compile, parity-only diffs). Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 647 -> 649 (failures 10 -> 8), `Parity` 311 -> 317.
- [x] Match OCaml let-module scoping and declaration-bound type-variable globalization for first-class module unpack flows: thread declaration `type_variables` through type declaration translation (`typemod`), globalize `used_variables` in `transl_type` like OCaml `typetexp.globalize_used_variables`, and in `type_letmodule` abstract module-rooted paths from surrounding env value types (not just the body/expected expression type) before outer unification. This prevents local `X.key` paths from escaping through captured values in `let module X = unpack(...)` bodies and moves `defunctor_make_test.res` from Rust compile failure to parity-only diff. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 646 -> 647 (failures 11 -> 10), `Parity` 311 -> 311 (with one additional compiled file).
- [x] Match OCaml package-modtype identity and let-module alias resolution for first-class module flows: in `typecore::transl_type` (`Ptyp_package`), resolve unqualified module-type paths via the environment’s canonical modtype identifier (`find_modtype_with_id`) instead of allocating fresh path identities per occurrence; and in `type_letmodule`, materialize direct identifier aliases (`module M = List`, including constrained direct idents) to resolved signatures before extending the body env so member types like `M.t` expand consistently under opened modules (e.g. `open Belt`). This moves `global_module_alias_test.res`, `module_alias_test.res`, `module_missing_conversion.res`, `module_parameter_test.res`, and `test_non_export.res` from Rust compile failure to parity-only diff (with `defunctor_make_test.res` temporarily regressed later), and improves deterministic full-run totals (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 643 -> 647 (failures 14 -> 10), `Parity` 308 -> 308.
- [x] Port OCaml local-exception typing and dict predef constructor/label availability: implement `Pexp_letexception` typing by translating the exception constructor, extending the body environment with its `CstrExtension`, and emitting `Texp_letexception` (matching OCaml `typecore.ml` / `Typedecl.transl_exception` flow); also mirror OCaml `Predef.decl_dict` in Rust predef env by adding `dict` as a record type with optional magic field `dictValuesType: option<'a>` and registering record labels from predef types so dict-pattern label disambiguation can route through that field. This removes the Rust `NotAVariantType` local-exception failure in `large_record_duplication_test.res` (now compiles, parity-only diff). Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 642 -> 643 (failures 15 -> 14), `Parity` 307 -> 308.
- [x] Fix Rust typedtree compile crashes caused by non-owning unify env state and alias-cycle re-entry in `ctype` module-type resolution. Replaced `UnifyState`'s raw `*const Env` with an owned `Env` snapshot (`set_env` now clones), so nested typing no longer leaves dangling env pointers that crashed in `Env::find_modtype`/`find_module`; also keep module-path visit markers for the full `resolve_module_signature_through_cmi` / `resolve_module_type_through_env_path` walk so alias chains cannot re-enter cycles. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 621 -> 626 (failures 36 -> 31), `Parity` 302 -> 303 with five additional compiled files moved from Rust failure to parity-only diff (`bs_array_test.res`, `caml_compare_test.res`, `js_nullable_test.res`, `js_string_test.res`, `nested_obj_test.res`).
- [x] Continue reducing remaining Rust compile failures (31), starting with the current deterministic first failures in module/FFI-heavy files (`bs_map_set_dict_test.res`, `bs_poly_map_test.res`, `defunctor_make_test.res`) and prioritizing shared root causes before parity-only diffs. Ported OCaml-aligned type-constructor resolution/arity handling for `Ptyp_constr` (canonical env-resolved paths + `_` expansion for multi-arity constructors), fixed canonical module-path reuse in `resolve_module_lid`, and tightened let-module local type-path abstraction to rewrite freshly-created let-module-rooted paths before outer unification. This moves `bs_poly_map_test.res` and `defunctor_make_test.res` from Rust compile failure to parity-only diff (with `bs_map_set_dict_test.res` already parity-only). Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 626 -> 629 (failures 31 -> 28), `Parity` 303 -> 305.
- [x] Match OCaml object-row unification behavior in `ctype::unify_fields` for open object types: when `Tobject` field chains hit a row variable (`Tvar`), delegate to regular unification so the open row can link to the concrete `Tfield` chain (instead of requiring exact field-shape equality). This fixes function-call unification for open-object externals (e.g. `Js_obj.keys`) and moves `ffi_js_test.res`, `js_obj_test.res`, `reasonReact.res`, `stdlib/Stdlib_TempTests.res`, and `stdlib/Test.res` from Rust compile failure to parity-only diff. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 629 -> 634 (failures 28 -> 23), `Parity` 305 -> 305 with 5 additional compiled files.
- [x] Continue reducing remaining Rust compile failures (23), prioritizing the current failure bucket (`forwardRef_regress.res`, `functor_ffi.res`, `global_module_alias_test.res`, `gpr_1409_test.res`, `gpr_5753.res`, `inline_map2_test.res`, `inline_record_test.res`, `js_json_test.res`, `json_decorders.res`, `large_record_duplication_test.res`, `mario_game.res`, `module_alias_test.res`, `module_missing_conversion.res`, `module_parameter_test.res`, `object_type_spreads.res`, `record_regression.res`, `record_with_test.res`, `recursive_react_component.res`, `res_debug.res`, `stdlib/Stdlib_ObjectTests.res`, `string_unicode_test.res`, `test_non_export.res`, `uncurried_default.args.res`) and shared root causes before parity-only diffs. Ported OCaml-style record definition reconstruction in `typecore::type_record` (build definitions over full labels when available; synthesize missing optional `None`; preserve spread/object placeholder behavior), and aligned lambda record conversion indexing with OCaml field-order semantics for `Kept`/record allocation. This removes the Rust aborts in `record_regression.res` and `record_with_test.res` (both now compile, parity-only), while keeping spread-heavy files compiling. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 634 -> 636 (failures 23 -> 21), `Parity` 305 -> 306.
- [x] Continue reducing remaining Rust compile failures (21), prioritizing the current failure bucket (`forwardRef_regress.res`, `functor_ffi.res`, `global_module_alias_test.res`, `gpr_1409_test.res`, `gpr_5753.res`, `inline_map2_test.res`, `inline_record_test.res`, `js_json_test.res`, `json_decorders.res`, `large_record_duplication_test.res`, `mario_game.res`, `module_alias_test.res`, `module_missing_conversion.res`, `module_parameter_test.res`, `object_type_spreads.res`, `recursive_react_component.res`, `res_debug.res`, `stdlib/Stdlib_ObjectTests.res`, `string_unicode_test.res`, `test_non_export.res`, `uncurried_default.args.res`) and shared root causes before parity-only diffs. Ported OCaml `res_scanner.ml` single-quote UTF-8 codepoint handling in the Rust scanner (`'` token branch): after opening quote, decode a codepoint from scanner bytes, accept only when followed by closing quote, and restore scanner state on fallback to `SingleQuote` (matching OCaml `scanner.ch/offset/offset16` restore behavior). Also switched scanner byte storage to Latin-1 byte values (one per scanner char) so UTF-8 decode runs on the same byte representation OCaml uses. This moves `gpr_5753.res`, `res_debug.res`, and `string_unicode_test.res` from Rust parse failures to Rust compile success (`gpr_5753.res` now parity pass; the other two are parity-only diffs). Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 636 -> 639 (failures 21 -> 18), `Parity` 306 -> 307.
- [x] Continue reducing remaining Rust compile failures (18), prioritizing the current failure bucket (`forwardRef_regress.res`, `functor_ffi.res`, `global_module_alias_test.res`, `gpr_1409_test.res`, `inline_map2_test.res`, `inline_record_test.res`, `js_json_test.res`, `json_decorders.res`, `large_record_duplication_test.res`, `mario_game.res`, `module_alias_test.res`, `module_missing_conversion.res`, `module_parameter_test.res`, `object_type_spreads.res`, `recursive_react_component.res`, `stdlib/Stdlib_ObjectTests.res`, `test_non_export.res`, `uncurried_default.args.res`) and shared root causes before parity-only diffs. Matched OCaml JSX component lowering intent for source-compilation fallback in `compiler-rust/src/driver.rs`: detect `@react.component` bindings that specifically require lowering (`React.forwardRef(...)` wrappers and recursive component bindings) and run `parser::jsx_ppx::transform_structure` before builtin PPX rewrites only for those shapes. This follows OCaml’s `Ppx_entry.rewrite_implementation` JSX-before-builtin ordering while avoiding unrelated JSX rewrites in files that already type-check in source mode. Files moved from Rust compile failure to parity-only diff: `forwardRef_regress.res`, `recursive_react_component.res`. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 639 -> 641 (failures 18 -> 16), `Parity` 307 -> 307.
- [x] Continue reducing remaining Rust compile failures (16), prioritizing the current failure bucket (`functor_ffi.res`, `global_module_alias_test.res`, `gpr_1409_test.res`, `inline_map2_test.res`, `inline_record_test.res`, `js_json_test.res`, `json_decorders.res`, `large_record_duplication_test.res`, `mario_game.res`, `module_alias_test.res`, `module_missing_conversion.res`, `module_parameter_test.res`, `object_type_spreads.res`, `stdlib/Stdlib_ObjectTests.res`, `test_non_export.res`, `uncurried_default.args.res`) and shared root causes before parity-only diffs. Matched OCaml `typemod` non-path functor-application intent for semantic module-type extraction in `Pmod_apply`: keep applicative path substitution when the argument has a path, and for non-path arguments (e.g. structure args) specialize functor-result value types using argument manifest aliases (OCaml `Mtype.nondep_supertype` effect for this case), rather than leaving unresolved parameter-member paths in the result. This moves `functor_ffi.res` from Rust compile failure to parity-only diff. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 641 -> 642 (failures 16 -> 15), `Parity` 307 -> 307 with one additional compiled file.
- [x] Match OCaml path-based type alias expansion for dotted module aliases in `ctype` by resolving module signatures through both local env aliases (`Mty_alias`/`Mty_ident`) and CMI alias chains (including non-`Pident` alias paths like `Belt.Array`). This fixes `A.t` vs `array` unification clashes in function calls and moves `belt_hashmap_test.res`, `belt_hashset_int_test.res`, and `belt_sortarray_test.res` from Rust compile failure to parity-only diff. Deterministic full run (`timeout 300 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1`): `Rust bsc` 614 -> 621 (failures 43 -> 36); `Parity` 303 -> 302 with 7 additional compiled files.
- [x] Match OCaml `parse_type_constructor_declarations` continuation behavior in the Rust parser: after a `type ... = | ...` variant, continue parsing constructors only for `|` or doc-comment-then-`|` (not bare `@...`). This fixes a parser over-consumption bug where top-level attributes like `@val external` were incorrectly eaten as constructor attrs, producing false "consecutive statements" parse errors. Updated `parse_constructors` in `compiler-rust/src/parser/module.rs` to mirror OCaml’s first-constructor + bar-gated continuation flow. Files moved from Rust compile failure to parity-only diff include `bs_ignore_test.res`, `bs_ignore_effect.res`, and `reactDOM.res`; full `--with-locs --no-build --parallel 1` totals improved (`Rust bsc`: 611 -> 614, failures: 46 -> 43; `Parity`: 303 -> 303 with 3 additional compiled files).
- [x] Match OCaml path-based alias expansion in `ctype::try_expand_head`: only use direct env lookup for `Pident` type paths, and skip `env.lookup_type` for qualified `Pdot` paths so local leaf-name declarations (`type t = ...`) cannot hijack qualified aliases like `Belt.Array.t`. This fixes `UntaggedVariants.res` Rust compilation (`ExprTypeClash` -> compile success) and improves full `--with-locs --no-build --parallel 1` totals (`Rust bsc`: 602 -> 611, failures: 55 -> 46; `Parity`: 302 -> 303).
- [x] Match OCaml applicative functor result substitution in `typemod` (`path_of_module` + `Subst.add_module`/`Subst.modtype`) for parsed `Pmod_apply`: when extracting semantic module types from functor applications, substitute functor-parameter module-path references in the result type with the argument module path. This fixes unqualified constructor disambiguation through applied-functor aliases (`variant.res`: Rust compile failure `NotAVariantType` -> Rust compile success, now parity-only diff) and improves full `--with-locs --no-build` totals (`Rust bsc`: 600 -> 602, failures: 57 -> 55).
- [x] Match OCaml `expand_head` resolution behavior for qualified type paths in `ctype::try_expand_head`: keep leaf-name fallback (`find_type_decl(head_name)`) for `Pident` only, and do not use it for `Pdot` paths. This removes a non-OCaml alias resolution path that caused infinite `unify -> expand_head` recursion (observed as Rust timeout/hang) and moves `ExternalExtension.res` from Rust compile failure to parity-only diff (`timeout 60 ./scripts/test_typedtree_parity.sh --with-locs --no-build --parallel 1 tests/tests/src/ExternalExtension.res`: Rust `0 -> 1` pass).
- [x] Continue reducing Rust compile failures by finding other unification recursion sites triggered by non-OCaml alias expansion paths (`ctype::unify`/`expand_head`), prioritizing currently-timing-out files. Removed the non-OCaml name-only `Pident` fallback in `ctype::try_expand_head` so alias expansion stays path-based; this eliminates nullable alias-expansion recursion in timed-out files and moves `js_nullable_test.res` and `float_test.res` from Rust timeout to full parity pass (`timeout 60 ./scripts/test_typedtree_parity.sh --with-locs --no-build tests/tests/src/js_nullable_test.res` and `tests/tests/src/float_test.res`: Rust `0 -> 1`, Parity `0 -> 1`).
- [x] Continue reducing remaining timeout/crash files in typedtree parity (e.g. `belt_list_test.res`, `js_math_test.res`, `test_list.res`) by tracing the next non-OCaml recursion/crash root cause in `ctype::unify`/`expand_head`. Root cause identified for the remaining timeout case (`belt_list_test.res`): Rust typedtree sexp output wrote Latin-1 bytes to stderr one character at a time (many syscalls), unlike OCaml's single `Format.fprintf` write. Buffering bytes in `write_latin1_line` restores OCaml-like output behavior/performance and moves the file from Rust timeout failure to compiled parity-diff status. Full `--with-locs --no-build` totals improved (`Rust bsc`: 599 -> 600, failures: 58 -> 57; `Parity`: 301 -> 302).
- [x] Match OCaml `@deriving(abstract)` behavior for non-record declarations in the Rust PPX: keep non-record type declarations unchanged (including alias manifests) and parse `{abstract: light}` config so light-mode accessors keep original field names. This fixes Rust compilation for `bs_abstract_test.res` and moves the file from Rust compile failure to parity-only diff (`--with-locs --no-build tests/tests/src/bs_abstract_test.res`: Rust `0 -> 1` pass).
- [x] Port OCaml `Pexp_newtype` typing behavior in `typecore`: enter a temporary abstract type declaration in the environment, type the body without an early expected-type constraint, then copy and rewrite the result type by replacing `Tconstr(Pident newtype_id)` with a fresh type variable (matching OCaml's `Subst.type_expr` + `link_type` walk). This fixes Rust compilation for `bench.res` (`--with-locs --no-build tests/tests/src/bench.res`: Rust `0 -> 1` pass), and the deterministic sequential first failure moves from `src/bench.res` at `50/657` to `src/bs_abstract_test.res` at `87/657`.
- [x] Match OCaml recursive `let` prebinding behavior for constrained variable patterns in `type_let`: predeclare recursive value identifiers through `Ppat_constraint` wrappers (and alias-on-`_` form) before typing RHS expressions, so self-references like `let rec v0: t3<_> = #A({field: v0})` resolve as values instead of falling through to `UndefinedMethod`. This fixes Rust compilation for `unboxed_use_case.res` and improves full `--with-locs --no-build` totals (`Rust bsc`: 567 -> 569, failures: 90 -> 88; `Parity`: 291 -> 291 with additional compiled files).
- [x] Match OCaml `transl_modtype`/`Env.scrape_alias` behavior for module-type identifiers in `typemod`: keep `Pmty_ident` as `MtyIdent(path)` (instead of falling back to empty signatures), resolve `Mty_ident` through local/persistent `Sig_modtype` paths, and preserve `Tstr_modtype` bodies when extracting structure signatures from typed module expressions. This unblocks functor-parameter lookups through dotted modtype paths (`UseCase.Layer`, `Belt.Id.Comparable`) and improves full `--with-locs --no-build` compilation (`Rust bsc`: 565 -> 568, failures: 92 -> 89).
- [x] Port OCaml module-type extraction behavior for structure-local aliases and functors in `typemod`: resolve `Tmod_ident` through environment/persistent signature scraping, thread an evolving local env while extracting `Tmod_structure` items, and extract `Tmod_functor`/`Tmod_apply` result module types. This unblocks nested module alias/functor member lookup (`coercion_module_alias_test.res` now compiles with Rust) and improves full `--with-locs --no-build` totals (`Rust bsc`: 560 -> 565, `Parity`: 291 -> 292).
- [x] Match OCaml `expand_head` behavior in `type_application` when handling labeled args for aliased function types (`type t = (~x: int, ~y: int) => int`). Expand the head type before arrow/label matching (and optional-tail skipping) so applications like `f(~y=b, ~x=a)` don't fall into unknown-arg fallback. This fixes `arity.res` compilation and improves full `--with-locs --no-build` results (`Rust bsc`: 556 -> 561, `Parity`: 289 -> 291).
- [x] Port OCaml `Pmod_unpack` typing path in `typemod`: derive unpack module types from `expand_head` package types (`Tpackage`) and preserve `Psig_type` manifests/`Psig_modtype` items in `translate_module_type_to_decl`, then qualify module-signature type paths when entering `Pstr_module` bindings. This fixes the `let module X = unpack(v.compare)` compilation failure (`UndefinedMethod "X.compare"` in `defunctor_make_test.res`) and improves full `--with-locs` compilation (`Rust bsc`: 557 -> 559).
- [x] Match OCaml `@deriving(accessors)` variant accessor location behavior in PPX output by emitting generated value/pattern/expression/signature item locs as `Location.none` while preserving constructor-name locations on `Located` identifiers and `Typ.arrows ~loc` for signature arrow nodes (`DerivingAccessorsCurried.res` parity fixed; `Parity`: 293 -> 295 in the latest full `--with-locs --no-build` run).
- [x] Fix qualified constructor typing + trailing optional-arg consumption in `type_application` so dict-pattern matches compile instead of failing with `PatternTypeClash`.
- [x] Reduce remaining Rust compile failures (67), prioritizing root causes in `UndefinedMethod`, `ExprTypeClash`, and `PatternTypeClash`.
- [x] Preserve nested module member visibility for awaited/unpacked modules in extracted signatures, and keep declared signatures for recursive self-alias modules (`module rec M = M`) to avoid `UndefinedMethod` regressions (Rust compile failures: 65 -> 63).
- [x] Port OCaml's variant spread pattern rewrite in `type_pattern` (`Ppat_type` expansion + alias type override) so `...a as a` binds the spread source type (Rust compile failures: 63 -> 61).
- [x] Resolve `Mty_ident` module types through modtype expansion (matching OCaml `Env.scrape_alias` order) before module-path fallback, so opened submodules constrained by modtypes expose their members (`inner_call.res`, Rust compile failures: 61 -> 60).
- [x] Port OCaml external FFI arg-spec behavior for erased `@as(...) _` parameters (including trailing `Extern_unit` insertion) and keep primitive externals untouched during extension-only rewriting so `pval_prim` encodes constants correctly; also emit typedtree sexp with Latin-1 byte output for primitive blobs (`AsInUncurriedExternals.res` parity).
- [x] Port OCaml first-class module unpack typing in patterns: translate `Ptyp_package` to `Tpackage`, type `Ppat_unpack` with `Tpat_unpack` extras, allow module unpack patterns in `let` and function parameters, and register package-backed module bindings in env (deterministic sequential compile failures: 61 -> 59, `UndefinedMethod`: 20 -> 16).
- [x] Port OCaml `extract_label`-style argument matching in `type_application` (label-name lookup across remaining args + omitted-parameter reconstruction), fixing uncurried mixed-label applications in `UncurriedAlways.res` (Rust compile failures: 106 -> 105).
- [x] Predeclare `Pstr_type` names in the type env before translating constructor argument types (matching OCaml recursive typedecl binding order), and tighten qualified-type lookup to avoid leaf-name fallback for `Pdot` paths. Also qualify module-signature type paths before constructor lookup. This fixes recursive module constructors resolving to outer `t` in `UntaggedVariants.res` and improves overall compilation (`Rust bsc`: 552 -> 559, `Parity`: 291 -> 293).
- [x] Match OCaml include-signature propagation when extracting module types from typed `Tmod_structure`: resolve `Tstr_include` identifier modules through the current environment (not just already-accumulated local signature items), so transitive included values stay visible (`acyc/x.res` no longer fails with `UndefinedMethod "v"`). Full `--with-locs --no-build` run: `Rust bsc` 554 -> 559, `Parity` 293 -> 296.
- [x] Allow variant type constructors to start after leading doc/attribute blocks in `type ... =` declarations by classifying `@...`/doc-comment + `|` as variant syntax and attaching those leading attrs to the first constructor (`arith_syntax.res` now parses and compiles with Rust `bsc` instead of failing with parser errors).

**Previous milestones completed:**
- Parser AST structure: 100% parity (sexp-locs 1196/1196)
- Syntax tests: 506/506 (100%)
- CMI loading and module resolution (0.2)
- Pipe-to-tuple distribution in desugar_pipe
- Path substitution for CMI-loaded modules (Tconstr rewriting)
- Module alias path rewriting (Belt.Array -> Pdot, not Pident)
- Qualified module paths for opened sub-modules (md_path on ModuleDeclaration)
- Fix _include_ path for non-ident include statements
- Fix type alias expansion: copy manifests during expansion to prevent corruption
- Propagate arity in arrow type unification
- Module-qualified constructor result typing + implicit trailing optional-arg consumption in applications (Rust compile failures: 71 -> 67)
- Recover semantic module types for `Pmod_unpack`/`await` module bindings and `let module` fallback resolution (Rust compile failures: 67 -> 65)
- Preserve unpacked-module type hints in extracted signatures and keep recmodule self-alias declarations from dropping explicit signatures (Rust compile failures: 65 -> 63)
- Port OCaml-style variant spread pattern expansion/alias typing for `...Type as x` patterns (Rust compile failures: 63 -> 61)
- Resolve `Mty_ident` via modtype expansion before module lookup in module-signature member resolution (`inner_call.res`, Rust compile failures: 61 -> 60)
- Match OCaml external primitive encoding and typedtree byte-string output for erased `@as(...) _` externals (`AsInUncurriedExternals.res`)

---

## Architecture Overview

```
ReScript Source (.res)
  -> Parser (compiler-rust/src/parser/)
  -> Parsetree (surface AST)
  -> PPX transforms (compiler-rust/src/binary_ast/ppx.rs)
  -> Parsetree (transformed)
  -> Type Checker (compiler-rust/src/types/)
  -> Typedtree (typed AST)    <-- THIS IS WHAT WE'RE COMPARING
  -> Lambda IR -> JS IR -> JavaScript
```

The type checker takes a Parsetree and produces a Typedtree. The Typedtree is the AST annotated with:
- Resolved paths (`Path.t`) for all identifiers
- Type expressions (`type_expr`) for all expressions and patterns
- Environments (`Env.t`) at each node
- Source locations (`Location.t`) at each node

---

## Reference Files

### OCaml (the reference implementation to match)

| File | Purpose |
|------|---------|
| `compiler/ml/typedtree.ml` | Typed AST implementation |
| `compiler/ml/typedtree.mli` | Typed AST type definitions — **primary reference** |
| `compiler/ml/sexp_typedtree.ml` | S-expression printer — **what we must match** |
| `compiler/ml/typecore.ml` | Expression/pattern type checking |
| `compiler/ml/typemod.ml` | Module type checking |
| `compiler/ml/typedecl.ml` | Type declaration checking |
| `compiler/ml/typetexp.ml` | Type expression translation |
| `compiler/ml/ctype.ml` | Core type operations / unification |
| `compiler/ml/env.ml` | Type environment |
| `compiler/ml/types.ml` | Core type representation |
| `compiler/ml/types.mli` | Core type representation interface |
| `compiler/ml/btype.ml` | Basic type operations |
| `compiler/ml/includemod.ml` | Module signature matching |
| `docs/TYPING.adoc` | Overview of the type checker architecture |

### Rust (our implementation)

| File | Purpose |
|------|---------|
| `compiler-rust/src/types/mod.rs` | Module root, re-exports |
| `compiler-rust/src/types/typedtree.rs` | Typed AST definitions |
| `compiler-rust/src/types/sexp_typedtree.rs` | S-expression printer (must match OCaml's) |
| `compiler-rust/src/types/typecore.rs` | Expression/pattern type checking |
| `compiler-rust/src/types/typemod.rs` | Module type checking |
| `compiler-rust/src/types/context.rs` | TypeContext with arena-based allocation |
| `compiler-rust/src/types/ctype.rs` | Core type operations (unify, generalize) |
| `compiler-rust/src/types/env.rs` | Type environment |
| `compiler-rust/src/types/type_expr.rs` | Type expression representation |
| `compiler-rust/src/types/decl.rs` | Type/value declarations |
| `compiler-rust/src/types/btype.rs` | Basic type operations |
| `compiler-rust/src/types/path.rs` | Module paths |
| `compiler-rust/src/types/asttypes.rs` | Common AST types |
| `compiler-rust/src/types/includemod.rs` | Signature matching |
| `compiler-rust/src/types/variance.rs` | Variance analysis |

---

## Key Areas for Improvement

### Rust Compilation Failures (59 files)

59 files fail to compile with the Rust type checker. Top error patterns:

| Error | Count | Description |
|-------|-------|-------------|
| ExprTypeClash | 28 | Function call and general type mismatches |
| UndefinedMethod | 16 | Module field access still falling back to unresolved value lookup |
| NotAVariantType | 6 | Variant type resolution |
| Parse errors | 5 | Unsupported syntax |
| Other/Crash | 4 | Runtime aborts/panics and remaining non-bucketed type errors |

### Parity Diff Categories (295 files with diffs)

Of the 598 files that compile, 303 match and 295 differ. Diff categories (overlap):

| Category | Files | Description |
|----------|-------|-------------|
| Module path | 229 | Pident vs Pdot differences |
| Cycle detection | 121 | OCaml prints `<cycle>`, Rust expands shared types |
| Arity (Some N vs None) | 66 | Arrow type arity annotations missing |
| Tvariant | 43 | Polymorphic variant type inference |
| Belt alias | 21 | Belt module alias name resolution |
| Stdlib prefix | 23 | Missing Pdot(Pident("Stdlib"), X) |
| Texp_open | 13 | Missing local open expression nodes |
| Pervasives prefix | 14 | Missing Pdot(Pident("Pervasives"), X) |
| Partial/Total | 11 | Pattern exhaustiveness |
| External encoding | 3 | External attribute string encoding |

### Root Causes (Highest Impact)

1. **Cycle detection in sexp output** (121 files): OCaml's `instance()` creates shared type nodes; the sexp printer detects these and prints `<cycle>`. Rust creates fresh nodes so sharing patterns differ. Fixing this requires either implementing OCaml-style type sharing in `instance()` or a two-pass sexp printer.

2. **Arrow type arity** (66 files): When creating arrow types during type checking, arity annotations (`Some(N)`) are not always propagated. Fix: ensure arity is set on all Tarrow types created during type inference.

3. **Module path qualification** (229 files): Various issues with module path resolution including local module paths, Belt alias resolution, and missing type path rewriting in various contexts.

### CMI File Loading (Task 0.2) ✅

Infrastructure for loading `.cmi` files (compiled module interfaces) has been implemented. This is critical for resolving external module references.

---

## Debugging Tips

1. **Start with simple files** - Test with `let x = 1`, `let f = x => x`, `type t = int` before complex files
2. **Compare sexp output side by side** - Pipe through `diff -u` for readable diffs
3. **Check both with and without locations** - Structural issues show up in both modes, location issues only in with-locs mode
4. **Read the OCaml type checker code** - When the Rust output is wrong, trace through the OCaml code to understand what it should produce

---

## Notes

- The OCaml sexp printer skips `Env.t` (never prints environments) and `Types.signature` (type field in structures)
- Ident stamps are skipped in both printers (only names are printed) for determinism
- `type_expr` is printed by following `Tlink` chains via `Btype.repr` in OCaml
- The `with_locs` parameter controls whether locations are included — both printers support this toggle
- `Texp_for` uses `Parsetree.pattern` (not `Typedtree.pattern`) for the loop variable pattern in OCaml
