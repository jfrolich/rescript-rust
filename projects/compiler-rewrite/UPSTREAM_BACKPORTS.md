# Upstream Backports

Status of upstream `rescript-lang/rescript` PRs in the Rust compiler port.

The Rust port lives downstream of OCaml `master`. As upstream lands new
features and bug fixes, they need to be replayed against the Rust
implementations of the parser, typechecker, lambda backend, JS IR, and PPX
layer. This document tracks which PRs have been backported, which were
intentionally deferred, which apply only to the OCaml side, and where the
work landed in the Rust tree.

For each entry: PR number, upstream commit, ported / deferred / N/A status,
the Rust commit(s) that did the port, and a short note on scope or rationale.
The CHANGELOG at the repo root tracks the upstream-style summary; this doc
tracks the Rust-port lens.

## Window covered

13.0.0-alpha.3 → 13.0.0-alpha.4 (upstream commits ~Mar–Apr 2026), captured
during the parity sync session on 2026-04-23 on branch `combined`.

## Compiler-facing PRs

| PR | Upstream commit | Status | Rust commit | Scope |
|----|----|----|----|----|
| [#7887](https://github.com/rescript-lang/rescript/pull/7887) | `f97609381` | **Ported** | `07d1b0e35`, `4972f4fe2` | for-of / for-await-of loops: parser AST (`Pexp_for_of`, `Pexp_for_await_of`), typedtree (`Texp_for_of`, `Texp_for_await_of`), Lambda (`Lfor_of`, `Lfor_await_of`), JS IR (`ForOf`, `ForAwaitOf`), codegen, plus sexp parity stubs |
| [#8207](https://github.com/rescript-lang/rescript/pull/8207) | upstream | **Ported** | `533723b3a` | `.mjs` / `.cjs` runtime extensions in `runtime_module_path` |
| [#8246](https://github.com/rescript-lang/rescript/pull/8246) | upstream | **Ported** | `5e0e2dee6`+ | Parmatch crash on empty record head patterns |
| [#8251](https://github.com/rescript-lang/rescript/pull/8251) | upstream | **Ported** | `7146ab86e` | Untagged variant `typeof` switch null/array guards (`untagged_typeof_object_guard`) |
| [#8296](https://github.com/rescript-lang/rescript/pull/8296) | upstream | **Ported** | `533723b3a` | JSX `vb_match` two-let pattern in `add_default_value_matches` |
| [#8304](https://github.com/rescript-lang/rescript/pull/8304) | `9dbdc0426` | **Deferred** | — | Inline records in external definitions. Substantial parser refactor (702 lines `res_core.ml`, 285 `res_printer.ml`); no current test file uses the new syntax form, so porting wouldn't move parity. Port on demand when test fixtures exercise it. |
| [#8319](https://github.com/rescript-lang/rescript/pull/8319) | `0a75e312f` | **Ported** | `be09d8d75`, `7b6a9ac67` | Optional inline-record fields wrapped in `option<…>` for both type-extension constructors AND `Pstr_exception` (the second handler was missed in the initial port and added in `7b6a9ac67`) |
| [#8343](https://github.com/rescript-lang/rescript/pull/8343) | `cca6205df` | **Ported** | `52cb6eb2f` | `Texp_apply { partial: true }` treated as nonexpansive in `is_nonexpansive_expression` |
| [#8348](https://github.com/rescript-lang/rescript/pull/8348) | `1642c25f5` | **Ported** | `cfa3c2078` | `break` / `continue` keywords: parser AST (`Pexp_break`, `Pexp_continue`), tokens, Lambda (`Lbreak`, `Lcontinue`), JS IR with `Option<String>` label, switch-depth/loop-stack/`ensure_loop_label` plumbing for labeled emission |
| [#8350](https://github.com/rescript-lang/rescript/pull/8350) | `23fc6cc8c` | **Ported** | `effacc7a5` | Preserve JSX prop locations across AST0 round-trip via `[@res.jsxPropLoc]` and `[@res.jsxSpreadLoc]` attributes in `mapper_from0` / `mapper_to0` |
| [#8352](https://github.com/rescript-lang/rescript/pull/8352) | `b642f8c06` | **N/A — already correct** | — | Indentation of `default:` for emitted switch statements. Rust's break/continue printer already matches the fixed behavior; verified `loop_control_test.mjs` byte-identical |
| [#8355](https://github.com/rescript-lang/rescript/pull/8355) | `4bf0cd302` | **Ported** | `4aa0501f3` | `Iterable` / `AsyncIterable` predef types: `STAMP_ITERABLE=61`, `STAMP_ASYNC_ITERABLE=62`, idents, paths, `find_predef_ident` entries, `type_is_builtin_path_but_option` extension |
| [#8359](https://github.com/rescript-lang/rescript/pull/8359) | `c8d05beb0` | **Ported** | `2bc806626` | Propagate expected dict / async value type into lowered `Primitive_dict.make` / `Primitive_promise.unsafe_async` calls via `should_unify_expected_result_before_typing_lowered_apply` and `filter_arrow_for_lowered_apply` |
| [#8369](https://github.com/rescript-lang/rescript/pull/8369) | `fe34ecd76` | **Ported** | `84ae1515a` | Dict spreads: `parse_dict_expr` rewrite with `DictPart` enum + grouping for `dict{...foo, "bar": 2, ...qux}` |
| [#8376](https://github.com/rescript-lang/rescript/pull/8376) | `28a0123d7` | **Ported** | `24c1566cc` | Remove deprecated `%external` extension. Both dispatcher entries and the `handle_external_ext` helper deleted from `binary_ast/ppx.rs` |
| [#8383](https://github.com/rescript-lang/rescript/pull/8383) | `0a51c27b7` | **Partially ported / Deferred** | — (syntax already accepted) | Restore legacy `(. ...)` uncurried syntax with deprecation warning. **Functional acceptance is already in place** — Rust's `parse_parameters`, `parse_parameter`, `parse_argument`, and type-parameter parsing all silently consume a leading dot. **Deferred** is the deprecation Warning #3: Rust's parser currently has no warning emission channel (only `ParserDiagnostic` errors), so emitting `Warnings.Deprecated` requires plumbing a new warning sink through `state.rs` / `diagnostics.rs` |

## Rust-port-only follow-ups (caught while backporting)

These bugs were exposed by the parity runs after backports landed but are
fixes to pre-existing Rust port code, not to upstream PR content.

| Issue | Rust commit | Notes |
|----|----|----|
| `alias_default_value_test` `UndefinedMethod __foo` crash | `3076a0a48` | JSX PPX was prefix-mutating the existing prop pattern (incl. aliases) when a default value was present; OCaml's `pattern_with_safe_label` instead replaces the entire pattern with a fresh `__<label>` var. Rust path now matches. Closes the last Rust crash in the test suite. |
| Dead `reached = true;` after `break;` in `while (true)` | `29f02e4d1` | Mirror OCaml's `Js_output.output_finished:True` from `Lbreak` / `Lcontinue` (lam_compile.ml:1928, 1943). Drop tail of `Lsequence` and skip body of `Llet` when the head/value is an unconditional exit. Gated on the Lambda form, not the JS block predicate, to avoid misclassifying printer-synthesized switch-case `break;` statements. |
| Multi-line array indentation inside `for-of` | `b5657b973` | Mirror `P.paren_group f 1` from `js_dump.ml:1516, 1527`: wrap the `(let i of ITER)` body in `with_indent(1, …)` so a multi-line iterable continues at base+2. |
| Function-body early-return shape (`if cond { … }` → `if (!cond) return; …`) | `02a29344d` | Port `S.if_` rules 5 (`else = [Return _]` → flip + sibling then) and 7 (then ends terminal → drop else into siblings) into `compile_if_effect_block` and `compile_test_return_block_with_fallback`. Narrowly scoped to avoid cascading regressions in pattern-match compilation. |
| Stamp parity merge | `bfcc83e16` | Merge `typechecker-performance` tip — pulled in 117 commits of stamp-parity work and `nondep_supertype` for anonymous functor arguments. |
| In-process DAG scheduler wiring | `5962d8744` | Wire `compile_module_in_process` (which existed but had no callers) into `compile_one`. Branches on `BuildMode::InProcess`, takes a per-spawn registry snapshot, calls the in-process compile path. |

## Tooling / runtime / non-applicable PRs

PRs that affect rewatch, the runtime stdlib, GenType, dependency bumps,
release prep, or docs — these don't need a Rust-compiler-side port. Listed
here so the audit is complete.

| PR | Subject |
|----|----|
| #8277 | Reanalyze: glob pattern support |
| #8287 | `String.localeCompare` ~locales / ~options |
| #8289 | `Intl.Collator.compare` return type |
| #8315 | GenType exotic-identifier handling |
| #8316 | Rewatch: stale-lock handling |
| #8320, #8326, #8327, #8328, #8337, #8341, #8342, #8344, #8362, #8363 | Dep bumps |
| #8331, #8332, #8384 | Release prep |
| #8333 | Stdlib docs |
| #8347 | Rewatch: `--prod` flag |
| #8349 | Rewatch: builds while watcher running |
| #8353 | CHANGELOG update |
| #8354 | Docstring tests |
| #8358 | Rewatch: warnings after atomic-save rebuild |
| #8364 | `Dict.assignMany` etc. (stdlib — propagates via CMI) |
| #8365 | `rescript.json` reading moves to rewatch |
| #8368 | Rewatch: `bsconfig.json` back-compat |
| #8371, #8372, #8373 | Rewatch: progress / output polish |
| #8374 | Rewatch: DAG scheduler |
| #8377 | Belt `xxxUndefined` API removal (runtime) |
| #8379 | Rewatch: feature-gated source dirs |

## Parity outcome after this batch

- Typed-tree parity (canonical stamps): **658 / 659 (99%)**, 0 Rust crashes
- JS output parity: **658 / 660 (99.7%)**

See [../js-output-parity/RALPH_TODO.md](../js-output-parity/RALPH_TODO.md)
for the two remaining JS-output diffs (both semantically equivalent).
