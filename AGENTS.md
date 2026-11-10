# AGENTS.md

This file provides guidance to AI coding assistants when working with code in this repository.

## ⚠️ CRITICAL: NEVER use `rm -rf` on directories

**An agent previously deleted the entire repository with `rm -rf`.** This is catastrophic and unrecoverable.

Rules:
- **NEVER run `rm -rf` on any directory** unless the user explicitly asks you to delete that specific directory
- **NEVER run `rm -rf` with variables** (e.g., `rm -rf $DIR`) — variable expansion bugs can delete wrong paths
- To clean caches or temp files, remove specific files by name (e.g., `rm /path/to/specific/file`)
- If you need to clear a cache directory, use `rm /path/to/cache/*.ext` with a specific extension, NOT `rm -rf /path/to/cache/`
- When in doubt, use `ls` first to see what you'd be deleting, and ask the user before proceeding

## ⚠️ Repository Setup - READ FIRST

This repository has two Git remotes configured:

- `origin` → `rescript-lang/rescript` (upstream public repo - **READ ONLY**)
- `private` → `jfrolich/rescript-rust` (private development repo)

**IMPORTANT: Only push to the `private` remote.** Never push directly to `origin`.

```bash
# Push changes to private repo
git push private

# Pull updates from upstream (if needed)
git fetch origin
git merge origin/master
```

## Quick Start: Essential Commands

```bash
# Build the platform toolchain (default target)
make

# Build the platform toolchain + stdlib
make lib

# Build the platform toolchain + stdlib and run tests
make test

# Format code
make format

# Check formatting
make checkformat
```

The Makefile’s targets build on each other in this order:

1. `yarn-install` runs automatically for targets that need JavaScript tooling (lib, playground, tests, formatting, etc.).
2. `build` (default target) builds the toolchain binaries (all copied into `packages/@rescript/<platform>/bin`):
   - `compiler` builds the dune executables (`bsc`, `rescript-*`, `ounit_tests`, etc.), including upstream's OCaml build system (`rescript-ocaml`).
   - `rewatch` builds the Rust build system and CLI with the Rust compiler linked in (`rescript`, the default).
3. `lib` uses those toolchain outputs to build the runtime sources.
4. Test targets (`make test`, `make test-syntax`, etc.) reuse everything above.

## ⚠️ Critical Guidelines & Common Pitfalls

- **COMMIT YOUR CHANGES** - After completing ANY meaningful work (bug fix, feature, refactor, parity improvement), you MUST commit immediately. Do not leave work uncommitted. Do not move on to the next task without committing first. This is the most important rule.

- **Do NOT reinvent solutions—follow the reference implementation** - This is a 1:1 port from OCaml to Rust. When implementing any feature, ALWAYS look at the corresponding OCaml code first. Do not invent new algorithms, new approaches, or "better" solutions. The goal is identical behavior, which means replicating the OCaml logic as closely as possible in idiomatic Rust. If you're tempted to do something differently, stop and ask yourself: "How does OCaml do this?" Then do that.

- **No Rust-only parity compensations or lazy-behavior hacks** - If OCaml gets a typedtree shape, type-node sharing pattern, path shape, row mutation, or traversal order from lazy evaluation, Rust must implement the same lazy behavior. Do NOT add force-suppression flags, path-spelling equivalence, representative rewrites, signature-content heuristics, mode-dependent canonical behavior, "top-level only" rewrites, post-hoc path normalization, selective deep/shallow mutation, or ad hoc guards that merely reproduce one observed diff. Parity wins from these tricks are invalid because they create a second Rust algorithm. The correct fix is to model the OCaml mechanism directly: the same Env/Ctype API boundary, captured environment, substitution scope, lazy component thunk, mutation point, and force order. If Rust currently has an eager helper where OCaml uses laziness, refactor toward OCaml's lazy algorithm instead of layering a Rust-only workaround on top.

- **Correctness over local parity — never revert verified OCaml-aligned changes** - If you have verified that a change makes the Rust implementation match OCaml's behavior exactly (same algorithm, same data sharing, same control flow), KEEP IT even if it causes a parity regression. The cycle detection and type sharing issues mean that a single correct change can cause regressions that are only resolved when combined with other correct changes. Reverting correct changes to preserve a local parity score prevents reaching the global optimum. The right approach is: (1) verify the change is 1:1 with OCaml, (2) commit it, (3) investigate and fix the regressions it causes by making MORE correct changes. Multiple correct changes in combination lead to breakthroughs. A temporary regression from a verified-correct change is progress, not failure.

- **You have time — do large refactors when needed** - If the OCaml implementation does something fundamentally different from the current Rust code (different algorithm, different data sharing model, different control flow), do NOT work around it with heuristics or workarounds. Start implementing the OCaml approach NOW, even if it means rewriting a large subsystem. We are building a 1:1 rewrite of the OCaml reference compiler in idiomatic Rust — nothing more, nothing less. There is no shortcut that avoids doing the real work. A multi-session refactor that aligns with OCaml is always better than a quick hack that papers over the difference. Take as many sessions as needed to get it right.

- **We are NOT bound by OCaml compatibility** - The ReScript compiler originated as a fork of the OCaml compiler, but we maintain our own AST and can make breaking changes. Focus on what's best for ReScript's JavaScript compilation target.

- **Never modify `parsetree0.ml`** - Existing PPX (parser extensions) rely on this frozen v0 version. When changing `parsetree.ml`, always update the mapping modules `ast_mapper_from0.ml` and `ast_mapper_to0.ml` to maintain PPX compatibility while allowing the main parsetree to evolve. **Test the bridge with the existing infra** — do not build new harnesses for this:
  - Add a source fixture exercising the new syntax to `tests/syntax_tests/data/ast-mapping/`. Every file there is run through `res_parser -test-ast-conversion` (which round-trips the parsetree through the frozen v0 AST before printing) as part of `make test-syntax`; the printed output must match the snapshot in its `expected/` directory.
  - For exact-identity invariants (locations, attributes) or the v0 wire shape itself, add cases to `tests/ounit_tests/ounit_ast_mapper0_tests.ml`, which tests `ast_mapper_to0`/`ast_mapper_from0` directly.

- **Missing test coverage** - Always add tests for syntax, lambda, and end-to-end behavior

- **Test early and often** - Add tests immediately after modifying each compiler layer to catch problems early, rather than waiting until all changes are complete

- **Use underscore patterns carefully** - Don't use `_` patterns as lazy placeholders for new language features that then get forgotten. Only use them when you're certain the value should be ignored for that specific case. Ensure all new language features are handled correctly and completely across all compiler layers
- **Avoid `let _ = …` for side effects** - If you need to call a function only for its side effects, use `ignore expr` (or bind the result and thread state explicitly). Do not write `let _ = expr in ()`, and do not discard stateful results—plumb them through instead.

- **Don't use unit `()` with mandatory labeled arguments** - When a function has a mandatory labeled argument (like `~config`), don't add a trailing `()` parameter. The labeled argument already prevents accidental partial application. Only use `()` when all parameters are optional and you need to force evaluation. Example: `let forceDelayedItems ~config = ...` not `let forceDelayedItems ~config () = ...`

- **Avoid warning suppressions** - Never use `[@@warning "..."]` to silence warnings. Instead, fix the underlying issue properly
- **Skip trailing `; _` in record patterns** - The warning it targets is disabled in this codebase, so prefer `{field = x}` over `{field = x; _}`.
- **Do not introduce new `unsafe` Rust in compiler code** - Prefer safe ownership/lifetime patterns (owned `String`, arena indices, side tables). If `unsafe` is truly unavoidable (for example, FFI boundaries), keep it narrowly scoped, document invariants, and justify it in the PR/commit message.

- **Do not introduce new keywords unless absolutely necessary** - Try to find ways to implement features without reserving keywords, as seen with the "catch" implementation that avoids making it a keyword.

- **Use tight timeouts when testing compiler/parser** - When running the compiler or parser in tests, always use a short timeout (e.g., 5-10 seconds). Compilation should be fast, and logic errors can cause infinite loops or hangs. A tight timeout ensures these issues are caught quickly rather than blocking indefinitely.

- **Handle concurrent agent work gracefully** - If compilation fails due to errors in code you didn't touch, another agent may be actively working on that part of the codebase. Do NOT modify their files and NEVER use `git stash`. Simply wait 30 seconds and retry the build. Repeat this until compilation succeeds—the other agent will fix their changes shortly.

- **There is NO linter that reverts your changes** - If you're having trouble editing files, the issue is with your edit commands (e.g., wrong `old_string`, file not found, etc.), NOT a linter reverting changes. There are no pre-commit hooks, no auto-formatters, and no tools that automatically modify or revert your edits. Debug your actual edit failures instead of assuming external interference.

- **Do NOT revert large changes** - If a task impacts a large amount of code, do NOT revert and give up. Complete the large task as requested. The user is aware it's a big change and expects you to follow through.

- **Do NOT switch tasks when things get hard** - If you're working on a difficult task, do NOT abandon it to work on something easier. Complete the current task FIRST, then move on to the next one. Switching tasks loses valuable context and leaves work incomplete.

- **Embrace complexity - everything must be done** - Do not shy away from complex tasks or defer them hoping for an easier path. Every item on the task list must eventually be completed, so you might as well dig in now. Complex problems don't get easier by avoiding them—they just stay unsolved. Tackle the hard parts head-on with full attention. The satisfaction of solving a difficult problem far outweighs the temporary comfort of picking low-hanging fruit.

- **Stop looking for easy wins — all remaining issues are hard** - Do NOT start by scanning for "smallest diffs" or "simple fixes." There are none left. Every remaining parity failure has been investigated and requires deep work. Pick the highest-impact root cause and dig in, even if it takes hours or multiple sessions. Reading OCaml source for an hour before writing a single line of Rust is expected and encouraged. The path forward is through understanding, not through hoping to find a quick fix that was somehow missed.

- **ALWAYS commit before moving on** - Before starting a new task, before investigating a problem, before taking a break: COMMIT. Use `git add <files> && git commit -m "description"`. No exceptions.

- **One task per session** - Only take on ONE task at a time. When you complete a task, STOP. Do not pick up another task from the TODO list. Each new task should start with a fresh context window. This ensures you have full context capacity for each task and prevents context exhaustion from accumulating state across multiple tasks.

## ⚠️ CRITICAL: Typedtree Sexp Parity — No Cheating

Typedtree sexp parity compares the sexp serialization of the typed AST between the OCaml and Rust compilers. The goal is **identical output** achieved by making the Rust **type checker implementation** functionally equivalent to OCaml's — NOT by adding normalizations, sorting, or content-based tricks to the sexp serializer.

### Absolute Rules

1. **NO content-based normalization in the serializer.** Do not merge, deduplicate, or rewrite type nodes based on their content/structure. OCaml's sexp dedup is based on **physical identity** (`type_expr.id`), not structural equality. The Rust serializer must use **physical identity** (`TypeExprRef`) for dedup — nothing else.

2. **NO sorting.** Do not sort record fields, variant row fields, object fields, or any other list by name/label/position. Serialize everything in the **natural order** the type checker produces. If the order differs from OCaml, the type checker is building the data structure differently — fix the type checker, not the serializer.

3. **NO stripping or rewriting.** Do not strip `Tvar` names, remove `Tlink` nodes, convert `Reither` to `Rpresent`, rewrite paths, or transform type descriptions in the serializer. The serializer must faithfully emit what the type checker produced.

4. **NO special-case hacks.** Do not add "if this specific test file / this specific type / this specific pattern, then do X" logic. Every fix must be a general improvement to the type checker that makes it behave more like OCaml.

5. **The only legitimate serializer-level dedup is physical identity** — same `TypeExprRef` maps to same index. The one exception is the arity alias dedup, which exists because OCaml's `{t with desc = Tarrow(...)}` creates a new record sharing the same `type_expr.id` — this is matching OCaml's physical identity semantics, not adding a content-based hack.

### How to Fix Parity Issues

When the Rust sexp output differs from OCaml:

1. **Read the OCaml source** to understand WHY OCaml produces that output. The answer is always in the type checker (`ctype.ml`, `typecore.ml`, `typemod.ml`, `typetexp.ml`), not in the serializer.

2. **Understand the data sharing model.** OCaml's type checker creates specific sharing patterns through `instance()`, `copy`, `link_type`, `unify`, `generalize`, and `Subst`. These determine which type nodes are physically identical. The Rust type checker must create the **same sharing patterns**.

3. **Understand traversal order.** OCaml processes data structures in specific orders (e.g., `List.fold_left` vs `List.fold_right`, batch pattern typing before body typing). The Rust type checker must process things in the **same order**.

4. **Fix the type checker**, not the serializer. If Rust has more/fewer type nodes, different sharing, or different order — the fix is in `ctype.rs`, `typecore.rs`, `typemod.rs`, `context.rs`, etc.

5. **Use introspection.** You have full access to the OCaml reference source (`compiler/ml/`), debug flags (`-dtyped-sexp-locs`), and can add temporary `eprintln!` tracing to understand exactly what the type checker does differently.

### What "Parity" Means

Parity means the Rust type checker produces a typed AST with:
- The **same type nodes** (same structure and content)
- The **same physical sharing** (same nodes deduplicated by identity)
- The **same traversal order** (nodes encountered in the same DFS order)
- The **same number of instances** (no extra copies from over-generalization, no missing copies from wrong identity returns)

This is achieved ONLY by making the Rust type checker implementation equivalent to OCaml's. There are no shortcuts.

### Current Lazy-Typechecker Debt TODO

These are known high-risk areas from the seven-day parity review. Treat them as debt for the current strict typedtree/lambda/output parity goal. Do not add more compensation in these areas; replace Rust-only behavior with the OCaml lazy Env/Ctype flow and cite the exact OCaml reference locations in each change.

Hard rule for this goal: never improve parity by adding a Rust-only compatibility layer. Any change that suppresses a force, rewrites a representative, matches path strings, scans signature contents to guess forcing, or branches lazy behavior on output mode must be treated as debt unless it directly mirrors the reference OCaml implementation at a cited source location.

### Intentional Rust Performance Representations

Do not remove these while cleaning parity debt. They are explicit Rust storage/layout optimizations that must preserve OCaml-equivalent external typedtree, lambda, and JavaScript behavior, but they do not have to use OCaml's exact in-memory representation.

- **Sparse typedtree extras:** `typedtree::SparseExtras<T>` stores the common empty extras case without an inline empty `Vec`. This preserves the same slice/iterator behavior as OCaml's `exp_extra = []` / `pat_extra = []`, while reducing per-node memory.
- **Parser expression side tables:** `ParseArena` keeps rarely-present expression payloads such as function defaults, case guards, record spreads, and coercion sources in sparse `ExprIdx` side tables. This is a storage optimization over OCaml Parsetree records from `compiler/ml/parsetree.ml:210-214` and `compiler/ml/parsetree.ml:226-298`; it must preserve the same AST accessors and marshalling behavior.
- **Sparse large regular records:** `ExpressionDesc::Texp_record_sparse` and `RecordLabelDefinition::OmittedOptionalNone` avoid allocating hundreds of cloned label descriptions and full `Texp_construct None` nodes for large JSX prop records. The boundary must remain equivalent to OCaml `compiler/ml/typecore.ml:297-300`, `compiler/ml/typecore.ml:2833-2842`, and `compiler/ml/translcore.ml:1139-1191`: serializers plus debug/captured lambda output expand over the complete `lbl_all` order, while normal JS lowering may compact omitted optional `None` fields only when named record metadata and projection still preserve byte-for-byte JS output parity.
- **Compact type-node handles:** `TypeExprRef(u32)` and `TypeExprRefMap<T>` are arena-index storage optimizations for OCaml `type_expr` physical identity from `compiler/ml/types.ml:22` and the allocation path in `compiler/ml/btype.ml:46-48`. Keep identity-based behavior; do not replace this with structural keys.
- **Derived Env alias-scope caches:** `Env::local_module_aliases_cache` and `module_path_requires_env_scoped_cache_cache` are Rust-side memo tables derived from visible bindings, preserving OCaml lookup boundaries in `compiler/ml/env.ml:781-813` and `compiler/ml/env.ml:1516-1538`. They are performance caches only, not path-spelling alias equivalence.
- **CMJ export lookup caches:** `LambdaCompiler` caches `.cmj` constant/arity/lambda export tables per module because Rust's resolver can cross an I/O boundary. This must preserve OCaml's query/export gates in `compiler/core/lam_compile.ml:234-244`, `compiler/core/lam_compile.ml:274-279`, `compiler/core/lam_stats_export.ml:53-63`, and `compiler/core/js_cmj_format.ml:120-128`.

Completed for this goal:
- **Alias representative patching removed:** `preserve_alias_unify_representative` and its call sites were deleted. Do not reintroduce a typecore-side representative rewrite; representative choice must continue to emerge from the OCaml-aligned `type_argument` -> `type_expect` -> `unify_exp` flow plus `ctype.ml` unification/expansion.
- **Canonical typedtree mode altering semantics removed:** `preserve_canonical_typedtree` and its driver/typecore branches were deleted. Normal compilation and typedtree dumping now use one lazy component-resolution path; output mode must stay out of force order, thunk sharing, and signature copy depth.
- **Alias representative selection removed:** `preferred_alias_equiv_representative` and its call sites were deleted. Alias-equivalent constructor recovery now links through the existing unification order instead of a typecore-side representative preference.
- **Path-spelling alias fallbacks reduced:** `env_lazy::parent_matches_component_context` no longer formats `A__B`/`A_B`; local alias unification no longer succeeds when the short declaration is missing; `lookup_type_decl_for_path` no longer synthesizes `Stdlib.X.t`/`Stdlib_X.t`; flattened constructor, signature-prefix, nested self-path, include-localization, and raw lazy signature registration now require registered alias-table evidence.
- **CMI substitution spelling fallback removed:** `persistent_env.rs` no longer rewrites non-persistent type or module idents by checking for `_` in the name. Non-persistent substitution now follows OCaml `compiler/ml/subst.ml:69-76` and `compiler/ml/subst.ml:87-100`: rewrite by identifier identity only, with name lookup reserved for persistent stamp-0 ids.
- **Qualified type expansion name fallback removed:** `ctype.rs` no longer treats a declaration with the same printed qualified path as an exact type lookup. Qualified type expansion now follows OCaml `compiler/ml/env.ml:800-813` and `compiler/ml/ctype.ml:1395-1439`: resolve through the parent component table and fall through when that lookup fails.
- **Flattened alias declaration-name fallback removed:** `ctype.rs` no longer treats two registered flattened-alias declarations as equivalent just because their `type_path` values print the same name. The final declaration-identity comparison now follows OCaml `compiler/ml/ctype.ml:1941` and `compiler/ml/ctype.ml:2077-2088`: use `Path.same`, with alias equivalence coming from manifests or registered component-alias evidence.
- **Manifest/nullary constructor name fallbacks removed:** `ctype.rs` no longer treats manifest aliases or nullary constructor paths as equivalent just because their printed path names match. These checks now follow OCaml `compiler/ml/ctype.ml:1941` and `compiler/ml/ctype.ml:2077-2088`: compare paths with `Path.same`; let real manifest expansion and registered alias evidence account for legitimate aliases.
- **Name-based nullary unify shortcut removed:** `ctype.rs` no longer links two expanded nullary constructors just because their printed paths match. `unify_after_expansion` now falls through to the normal OCaml-shaped constructor branch, matching `compiler/ml/ctype.ml:2338-2363` and the `Tconstr`/`Path.same` branch at `compiler/ml/ctype.ml:2413-2433`.
- **Failed-unify snapshot/backtrack added:** `TypeContext::snapshot_type_state` / `restore_type_state` now give Rust an OCaml-style mutation rollback for speculative unification. `for...of` follows the two-snapshot iterable-then-array order from `compiler/ml/typecore.ml:3187-3211`, and non-generalizable coercions use the snapshot/backtrack fast path from `compiler/ml/typecore.ml:3317-3330` instead of copied-node compensation. Local type declarations also preserve `ptype_private` in the environment declaration per `compiler/ml/typedecl.ml:700-706`, so private aliases do not become public equality-unification aliases.
  Debug verification: `cargo build --manifest-path compiler-rust/Cargo.toml`, `cargo build --manifest-path rewatch/Cargo.toml`, `./scripts/test_typedtree_parity.sh type_coercion_free_vars` = 1/1, `./scripts/test_typedtree_parity.sh --quick` = 660/660, `./scripts/test_lambda_parity.sh --quick` = 660/660.
- **Name-based constructor unify shortcut removed:** `ctype.rs` no longer links parameterized constructors solely because their printed paths match. Constructor unification now continues through the OCaml-shaped `Path.same` branch from `compiler/ml/ctype.ml:2413-2433`, with alias equivalence coming from expansion, normalization, or registered component-alias evidence.
- **Local submodule segment fallback removed:** `ctype.rs` no longer splits printed paths to equate aliases such as `A.B.t` and `B.t`. Legitimate local module alias identity must come from OCaml-shaped component prefixing/substitution (`compiler/ml/env.ml:1516-1559`, `compiler/ml/subst.ml:69-100`) and normal `Path.same` unification (`compiler/ml/ctype.ml:2413-2433`), not segment-count heuristics.
- **Package path printed-name fallback removed:** `ctype.rs` package unification no longer accepts equal printed package paths. It now follows OCaml `compiler/ml/ctype.ml:2173-2175` and `compiler/ml/ctype.ml:2236-2244`: compare the original package paths with `Path.same`, then compare normalized package paths with `Path.same`.
- **Probe cache suppression removed:** `component_alias_probe_cache_suppression` and its global guard were deleted. Probe-style type/component lookups now use explicit no-publish cache mode at the lookup API boundary, matching OCaml's separate `find_module_descr`/`find_type` descriptor reads instead of changing global context state.
- **Global force suppression guard removed:** `component_alias_sig_force_suppression` and its scoped wrappers were deleted. Probe-style component/type lookups now carry explicit `ComponentLookupCacheMode::Probe`, matching OCaml `compiler/ml/env.ml:781-813` descriptor/type lookups separately from `find_module`/`components_of_module_maker` forcing at `compiler/ml/env.ml:865-882` and `compiler/ml/env.ml:1516-1588`.
- **Label root rewrite name fallback removed:** `typecore.rs` no longer rewrites label argument/result type paths by matching equal printed parent names. Direct record-label root rewriting now follows OCaml `compiler/ml/subst.ml:87-95` and `compiler/ml/env.ml:1542-1559`: apply explicit component substitution with `Path.same`, not path spelling.
- **Value-only signature qualification shortcut removed:** `typecore.rs` no longer skips component-signature copying/substitution when a signature contains only values. Component signatures now follow OCaml `compiler/ml/env.ml:1530-1538` and `compiler/ml/subst.ml:303-309`: run `prefix_idents`/`Subst.value_description` shape consistently instead of deciding laziness from signature contents.
- **Primitive_js_extern probe compensation removed:** `typemod.rs` no longer scans type manifests for a `Primitive_js_extern` root to decide whether to force constraint-match expansion. Type-declaration constraint side effects now stay on the OCaml-shaped path at `compiler/ml/typedecl.ml:767-781` and `compiler/ml/ctype.ml:2338-2344`: expand copied heads for the parameterized constructor currently being checked.
- **Implicit-root signature-content shortcut removed:** `ctype.rs` no longer follows synthetic `Stdlib`/`Pervasives` component aliases before recursive path normalization, and no longer checks whether an alias target signature contains submodules before deciding to normalize through it. `normalize_path_full_inner` now follows OCaml `compiler/ml/env.ml:903-914`: normalize the dotted prefix first, then let `find_module ~alias:true` at `compiler/ml/env.ml:865-882` force and follow aliases in Env order.
- **Selected-value Primitive_js_extern manifest scan removed:** `typecore.rs` no longer walks copied selected-value type manifests looking for a `Primitive_js_extern` root to trigger head expansion. Qualified value typing now stays on the OCaml path from `compiler/ml/typecore.ml:2421-2457` and `compiler/ml/typecore.ml:4171-4192`: instance the selected value description, type source arguments, and let `compiler/ml/ctype.ml:2338-2344` expansion occur through unification rather than a content-based manifest scan.
- **Selected-value force suppression flag removed:** `typecore.rs` no longer carries a dead `suppress_selected_value_forces` branch through selected-value type traversal. All selected-value traversal now follows the single OCaml-shaped path: `compiler/ml/typecore.ml:2421-2457` instances the `Env.find_value` result, `compiler/ml/typecore.ml:4171-4192` types source arguments, and component value paths come from `compiler/ml/env.ml:1530-1538` plus `compiler/ml/subst.ml:303-309`.
- **Constructor same-type-item unification fallback removed:** `ctype.rs` no longer bypasses constructor expansion/failure by comparing resolved `Sig_type` item identities for different paths, and selected-value persistent rewrites no longer depend on that identity helper. Constructor unification now follows OCaml `compiler/ml/ctype.ml:2338-2344` and `compiler/ml/ctype.ml:2413-2433`: expand both heads first, then take the argument-only path only when the resulting constructor paths are `Path.same`.
- **Packed-module placeholder fallback removed:** `typecore.rs` no longer synthesizes a placeholder `Texp_pack` when the expected type does not expand to `Tpackage`. `Pexp_pack` now follows OCaml `compiler/ml/typecore.ml:3518-3525`: raise `CannotInferSignature` for an unconstrained type variable and `NotAPackedModule` otherwise. Debug verification at the time of this change: `cargo build --manifest-path compiler-rust/Cargo.toml`, `cargo build --manifest-path rewatch/Cargo.toml`, `./scripts/test_typedtree_parity.sh --quick` = `660/660`, `./scripts/test_lambda_parity.sh --quick` = `660/660`.
- **Typecore post-unify alias retry removed:** `typecore.rs` no longer catches `Ctype.Unify` to retry flattened-alias or nullary-constructor linking from expression typing. `unify_expression_types` now mirrors OCaml `compiler/ml/typecore.ml:345-348`: report the `Ctype.unify` result directly, with alias expansion and representative choice handled inside the Ctype/Env flow.
- **Ctype flattened-alias constructor link removed:** `ctype.rs` no longer links flattened and qualified constructors after expansion failed to make their paths equal. Constructor unification now follows OCaml `compiler/ml/ctype.ml:2338-2344` and `compiler/ml/ctype.ml:2413-2433`: run `expand_head_unif`, then unify constructor arguments only when the expanded paths are `Path.same`.
- **Selected-value alias post-unify skip removed:** `typecore.rs` no longer skips the second argument unification for selected flattened aliases. Function application arguments now follow OCaml `compiler/ml/typecore.ml:3771-3773`: `type_expect` first, then `unify_exp`; alias success/failure must come from Ctype/Env, not a selected-value guard.
- **Flattened alias equivalence helper removed:** `ctype.rs` no longer exposes `flattened_alias_paths_equivalent`, `registered_flattened_alias_rewrite`, or `nullary_constr_paths_equivalent`. Type-path equivalence now stays on the OCaml-shaped routes: component lookup through `compiler/ml/env.ml:800-813`, substitution through `compiler/ml/subst.ml:87-100`/`303-309`, expansion through `compiler/ml/ctype.ml:1346-1372`, and constructor unification only under `Path.same` at `compiler/ml/ctype.ml:2413-2433`.
- **Initial-env `ref` duplicate removed:** `env.rs` no longer installs a local predef `ref` record into `initial_env`. OCaml `compiler/ml/predef.ml:239-419` does not define `ref` in `initial_safe_string`; `ref` enters the environment from `packages/@rescript/runtime/Pervasives.res:302` through the implicit open in `compiler/core/res_compmisc.ml:58-62` and `compiler/ml/env.ml:1874-1877`. With the duplicate local label gone, `typecore.rs` no longer needs the Rust-only `Pervasives.ref`/`ref` duplicate path shortcut in label ambiguity handling.
- **Initial-env Pervasives value preload removed:** `env.rs` no longer installs Pervasives operators, utilities, and `ref` primitives directly into `initial_env`. OCaml `compiler/ml/predef.ml:419-424` only adds the remaining predef `char` type after the common predef types/exceptions; normal values come from `Pervasives.res` through the implicit-open path in `compiler/core/res_compmisc.ml:56-62` and `compiler/ml/env.ml:1874-1877`.
- **Implicit Stdlib/Pervasives root bindings removed:** `driver.rs` no longer adds standalone-only root module bindings after opening implicit `Pervasives` and `Stdlib`; it only keeps raw signatures available for descriptor lookup. This matches OCaml `compiler/core/res_compmisc.ml:56-62` and `compiler/ml/env.ml:1874-1877`, where `open_signature` adds opened components but not root module bindings. `ctype.rs` normalize-path root forcing now follows the ordinary `compiler/ml/env.ml:865-882` persistent path without explicit `Stdlib`/`Pervasives` name overrides.
- **Pervasives variance force removed:** `ctype.rs` no longer forces a `Pervasives` signature rename during variance lookup for `Pervasives.ref`. OCaml `compiler/ml/typedecl.ml:1064-1066` asks `Env.find_type`, whose dotted lookup goes through `compiler/ml/env.ml:800-813` and `find_module_descr` at `compiler/ml/env.ml:781-788`; that reads persistent `ps_comps` without entering `find_module`'s `ps_sig` force at `compiler/ml/env.ml:865-875`.
- **Stdlib ArrayBuffer normalize-path exception removed:** `ctype.rs` no longer skips the implicit-root `Stdlib` force only for `Stdlib.ArrayBuffer`. Normalize-path root forcing now follows OCaml `compiler/ml/ctype.ml:1367-1372` and `compiler/ml/env.ml:903-914`: normalize the prefix first, then `find_module ~alias:true` at `compiler/ml/env.ml:865-882` decides whether the persistent root signature is forced.
- **Flattened alias spelling synthesis removed:** `typecore.rs` no longer constructs double-underscore flattened names inside `rewrite_flattened_alias_head_prefixes`. Source prefixes now come only from the persistent alias table or the component relation registered while building selected components, matching OCaml `compiler/ml/env.ml:1516-1538` alias scraping/prefixing and `compiler/ml/env.ml:1567-1578` child component storage.
- **Nested alias self-path spelling fallback removed:** `typecore.rs` no longer treats `flat_head_...` string prefixes as proof that a resolved module belongs under a selected alias component. `should_rewrite_nested_alias_self_path` now keeps a backing unit only when `TypeContext` has registered the parent or child component relation, matching OCaml `compiler/ml/env.ml:1516-1538` alias scraping/prefixing and `compiler/ml/env.ml:1567-1578` child component storage.
- **Selected-value implicit Stdlib inference removed:** `typecore.rs` no longer carries a non-Stdlib selected-value flag that infers `Stdlib.*` rewrites from flattened parent paths. Selected value traversal now rewrites persistent nested `t` paths only through the selected component's registered alias relation, matching OCaml `compiler/ml/typecore.ml:2421-2457`, `compiler/ml/typecore.ml:4171-4192`, `compiler/ml/typecore.ml:4219-4224`, `compiler/ml/env.ml:1530-1538`, and `compiler/ml/subst.ml:303-309`.
- **Signature item-shape substitution gate removed:** `typecore.rs` no longer decides whether to copy/substitute a resolved module signature by scanning for type/module/modtype declarations. Module signature qualification now follows OCaml `compiler/ml/env.ml:1530-1538` and `compiler/ml/subst.ml:303-309`: build/apply the component substitution path independently of whether the signature contains only values.
- **Selected-value implicit Stdlib alias-target gate removed:** `typecore.rs` no longer has a separate `Stdlib`-root predicate for deciding whether to collect selected alias targets. Exact selected roots and dotted selected component paths already cover the OCaml `compiler/ml/env.ml:781-813` and `compiler/ml/env.ml:1530-1538` lookup/substitution cases, including implicit opens from `compiler/core/res_compmisc.ml:56-62`.
- **Selected-value opened-component root exclusion removed:** `typecore.rs` no longer excludes `Stdlib`/`Pervasives` by name when checking whether a selected module is an opened component. Alias-target collection now uses the same generic opened-component predicate, with exact roots and dotted component paths covering the implicit-open cases from `compiler/core/res_compmisc.ml:56-62` and `compiler/ml/env.ml:1874-1877`.
- **Implicit Stdlib component helper removed:** `typecore.rs` no longer has a separate `is_implicit_stdlib_component_path` helper for local type-path qualification. The existing persistent/global-root predicate covers the OCaml `compiler/ml/env.ml:781-813` descriptor/component path, so alias-target lookup no longer needs a root-name shortcut.
- **Selected-value implicit Stdlib force skip removed:** `typecore.rs` no longer skips nested type forcing for a non-Stdlib selected value solely because the nested type parent is rooted at `Stdlib` or `Pervasives`. Selected value traversal now skips only the selected component's own nested module and selected alias siblings, matching OCaml `compiler/ml/typecore.ml:2421-2457` value instancing, `compiler/ml/typecore.ml:4171-4192` source argument typing, `compiler/ml/env.ml:1091-1100` qualified value lookup, and `compiler/ml/ctype.ml:666-695` later argument lowering.
- **Qualified value leaf fallback removed:** `typecore.rs` no longer resolves `Module.value` by falling back to an unqualified `value` lookup when the module prefix is unavailable. Qualified value lookup now follows OCaml `compiler/ml/env.ml:1091-1100`: resolve the module prefix through `lookup_module_descr`, read the selected component value table, or fail.
- **Qualified value raw-signature fallback removed:** `typecore.rs` no longer scans a resolved raw signature when the component-value cache misses during qualified value lookup. Qualified value lookup now stays on the OCaml `compiler/ml/env.ml:1091-1100` route: `lookup_module_descr` at `compiler/ml/env.ml:1000-1034`, component values built by `compiler/ml/env.ml:1516-1538`, and `Subst.value_description` at `compiler/ml/subst.ml:303-309`.
- **Selected-value implicit Stdlib nested-force gate removed:** `typecore.rs` no longer forces nested selected-value type paths just because the selected module is rooted at `Stdlib`. The nested selected-component skip is now generic for all selected modules, matching OCaml `compiler/ml/typecore.ml:2421-2457` value instancing, `compiler/ml/typecore.ml:4171-4192` argument typing, `compiler/ml/env.ml:1091-1100` qualified value lookup, and the separate child-module thunk force boundary in `compiler/ml/env.ml:1567-1578`.
- **Selected-value Stdlib alias-root exception removed:** `typecore.rs` no longer excludes `Stdlib` by name when deciding whether the selected module and a candidate type parent share a registered alias root. The rewrite decision now uses the same registered alias-root relation for every module family, matching OCaml `compiler/ml/env.ml:1516-1538` alias scraping/component prefixing, `compiler/ml/mtype.ml:41-49` alias strengthening, and `compiler/ml/subst.ml:303-309` value-description substitution.
- **Opened-component path detection generalized:** `ctype.rs` no longer decides selected child signature reuse and component-alias normalization by hard-coded `Stdlib`/`Pervasives` root names. It now detects whether the first dotted component came from an opened Env binding, matching OCaml implicit opens in `compiler/core/res_compmisc.ml:56-62`, `compiler/ml/env.ml:1874-1877`, descriptor/component lookup in `compiler/ml/env.ml:781-793`, module forcing in `compiler/ml/env.ml:865-882`, and child component construction in `compiler/ml/env.ml:1567-1578`.
- **Direct opened-component alias forcing generalized:** `env_lazy.rs` no longer hard-codes direct `Stdlib`/`Pervasives` children when deciding whether a persistent alias target should trigger signature renaming without a `PersistentEnv`. The predicate now checks opened Env binding origin, matching OCaml implicit opens in `compiler/core/res_compmisc.ml:56-62`, `compiler/ml/env.ml:1874-1877`, alias scraping in `compiler/ml/env.ml:1440-1446`, module forcing in `compiler/ml/env.ml:865-882`, and probe-style descriptor/type lookup laziness in `compiler/ml/env.ml:800-813`.
- **Belt normalize-path force exception removed:** `ctype.rs` no longer skips persistent signature forcing for `Belt` when a component cache already exists. Normalize-path `Pident` handling now follows OCaml `compiler/ml/ctype.ml:1367-1372` and `compiler/ml/env.ml:903-914`: call `find_module ~alias:true`, whose persistent branch in `compiler/ml/env.ml:865-875` forces `ps_sig` unless the module is present in `env.modules`.
- **Signature-content child forcing removed:** `typecore.rs` no longer scans raw signatures to decide that a manifest parent has a persistent alias child. Lowered-argument manifest forcing is now limited to captured `Ctype.lower_args` lookup/expansion paths plus registered alias-component facts, matching the OCaml force route through `compiler/ml/typecore.ml:2335-2342`, `compiler/ml/ctype.ml:666-673`, `compiler/ml/env.ml:800-813`, and child component thunk storage at `compiler/ml/env.ml:1567-1578`.
- **Fabricated flattened alias head removed:** `typecore.rs` no longer derives a persistent backing unit by joining a qualified alias path with underscores during local module type-path qualification. Rewrites now use only flattened heads recorded from the persistent alias table or component relations, matching OCaml alias evidence from `compiler/ml/env.ml:1517`, `compiler/ml/env.ml:1530-1538`, and `compiler/ml/env.ml:1567-1578` rather than path spelling.
- **Namespace suffix force heuristic removed:** `persistent_env.rs`/`typecore.rs` no longer decide lowered-argument manifest forcing from `.mlmap` filenames, `Module-Namespace` suffix spelling, or alias-only signature shape. Namespace-backed aliases now rely on alias-prefix rewrites collected from actual module alias declarations/components, matching OCaml alias evidence from `compiler/ml/env.ml:1517`, `compiler/ml/env.ml:1530-1538`, and `compiler/ml/env.ml:1567-1578`.
- **Selected-value Promise path spelling removed:** `typecore.rs` no longer treats printed `Stdlib.Promise.t` as a Promise constructor when deciding whether async selected-value final results stay lazy. The async final-result skip now recognizes only the predef Promise path, matching `compiler/ml/predef.ml:66`, `compiler/ml/predef.ml:113`, and the lowered async application flow at `compiler/ml/typecore.ml:2568-2588`.
- **Selected-value Promise-aware final-result branch removed:** `typecore.rs` no longer scans final application result types for a qualified component path plus Promise constructor before deciding whether to force them. Selected-value final-result laziness now uniformly follows OCaml `compiler/ml/typecore.ml:2335-2343` (`lower_args` stops at the first non-arrow result) and `compiler/ml/typecore.ml:4219-4224` (the final application result is left to caller unification/expansion).
- **Path-spelling alias equivalence helper removed:** `flattened_alias_paths_equivalent` and its call sites are gone from `ctype.rs`, `typecore.rs`, and `typemod.rs`. Remaining flattened-name uses must stay tied to persistent alias-table or registered component evidence from `compiler/ml/env.ml:1516-1538` and `compiler/ml/subst.ml:87-100`, not fallback path spelling.
- **Implicit Stdlib/Pervasives force-order special cases audited/removed:** Current explicit `Pervasives.*` entries in `typecore.rs` mirror unified operators from `compiler/ml/unified_ops.ml:56-262` and `compiler/ml/typecore.ml:3814-3819`; current explicit `Stdlib_*`/`Stdlib.Child.t` entries in `typemod.rs` mirror untagged-variant builtin object matching in `compiler/ml/ast_untagged_variants.ml:243-271`. Implicit opens are handled through `compiler/core/res_compmisc.ml:56-62` and `compiler/ml/env.ml:1874-1877`, not Rust-only force-order branches.
- **Value component substitution scan removed:** `env_lazy.rs::lookup_value_for_access` no longer runs `value_mentions_local_component_type` before selected value substitution. Qualified component value lookup now always deep-copies the selected value and applies the component substitution, matching `compiler/ml/env.ml:1530-1538` and `compiler/ml/subst.ml:303-309`, with the copied result memoized in the component table.
- **Direct flattened component type rewrite moved to Env substitution:** `persistent_env.rs::substitute_type_paths_in_value_from_sig` now rewrites direct flattened backing type paths for the selected component's own `Sig_type` binders, and the matching `typecore.rs` post-instance fallback was deleted. This follows OCaml `compiler/ml/env.ml:1454-1481` (`prefix_idents` creates selected component paths), `compiler/ml/env.ml:1530-1538` (component values are stored after substitution), `compiler/ml/subst.ml:303-309` (`Subst.value_description`), and `compiler/ml/typecore.ml:2421-2457` (typecore only instances the returned value description).
- **Opened-component selected-value rewrite removed:** `typecore.rs` no longer has a post-instance `selected_opened_alias_type_path` branch. Opened component value paths now rely on the existing qualified component lookup/substitution flow from OCaml `compiler/ml/env.ml:1841-1860`/`compiler/ml/env.ml:1874-1877` (open component tables), `compiler/ml/env.ml:1091-1100` (qualified value lookup), `compiler/ml/env.ml:1530-1538` (component values), `compiler/ml/subst.ml:303-309` (`Subst.value_description`), and `compiler/ml/typecore.ml:2421-2457` (instance the returned value description).
- **Flattened persistent selected-value rewrite removed:** `typecore.rs` no longer has a post-instance `flattened_persistent_alias_type_path` branch. Flattened alias value path shape now comes from component signature qualification and value-description substitution instead of a typecore-side path rewrite, matching OCaml `compiler/ml/env.ml:1435-1446` (alias scraping), `compiler/ml/env.ml:1516-1538` (component construction), `compiler/ml/mtype.ml:41-49` (alias strengthening leaves value descriptions unchanged), `compiler/ml/subst.ml:303-309`, and `compiler/ml/typecore.ml:2421-2457`.
- **Local-alias selected-value rewrite removed:** `typecore.rs` no longer rewrites selected-value type paths through `visible_local_alias_type_path` or collects alias targets after `instance`. Local alias value path shape now comes from component construction/substitution before expression typing, matching OCaml `compiler/ml/env.ml:1718-1734` (local `store_module` builds components rooted at `Pident id`), `compiler/ml/env.ml:1435-1446` (alias scraping), `compiler/ml/env.ml:1516-1538` (component values), `compiler/ml/subst.ml:303-309`, and `compiler/ml/typecore.ml:2421-2457`.
- **Selected-value force helper removed:** `typecore.rs` no longer has `force_qualified_value_type_paths`, no longer walks selected-value schemes after `instance`, and no longer forces constructor-result alias paths through `constructor_alias_rewrite_value_path`. Identifier typing now mirrors OCaml `compiler/ml/typecore.ml:2421-2457`: `Typetexp.find_value`, `instance env desc.val_type`, then `rue`. Constructor typing now leaves argument/result forcing to the normal constructor flow from `compiler/ml/typecore.ml:4282-4347`, with later expansion through `compiler/ml/ctype.ml:1367-1372` and Env lookup `compiler/ml/env.ml:896-914`.
- **Stale include substitution helper removed:** `includemod.rs` no longer keeps the unused `substitute_module_declaration_paths` helper that claimed Rust could not thread substitution lazily. The active module-declaration check already follows OCaml `compiler/ml/includemod.ml:396-413`: strengthen the implementation module type, then recurse through `modtypes` with the current substitution instead of pre-substituting the module declaration.
- **Rust-only type declaration registries removed:** `TypeContext` no longer keeps the name-, stamp-, printed-path- and exact-path-keyed declaration maps (`type_decl_store`, `type_decl_by_stamp`, `type_decl_by_path`, `type_decl_by_exact_path`, `type_item_by_path`, `missing_type_item_by_path`), and `persistent_env.rs` no longer refills them from every loaded signature (`register_sig_types_recursive`, `register_types_by_stamp_recursive`). Type lookups go through the Env and module components only, as OCaml does in `compiler/ml/env.ml:781-813` and `compiler/ml/env.ml:1516-1588`; `Typeopt.is_base_type` inspects `scrape env ty` only (`compiler/ml/typeopt.ml:99-101`). Do not reintroduce a global declaration table as a lookup fallback.

### Rebuilding the OCaml bsc

If you modify OCaml source files (e.g., `compiler/ml/sexp_typedtree.ml`), rebuild with:
```bash
eval $(opam env) && dune clean --root . && dune build --root .
```
This is worktree-specific — other worktrees have their own dune build.

## Compiler Architecture

### Compilation Pipeline

```
ReScript Source (.res)
  ↓ (ReScript Parser - compiler/syntax/)
Surface Syntax Tree
  ↓ (Frontend transformations - compiler/frontend/)
Surface Syntax Tree
  ↓ (OCaml Type Checker - compiler/ml/)
Typedtree
  ↓ (Lambda compilation - compiler/core/lam_*)
Lambda IR
  ↓ (JS compilation - compiler/core/js_*)
JS IR
  ↓ (JS output - compiler/core/js_dump*)
JavaScript Code
```

### Platform-specific compiler modules

The Dune `browser` profile builds the playground compiler. Platform-dependent
modules are stored below `platform/native/` and `platform/playground/` in their
owning compiler directory. Rules in that directory's `dune` file copy the
selected implementation into the build directory as an ordinary `.ml` module;
all other profiles select the native source. Generated module paths in errors
or stack traces therefore map back to one of those two source directories.

### Key Directory Structure

```
compiler/
├── syntax/          # ReScript syntax parser (MIT licensed)
├── frontend/        # AST transformations, FFI processing
├── ml/              # OCaml compiler infrastructure
├── core/            # Core compilation (lam_*, js_* files)
├── ext/             # Extended utilities and data structures
└── gentype/         # TypeScript generation

analysis/            # Language server and tooling
packages/@rescript/
├── runtime/         # Runtime and standard library
└── <platform>/      # Platform-specific binaries

tests/
├── syntax_tests/    # Parser/syntax layer tests
├── tests/           # Runtime library tests
├── build_tests/     # Integration tests
└── ounit_tests/     # Compiler unit tests
```

## Working on the Compiler

### Development Workflow

Read the area guide before changing a compiler subsystem:

- [`compiler/syntax/README.md`](compiler/syntax/README.md) for parsing,
  printing, and JSX transformation
- [`compiler/ml/README.md`](compiler/ml/README.md) for the type checker and
  typed tree
- [`compiler/core/README.md`](compiler/core/README.md) for Lambda
  optimization and JavaScript generation
- [`analysis/README.md`](analysis/README.md) for editor analysis
- [`rewatch/README.md`](rewatch/README.md) for the build system
- [`tools/README.md`](tools/README.md) for `rescript-tools`

1. **Understand which layer you're working on:**
   - **Syntax layer** (`compiler/syntax/`): Parsing and surface syntax
   - **ML layer** (`compiler/ml/`): Type checking and AST transformations
   - **Lambda layer** (`compiler/core/lam_*`): Intermediate representation and optimizations
   - **JS layer** (`compiler/core/js_*`): JavaScript generation

2. **Always run appropriate tests:**

   ```bash
   # For compiler or stdlib changes
   make test

   # For syntax changes
   make test-syntax

   # For specific test types
   make test-syntax-roundtrip
   make test-gentype
   make test-analysis
   ```

3. **Test your changes thoroughly:**
   - Syntax tests for new language features
   - Integration tests for behavior changes
   - Unit tests for utility functions
   - Always check JavaScript output quality

4. **Add a changelog fragment** `changes/<description>.<category>.md` for any user-facing change (bug fix, feature, or breaking change) instead of editing `CHANGELOG.md`; see [changes/README.md](changes/README.md) for categories and format. Validate with `yarn changelog:check`.

### Debugging Techniques

#### View Intermediate Representations

```bash
# Source code (for debugging preprocessing)
./packages/@rescript/<platform>/bin/bsc.exe -dsource myfile.res

# Parse tree (surface syntax after parsing)
./packages/@rescript/<platform>/bin/bsc.exe -dparsetree myfile.res

# Typed tree (after type checking)
./packages/@rescript/<platform>/bin/bsc.exe -dtypedtree myfile.res

# Raw lambda (unoptimized intermediate representation)
./packages/@rescript/<platform>/bin/bsc.exe -drawlambda myfile.res

# Use lambda printing for debugging (add in compiler/core/lam_print.ml)
```

#### Common Debug Scenarios

- **JavaScript formatting issues**: Check `compiler/ml/pprintast.ml`
- **Type checking issues**: Look in `compiler/ml/` type checker modules
- **Optimization bugs**: Check `compiler/core/lam_*.ml` analysis passes
- **Code generation bugs**: Look in `compiler/core/js_*.ml` modules

### Testing Requirements

#### When to Add Tests

- **Always** for new language features
- **Always** for bug fixes
- **When modifying** analysis passes
- **When changing** JavaScript generation

#### Test Types to Include

1. **Syntax tests** (`tests/syntax_tests/`) - Parser validation
2. **Integration tests** (`tests/tests/`) - End-to-end behavior
3. **Unit tests** (`tests/ounit_tests/`) - Compiler functions
4. **Build tests** (`tests/build_tests/`) - Error cases and edge cases
5. **Type tests** (`tests/build_tests/super_errors/`) - Single-file type checking errors
6. **Multi-file error tests** (`tests/build_tests/super_errors_multi/`) - Cross-module errors that need separate `.res` / `.resi` files

## Build Commands & Development

### Essential Commands

```bash
# Build compiler
make

# Build compiler in watch mode
make watch

# Build compiler and standard library
make lib

# Build compiler and standard library and run all tests
make test

# Build artifacts and update artifact list
make artifacts

# Clean build
make clean
```

### Testing Commands

```bash
# Specific test types
make test-syntax           # Syntax parser tests
make test-syntax-roundtrip # Roundtrip syntax tests
make test-gentype         # GenType tests
make test-analysis        # Analysis tests
make test-tools           # Tools tests
make test-rewatch         # Rewatch tests

# Single file debugging
./packages/@rescript/<platform>/bin/bsc.exe myfile.res
```

### Code Quality

```bash
# Format code
make format

# Check formatting
make checkformat

# Lint with Biome
npm run check
npm run check:all

# TypeScript type checking
npm run typecheck
```

## Performance Considerations

The compiler is designed for fast feedback loops and scales to large codebases:

- **Avoid meaningless symbols** in generated JavaScript
- **Maintain readable JavaScript output**
- **Consider compilation speed impact** of changes
- **Use appropriate optimization passes** in Lambda and JS IRs
- **Profile** before and after performance-related changes

### High-Performance Compiler Engineering

These principles apply to all performance-sensitive Rust code in the compiler, especially the parser, type checker, and code generator. They are informed by data-oriented design (DOD) research from OXC, Zig, Roc, Sorbet, and academic work.

#### Data layout principles

- **No `Rc` or `Arc`** — Reference counting prevents thread sharing and is slower than arena allocation. Use arena indices (`ExprIdx(u32)`), bump-allocated references (`&'arena T`), or owned/borrowed data (`Box<T>`, `&T`, `Cow<'a, T>`). The parser's `StrIdx`/`LocIdx`/`PosIdx` pattern is the model.

- **Keep enums small (≤16 bytes)** — Rust enums are sized by their largest variant. If 85% of variants fit in 8 bytes but one variant needs 100 bytes, every instance wastes 92 bytes. Box the large, rare variants. OXC measured 10% speedup from enforcing 16-byte AST enums.

- **Separate hot and cold data** — Fields accessed on every iteration belong together in one struct. Rarely-used fields (error recovery state, diagnostics, attributes) belong in a separate struct or side table. A 280-byte struct spanning 5 cache lines forces the CPU to load 4 cache lines of cold data to access 1 cache line of hot data. The Roc compiler gained 12% by splitting hot/cold data in their `Defs` type.

- **Side tables for sparse data** — If a field is None/empty >80% of the time, don't store it inline. Use a `HashMap<NodeIdx, T>` or `Vec<Option<T>>` side table. Each inline `Vec<Attribute>` wastes 24 bytes when empty (pointer + length + capacity), and ~95% of AST nodes have no attributes.

- **Prefer arrays over pointer-chased trees** — Sequential array access runs at ~0.96 instructions/cycle. Random pointer chasing runs at ~0.12 instructions/cycle (CPU stalled 87.5% of the time waiting for memory). Flattening a pointer-based AST into arena-indexed arrays gave 2.4x speedup in academic benchmarks. The CPU prefetcher can predict linear access but not pointer dereferences.

- **Bottom-up construction enables linear traversal** — When expressions are built bottom-up (children before parents), a depth-first traversal of the flattened array becomes a linear forward scan. This is automatically prefetcher-friendly and gives an additional ~8% speedup on top of flattening.

#### Allocation patterns

- **Arena allocate, bulk free** — Parser AST nodes have correlated lifetimes: they're all created during parsing and discarded together. Arena/bump allocation (single pointer increment) is near-zero cost vs `malloc` (free list search, metadata update). OXC measured 20% speedup from `bumpalo`. Even without bumpalo, storing nodes in `Vec<T>` pools with `u32` indices achieves similar benefits.

- **Pre-size collections** — If you know the approximate count (from source size heuristics or arena counts), pre-allocate Vecs and HashMaps. Repeated reallocation and copying is pure waste.

- **SmallVec for small, fixed-arity collections** — Function arguments average 1-3 items, tuple elements 2-4. `SmallVec<[T; 3]>` stores these inline without heap allocation. Only falls back to heap for the rare >N case.

#### String handling

- **Zero-copy from source** — Use `&'a str` or `Cow<'a, str>` to borrow from the source buffer rather than allocating `String`. Only allocate for strings that need transformation (escape sequences). The scanner produces borrowed strings for 99% of tokens.

- **Intern repeated strings** — Identifiers like `t`, `x`, `unit` appear thousands of times. Store each unique string once and reference by `StrIdx(u32)`. Comparison becomes integer equality instead of byte-by-byte string comparison.

- **Propagate borrows into the AST** — If strings are never modified after parsing, carry `Cow<'a, str>` or `&'a str` all the way into AST node types rather than converting to owned `String` at the token→AST boundary.

#### Serialization

- **Replace HashMaps with indexed Vecs for arena-keyed lookups** — If your keys are already arena indices (`PosIdx`, `LocIdx`, `StrIdx`), use `Vec<Option<u32>>` indexed by the raw index value. O(1) with no hashing, no pointer chasing, and the Vec can be pre-sized from the arena count.

- **Pre-allocate output buffers** — Binary output size correlates with source size. Pre-allocate based on a heuristic (e.g., 4x source bytes) rather than growing from a small default.

#### Measurement

- **Always benchmark with `hyperfine`** — Every performance change must have before/after numbers. "Should be faster" is not evidence. Use `hyperfine` with multiple runs and a representative `--prepare` step for clean-build measurements, then report the mean, standard deviation, and min/max range.

- **Profile before optimizing** — Use flamegraphs (`cargo flamegraph`), `perf stat` (cache misses, branch misses), or DHAT (heap profiling) to find actual bottlenecks. Don't guess.

- **Measure struct sizes** — Add `assert_eq!(std::mem::size_of::<T>(), N)` tests for critical types. Enum size regressions (someone adds a large variant) silently degrade cache performance across the entire codebase.

## Coding Conventions

### Naming

- **OCaml code**: snake_case (e.g., `to_string`)
- **ReScript code**: camelCase (e.g., `toString`)

### Commit Standards

- Sign off every commit with `Signed-off-by: Your Name <email>` (DCO)
- Put the sign-off in the final paragraph of the message, next to any other
  trailers such as `Co-Authored-By:`, with no blank line between them. Git only
  parses the last paragraph as trailers, so a sign-off separated by a blank
  line doesn't count. Check with
  `git log -1 --format=%B | git interpret-trailers --parse`.
- Include appropriate tests with all changes
- Build must pass before committing
- **Commit atomically** - Each commit should address exactly one concern (one bug fix, one feature, one refactor). When making multiple related changes, split them into separate atomic commits. For example, if fixing a parity issue requires adding a new field to a struct and then using that field in parsing logic, make two commits: one for the struct change, one for the parsing logic. This makes it easier to review changes, bisect issues, revert specific changes if needed, and understand the evolution of the codebase. Each commit message should clearly describe what was changed and why.
- Write each commit message as a record in the format of
  [`.agents/skills/records/SKILL.md`](.agents/skills/records/SKILL.md), and
  render review pages from records with `make semantic-diff`
- Every commit needs a description below its subject: a line or two of
  prose or a `Why:` section. This includes small follow-ups like adding a
  changelog fragment or fixing CI; a subject alone fails the Semantic Diff
  check (`node scripts/commitRecords.js --check origin/master..HEAD`)

### Stacked pull requests

When a PR depends on another unmerged PR, make a native GitHub stack. Keep the
branches linear and in the same repository, then run `gh stack link BOTTOM
[NEXT...]`, listing the stack bottom to top. Each argument is a branch name or
a PR number: the command pushes each branch, reuses the PR that already exists
for it, and opens one where there is none, so branches alone are enough. Open
the PRs yourself first if you want to write their titles and descriptions.

Linking sets each PR's base to the branch below it, leaving only the bottom PR
on `master`. CI runs on every PR in the stack.

### Code Quality

- Follow existing patterns in the codebase
- Prefer existing utility functions over reinventing
- Comment complex algorithms and non-obvious logic
- Maintain backward compatibility where possible

## Development Environment

- **OCaml**: 5.5.0+ with opam
- **Build System**: dune with profiles (dev, release, browser)
- **JavaScript**: Node.js 20+ for tooling
- **Rust**: Toolchain needed for rewatch

## Common Tasks

### Adding New Language Features

1. Update parser in `compiler/syntax/`
2. Update AST definitions in `compiler/ml/`
3. Implement type checking in `compiler/ml/`
4. Add Lambda IR handling in `compiler/core/lam_*`
5. Implement JS generation in `compiler/core/js_*`
6. Add comprehensive tests

### Debugging Compilation Issues

1. Identify which compilation phase has the issue
2. Use appropriate debugging flags (`-dparsetree`, `-dtypedtree`)
3. Check intermediate representations
4. Add debug output in relevant compiler modules
5. Verify with minimal test cases

### Working with Lambda IR

- Remember Lambda IR is the core optimization layer
- All `lam_*.ml` files process this representation
- Use `lam_print.ml` for debugging lambda expressions
- Test both with and without optimization passes

## Working on the Build System

### Rewatch Architecture

Rewatch is ReScript's build system written in Rust. It provides fast incremental builds, better error messages, and improved developer experience.

#### Key Components

```
rewatch/src/
├── build/              # Core build system logic
│   ├── build_types.rs  # Core data structures (BuildState, Module, etc.)
│   ├── compile.rs      # Compilation logic and bsc argument generation
│   ├── parse.rs        # AST generation and parser argument handling
│   ├── packages.rs     # Package discovery and dependency resolution
│   ├── deps.rs         # Dependency analysis and module graph
│   ├── clean.rs        # Build artifact cleanup
│   └── logs.rs         # Build logging and error reporting
├── cli.rs              # Command-line interface definitions
├── config.rs           # rescript.json configuration parsing
├── watcher.rs          # File watching and incremental builds
└── main.rs             # Application entry point
```

#### Build System Flow

1. **Initialization** (`build::initialize_build`)
   - Parse `rescript.json` configuration
   - Discover packages and dependencies
   - Set up compiler information
   - Create initial `BuildState`

2. **AST Generation** (`build::parse`)
   - Generate AST files using `bsc -bs-ast`
   - Handle PPX transformations
   - Process JSX

3. **Dependency Analysis** (`build::deps`)
   - Analyze module dependencies from AST files
   - Build dependency graph
   - Detect circular dependencies

4. **Compilation** (`build::compile`)
   - Generate `bsc` compiler arguments
   - Compile modules in dependency order
   - Handle warnings and errors
   - Generate JavaScript output

5. **Incremental Updates** (`watcher.rs`)
   - Watch for file changes
   - Determine dirty modules
   - Recompile only affected modules

### Development Guidelines

#### Adding New Features

1. **CLI Arguments**: Add to `cli.rs` in `BuildArgs` and `WatchArgs`
2. **Configuration**: Extend `config.rs` for new `rescript.json` fields
3. **Build Logic**: Modify appropriate `build/*.rs` modules
4. **Thread Parameters**: Pass new parameters through the build system chain
5. **Add Tests**: Include unit tests for new functionality

#### Common Patterns

- **Parameter Threading**: New CLI flags need to be passed through:
  - `main.rs` → `build::build()` → `initialize_build()` → `BuildState`
  - `main.rs` → `watcher::start()` → `async_watch()` → `initialize_build()`

- **Configuration Precedence**: Command-line flags override `rescript.json` config
- **Error Handling**: Use `anyhow::Result` for error propagation
- **Logging**: Use `log::debug!` for development debugging

#### Testing

```bash
# Run rewatch tests (from project root)
cargo test --manifest-path rewatch/Cargo.toml

# Test specific functionality
cargo test --manifest-path rewatch/Cargo.toml config::tests::test_get_warning_args

# Run clippy for code quality
cargo clippy --manifest-path rewatch/Cargo.toml --all-targets --all-features

# Check formatting
cargo fmt --check --manifest-path rewatch/Cargo.toml

# Build rewatch
cargo build --manifest-path rewatch/Cargo.toml

# Or use the Makefile shortcuts
make rewatch          # Build rewatch
make test-rewatch     # Run integration tests
```

**Note**: The rewatch project is located in the `rewatch/` directory with its own `Cargo.toml` file. All cargo commands should be run from the project root using the `--manifest-path rewatch/Cargo.toml` flag, as shown in the CI workflow.

**Integration Tests**: The `make test-rewatch` command runs bash-based integration tests located in `rewatch/tests/suite.sh`. These tests use the `rewatch/testrepo/` directory as a test workspace with various package configurations to verify rewatch's behavior across different scenarios.

**Running Individual Integration Tests**: You can run individual test scripts directly by setting up the environment manually:

```bash
cd rewatch/tests
export REWATCH_EXECUTABLE="$(realpath ../target/debug/rescript)"
eval $(node ./get_bin_paths.js)
export RESCRIPT_RUNTIME
source ./utils.sh
bash ./watch/06-watch-missing-source-folder.sh
```

This is useful for iterating on a specific test without running the full suite.

#### Debugging

- **Build State**: Use `log::debug!` to inspect `BuildState` contents
- **Compiler Args**: Check generated `bsc` arguments in `compile.rs`
- **Dependencies**: Inspect module dependency graph in `deps.rs`
- **File Watching**: Monitor file change events in `watcher.rs`

#### OpenTelemetry Tracing

Rewatch supports OpenTelemetry (OTEL) tracing for build and watch commands. To visualize traces locally, run a Jaeger all-in-one container:

```bash
docker run -d --name jaeger \
  -p 4317:4317 -p 4318:4318 -p 16686:16686 \
  jaegertracing/all-in-one
```

Then run rewatch with the OTLP endpoint set:

```bash
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4318 cargo run --manifest-path rewatch/Cargo.toml -- build
```

Open http://localhost:16686 to view traces in the Jaeger UI.

Note: Use `tracing::debug!` (not `log::debug!`) for events you want to appear in OTEL traces — they use separate logging systems.

##### Honored environment variables

Rewatch follows the OTEL spec for configuration — no rewatch-specific knobs exist.

| Variable | Purpose |
|---|---|
| `OTEL_EXPORTER_OTLP_ENDPOINT` | Base endpoint of the collector (e.g. `http://localhost:4318`). `/v1/traces` is appended for the trace exporter. Setting this (or `OTEL_EXPORTER_OTLP_TRACES_ENDPOINT`) is what enables telemetry — if neither is set, tracing is a no-op. |
| `OTEL_EXPORTER_OTLP_TRACES_ENDPOINT` | Full trace endpoint used verbatim. Overrides the general endpoint for traces. |
| `OTEL_EXPORTER_OTLP_HEADERS` | Extra headers on exporter requests (e.g. `authorization=Bearer xyz`). |
| `OTEL_SERVICE_NAME` | Service name reported on spans. Defaults to `rewatch`. |
| `OTEL_RESOURCE_ATTRIBUTES` | Comma-separated `key=value` pairs added as resource attributes (e.g. `deployment.environment=ci,host.name=$HOSTNAME`). |
| `RUST_LOG` | Controls which span/event levels are captured (e.g. `RUST_LOG=info`, `RUST_LOG=rewatch=debug`). Defaults to `debug` when telemetry is enabled. |

#### Running Rewatch Directly

When running the rewatch binary directly (via `cargo run` or the compiled binary) during development, point it at the local runtime. Otherwise, rewatch will try to use the installed version:

```bash
# Set the runtime path
export RESCRIPT_RUNTIME=$(realpath packages/@rescript/runtime)

# Now you can run rewatch directly
cargo run --manifest-path rewatch/Cargo.toml -- build
```

Builds compile in-process with the Rust compiler linked into rewatch: they
write the JavaScript plus the `.cmi`/`.cmt`/`.cmti` files editor tooling reads,
and need no `bsc` executable. One-shot builds recompile every module (watch
mode keeps state in memory).

Note that the dev binary is `./rewatch/target/debug/rescript`, not `rewatch`. The binary name is `rescript` because that's the package name in `Cargo.toml`.

This is useful when testing rewatch changes against local compiler modifications without running a full `make` build cycle.

Use `-v` for info-level logging or `-vv` for debug-level logging (e.g., to see which folders are being watched in watch mode):

```bash
cargo run --manifest-path rewatch/Cargo.toml -- -vv watch <folder>
```

#### Performance Considerations

- **Incremental Builds**: Only recompile dirty modules
- **Parallel Compilation**: Use `rayon` for parallel processing
- **Memory Usage**: Be mindful of `BuildState` size in large projects
- **File I/O**: Minimize file system operations

#### Performance vs Code Quality Trade-offs

When clippy suggests refactoring that could impact performance, consider the trade-offs:

- **Parameter Structs vs Many Arguments**: While clippy prefers parameter structs for functions with many arguments, sometimes the added complexity isn't worth it. Use `#[allow(clippy::too_many_arguments)]` for functions that legitimately need many parameters and where a struct would add unnecessary complexity.

- **Cloning vs Borrowing**: Sometimes cloning is necessary due to Rust's borrow checker rules. If the clone is:
  - Small and one-time (e.g., `Vec<String>` with few elements)
  - Necessary for correct ownership semantics
  - Not in a hot path

  Then accept the clone rather than over-engineering the solution.

- **When to Optimize**: Profile before optimizing. Most "performance concerns" in build systems are negligible compared to actual compilation time.

- **Avoid Unnecessary Type Conversions**: When threading parameters through multiple function calls, use consistent types (e.g., `String` throughout) rather than converting between `String` and `&str` at each boundary. This eliminates unnecessary allocations and conversions.

### Common Tasks

#### Adding New CLI Flags

1. Add to `BuildArgs` and `WatchArgs` in `cli.rs`
2. Update `From<BuildArgs> for WatchArgs` implementation
3. Pass through `main.rs` to build functions
4. Thread through build system to where it's needed
5. Add unit tests for the new functionality

#### Modifying Compiler Arguments

1. Update `compiler_args()` in `build/compile.rs`
2. Consider both parsing and compilation phases
3. Handle precedence between CLI flags and config
4. Test with various `rescript.json` configurations

#### Working with Dependencies

1. Use `packages.rs` for package discovery
2. Update `deps.rs` for dependency analysis
3. Handle both local and external dependencies
4. Consider dev dependencies vs regular dependencies

#### File Watching

1. Modify `watcher.rs` for file change handling
2. Update `AsyncWatchArgs` for new parameters
3. Handle different file types (`.res`, `.resi`, etc.)
4. Consider performance impact of watching many files

## CI Gotchas

- **`sleep` is fragile** — Prefer polling (e.g., `wait_for_file`) over fixed sleeps. CI runners are slower than local machines.
- **`exit_watcher` is async** — It only signals the watcher to stop (removes the lock file), it doesn't wait for the process to exit. Avoid triggering config-change events before exiting, as the watcher may start a concurrent rebuild.
- **`sed -i` differs across platforms** — macOS requires `sed -i '' ...`, Linux does not. Use the `replace` / `normalize_paths` helpers from `rewatch/tests/utils.sh` instead of raw `sed`.

---

## OCaml to Rust Compiler Rewrite

The compiler is being rewritten from OCaml to Rust. This is a major undertaking documented in the `compiler-rust/` directory.

### Key Documents

All project documentation is organized under **[projects/](projects/PROJECTS.md)**:

- **[projects/compiler-rewrite/](projects/compiler-rewrite/)** - OCaml-to-Rust compiler rewrite (PLAN, PROGRESS, GLOBAL_STATE_AUDIT, BINARY_AST)
- **[projects/parser-parity/](projects/parser-parity/)** - Parser AST and binary parity (PLAN, tasks, agent docs)
- **[projects/parser-performance-engineering/](projects/parser-performance-engineering/)** - Parser performance engineering (PLAN, PROGRESS)
- **[projects/raw-lambda-parity/](projects/raw-lambda-parity/)** - Unoptimized lambda parity (agent docs, setup, tracker)
- **[projects/optimized-lambda-parity/](projects/optimized-lambda-parity/)** - Optimized lambda parity (agent docs, setup, tracker)
- **[projects/printer-parity/](projects/printer-parity/)** - Printer/formatter parity (PLAN, formatter, agent docs)
- **[projects/comptime/](projects/comptime/)** - Compile-time metaprogramming design

> **Note for AI assistants**: These documents are living documents. Update the relevant project's PLAN.md and PROGRESS.md as you make progress. See [projects/PROJECTS.md](projects/PROJECTS.md) for the full index.

### Rewrite Constraints

1. **No global state** - The Rust compiler must support concurrent compilation
2. **Drop-in replacement** - Must be backward compatible at all times
3. **Identical output** - JavaScript output must be byte-for-byte identical

### Migration Phases

1. **Phase 1: Foundation** - Core types, contexts, FFI boundary (`compiler/ext/` → Rust)
2. **Phase 2: Parser** - ReScript parser in Rust (`compiler/syntax/` → Rust)
3. **Phase 3: Backend** - Lambda IR and JS generation (`compiler/core/` → Rust)
4. **Phase 4: Type Checker** - Type system in Rust (`compiler/ml/` → Rust)
5. **Phase 5: Integration** - Single Rust binary, OCaml removed

### Development Commands

```bash
# Build the Rust compiler crate
cargo build --manifest-path compiler-rust/Cargo.toml

# Run tests
cargo test --manifest-path compiler-rust/Cargo.toml

# Run tests with thread sanitizer (nightly)
RUSTFLAGS="-Z sanitizer=thread" cargo test --manifest-path compiler-rust/Cargo.toml

# Check for issues
cargo clippy --manifest-path compiler-rust/Cargo.toml --all-targets
```

### Following the Reference Implementation

**CRITICAL PRINCIPLE**: The Rust parser is a **1:1 rewrite** of the OCaml parser. All logic must be the same, translated into idiomatic Rust. The **only** architectural difference is eliminating global state to enable parallel compilation. Do not "improve" algorithms, change data structures, or deviate from the OCaml implementation's approach—even if you think there's a better way. Parity is the priority; optimizations can come later after we have identical behavior.

**IMPORTANT**: When implementing features in the Rust compiler, always compare against the OCaml reference implementation:

1. **Lambda IR comparison** - Use `-drawlambda` on both compilers to compare the intermediate representation
2. **JS output comparison** - The Rust compiler should produce functionally equivalent (ideally identical) JavaScript output
3. **Study the OCaml code** - When in doubt, read the corresponding OCaml implementation in `compiler/core/` (for Lambda/JS) or `compiler/ml/` (for type checking)
4. **Test with the same inputs** - Run both compilers on the same `.res` files to verify behavior matches

The goal is byte-for-byte identical output where possible, or at minimum functionally equivalent output.

- **Investigate parity differences at the source** - When you find a difference between Rust and OCaml output, don't just try to match the output superficially. Read the corresponding OCaml implementation to understand *why* it produces that output. The root cause is often in a different place than where the symptom appears.

- **Study the OCaml code, not just the output** - When fixing parity issues, you must read and understand the actual OCaml implementation, not just try to reverse-engineer what it does from the output. The goal is to create an *equivalent* Rust implementation that follows the same logic and handles the same edge cases. Simply tweaking Rust code until the output matches is fragile and will miss subtle behaviors. Understand the algorithm, data structures, and invariants in the OCaml code first, then write idiomatic Rust that achieves the same result.

- **Stay focused on hard parity issues** - If achieving parity requires a significant change (refactoring, adding new infrastructure, rethinking an approach), do that work rather than abandoning it for simpler issues. The end goal is 100% parity, and all issues must eventually be fixed. Switching between tasks loses valuable context about the problem you were investigating. It's better to complete a difficult task—even if it takes substantial effort—than to context-switch repeatedly and never finish the hard parts.

- **Commit parity improvements atomically** - When parity increases (more tests pass), commit immediately with atomic commits. Each commit should address one specific fix (e.g., "fix location for recursive module declarations" not "fix various location issues"). This creates a clear history of progress, makes it easy to bisect regressions, and ensures no work is lost. If a fix requires multiple steps (e.g., adding a struct field, then using it), make separate commits for each step.

### Key Design Decisions

- **Thread-safe ID generation** - `IdGenerator` with `AtomicI32` instead of global `currentstamp`
- **Explicit contexts** - `CompilationContext`, `TypeContext` passed through pipeline
- **Arena-per-compilation** - Type arenas owned by `TypeContext`, not shared
- **No `static mut`** - All mutable state in explicit contexts
