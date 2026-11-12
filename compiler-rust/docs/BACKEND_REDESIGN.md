# Backend redesign: one arena IR, printed by oxc

Status: design, not implemented. This document is the specification the staged
pull requests in section H are built from.

Scope: everything between the typed tree and the JavaScript file in
`compiler-rust/`: raw Lambda conversion and match compilation
(`src/raw_lambda/`), the Lambda passes and Lambda-to-JS compilation
(`src/lambda/`), the JS IR, its passes and its printer (`src/js_ir/`), and the
per-module summaries a dependent module reads.

Conventions: code is cited by file and function, never by line. "Measured"
means a number from a profile or an experiment; "estimated" means derived
arithmetic or judgement; "unknown" means the code does not answer the question
and an experiment is named that would.

## 0. Summary

### 0.1 Goal and budget

Measured, one worker, clean build of a 3,735-module application (619,000
source lines, about 900,000 emitted JavaScript lines, 1.45 emitted lines per
source line): 123,000 retired instructions per source line. The backend is
27.3% of that, about 33,600 instructions per source line. The target for the
whole build is 28,000 per line, of which the backend may spend about 9,000.

| Stage of today's backend | Share of build (measured) | Instructions per source line |
| --- | ---: | ---: |
| Typed tree to raw Lambda (about half is match compilation) | 7.1% | 8,700 |
| Lambda passes | 6.8% | 8,400 |
| Lambda to JS IR, JS passes | 7.7% | 9,500 |
| Printing (includes choosing identifier names) | 4.7% | 5,800 |
| Writing files | 0.6% | 700 |
| Other (summaries, bookkeeping) | 0.4% | 500 |
| Total | 27.3% | 33,600 |

About a fifth of backend time is collecting into vectors and copying them
(measured). oxc's printer prints the application's whole output in 0.59 G
instructions, 660 per emitted line, about 950 per source line (measured);
today's printer spends about 4,300 per emitted line.

Budget for the new backend (estimated; each line is the gate of a stage in
section H):

| Part of the new backend | Instructions per source line | Share of today's build |
| --- | ---: | ---: |
| Typed tree to IR, including match compilation | 2,900 | 2.4% |
| Rewrites (today's Lambda passes) | 1,800 | 1.5% |
| Lowering to JavaScript-level nodes and JS-level rewrites | 2,000 | 1.6% |
| Naming, building the oxc AST, `oxc_codegen` | 1,600 | 1.3% |
| Writing files (unchanged) | 700 | 0.6% |
| Total | 9,000 | 7.3% |

### 0.2 The design in one page

1. One arena, `Bir` (backend IR), holds a module from the typed tree to the
   oxc AST. Nodes are 16 bytes, mutable in place, and form a tree: each node
   has exactly one parent. Variables are rows of a table with a use count,
   flags and a "bound to" fact, kept current by the only functions that may
   edit the tree.
2. The arena has two levels of operations, and this is a correction to the
   direction this design started from. Output-visible decisions are made at two
   abstraction levels today, on Lambda (what is inlined, which binding is
   removed, how an exit is shared) and on JavaScript (statement or expression,
   which declaration is dead after lowering, which helper call a primitive
   becomes). They cannot be merged into one level without changing output.
   What is merged is storage, traversal, use counts and effect flags. Level L
   holds language-level nodes, level J holds JavaScript-shaped nodes, and
   lowering L to J rewrites the tree in the same arena.
3. Today's passes become rules in two classes. Normalising rules are today's
   smart constructors (`LamArena::prim`, `if_`, `seq`, `switch`, `apply`,
   and `js_exp_make`; `let_` builds its node as given); they run when a node
   is created and when a round's sweep returns to an ancestor of a rewrite
   (C.1, C.6). Pass rules are the bodies of today's passes; they run in rounds,
   one ordered sweep per round, in the order of today's pipeline. A sweep
   visits only subtrees that can contain a candidate and edits in place. The
   fixed order of rounds is kept wherever section C cannot show independence.
4. The match compiler keeps its algorithm (which tests are made in which
   order is output) and changes what it writes: decision trees as `Bir` nodes,
   with action sharing by structural hash instead of key strings.
5. The last step chooses names (a scope walk that reproduces
   `Ext_pp_scope`), builds an oxc AST in a per-worker allocator and prints it
   with `oxc_codegen`. Every decision today's printer makes that is not
   layout moves into this step or earlier.
6. The correctness gate is reformat-and-compare: the reference output is
   reformatted once with the same oxc printer and compared byte for byte.
7. The new backend is built beside the old one, back to front: printer first,
   then lowering, then rewrites, then conversion. Each stage has the old code
   as its oracle, takes over module by module (a module the new code does not
   fully support falls back), and deletes the code it replaces.

### 0.3 Stages

| Stage | Change | Expected saving, share of today's build |
| --- | --- | ---: |
| S0 | Gate tooling: reformat modes, corpus runner | 0 |
| S1 | oxc printer on today's JS IR | 2.8% |
| S2 | `Bir` arena, editing API, validator, dump | 0 |
| S3 | Level J: Lambda to JS in `Bir`, JS passes as rules | 6.3% |
| S4 | Level L rewrites: Lambda passes as rounds | 5.4% |
| S5 | Typed tree to `Bir`, match compilation into `Bir` | 5.1% |
| S6 | Per-module summaries from `Bir` | 0.4% |
| S7 | Type checker emits `Bir` for uninspected modules | outside the backend budget |

All savings are estimates; they add up to the 20.0% between today's 27.3%
and the budget's 7.3%. Section H gives the arithmetic.

## A. Today's pipeline

### A.1 Control flow

One module's backend run is driven from `src/driver.rs`:

1. `compile_preprocessed_structure_in_process_until_js` runs the type checker,
   then, under `timing::Phase::Lambda`:
   - `raw_lambda::convert::RawLambdaConverter::convert_structure_with_coercion`
     (typed tree to raw Lambda in a `RawArena`),
   - `raw_lambda::lower::lower_to_translmod_lambda` (raw Lambda to the
     optimised-Lambda arena `lambda::arena::LamArena`),
   - `lambda::lam_pass_collapse_var_aliases::collapse`,
   - `lambda::lam_compile::collect_possible_required_modules_in_arena`.
   The result is `InProcessPreJsCompileResult`. The build system may resume
   the rest on another worker thread, so the identifier counter is carried
   across (`ident_stamp_at_js_boundary`).
2. `finish_preprocessed_structure_in_process_from_js_boundary_with_metadata_hook`
   builds one `LambdaCompiler` per output target (`js_backend_compiler`) and
   calls `LambdaCompiler::compile_deps_program_in_arena`
   (`src/lambda/lam_compile.rs`), which:
   - simplifies (`lam_compile_main::simplify_in_arena`, under
     `Phase::LambdaOptimization`),
   - adds flat `make` export aliases (`add_flat_make_aliases`),
   - computes the summaries dependents read (section A.6),
   - compiles to JS IR (`compile_expr`), coerces exports, runs six JS passes
     and computes the import list.
3. `render_js_program` prints each target with
   `js_ir::program_printer::print_deps_program_with_directives_and_options`
   or `print_deps_program_with_source_map`.

A project with several output targets (module formats or suffixes) runs step
2 once per target from a clone of the lowered Lambda arena
(`compile_js_program_for_output`), because import paths are resolved while
compiling.

Three arenas are filled and two whole-term copies are made on the way:
`RawArena` to `LamArena` (`lower`), `LamArena` to `JsArena` (`compile_expr`),
and `JsArena` to text. `LamArena` and `JsArena` are append-only: a pass that
changes a node pushes a new node and rebuilds the spine above it, and an
unchanged subtree keeps its handle, which may then have several parents.

### A.2 Typed tree to raw Lambda

`src/raw_lambda/convert.rs` (`RawLambdaConverter`) is a port of
`translcore.ml` and `translmod.ml`. It reads the typed tree arena
(`types::tast_arena`), the type context and the environment, and writes raw
Lambda nodes.

Output-visible decisions made here:

| Decision | Function |
| --- | --- |
| Shape of every expression: which primitive a typed operation becomes, argument evaluation order (`let` temporaries for arguments), currying and uncurrying of applications | `RawLambdaConverter` (`transl_*` methods, `transl_apply_raw`) |
| Names of the temporaries it creates (`match`, `param`, `x`, ...) and the order they are created in | same, through its identifier generator |
| Block shapes and tags: records, inline records, variants, `option` nesting (`Blk_some_not_nested`) | `raw_lambda/typeopt.rs`, `types/variant_layout.rs`, `types/record_runtime.rs` |
| `let rec` groups split into recursive clusters, non-recursive members demoted | `raw_lambda/lambda_scc.rs` |
| JSX elements | `raw_lambda/convert/jsx.rs` |
| Module coercions, export list and its order, the flat `make` export paths | `convert_structure_with_coercion`, `check_flat_make_exports` |
| Externals: how an FFI call is spelled | attributes read here, compiled in `lam_compile_external.rs` |

Match compilation (`src/raw_lambda/matching.rs`, a port of `matching.ml`;
entry points `for_function`, `for_let`, `for_trywith`, `for_multiple_match`,
`for_tupled_function`, `compile_matching`) is about half of this stage
(measured). It reads typed patterns through `PatArena` and writes `switch`,
`if`, static catch and static raise nodes:

| Decision | Function |
| --- | --- |
| Column and row order, splitting into or-groups, variable and constructor groups | `split_precompile`, `Split`, `simplify_cases`, `simplify_or` |
| Which test is made at each step and how cases are divided | `divide`, `divide_line`, `do_compile_matching` |
| Sharing of equal actions and creation of exits (`staticcatch` labels) | `StoreExp`, `make_key` (keys are strings built by `key_encode.rs`), `make_catch`, `make_exit`, `comp_exit`, `comp_match_handlers` |
| Whether a failure branch exists, from the checker's `partial` flag and from contexts and jump summaries | `check_partial_list`, `Ctx`, `Jumps`, `jumps_union` |
| Dense switch or tree of comparisons for integers, and its thresholds | `raw_lambda/switch.rs` |
| Constructor, constant, variant and array dispatch forms | `combine_constructor`, `combine_constant`, `combine_variant`, `combine_array` |
| Tuple flattening for multiple matches | `flatten_pattern`, `compile_flattened` |

Order dependence: clause order and column choice are the algorithm. Exit
labels are numbered in creation order (`bump_raise_count`); labels are not
printed, but later passes key on them, and a negative label marks an exit that
must not be inlined (`lam_pass_exits`, test `i >= 0`).

### A.3 Raw Lambda to Lambda

`raw_lambda::lower::lower_to_translmod_lambda` is the port of
`Lam_convert.convert`. One walk; reads the raw arena, writes `LamArena`.

| Decision | Function |
| --- | --- |
| Constant forms (pointers, polymorphic-variant hashes, strings) | `lower_constant`, `polyvar_block_tag_constant` |
| Primitive rewriting and constant folding at construction | `lower_primitive_default`, `fold_constants`, and the smart constructor `LamArena::prim` |
| `f(x)` where `f` is an immediately applied function: eta reduction | `eta_reduce_function_apply`, `make_apply` |
| Module alias blocks collapsed to the module | `collapse_module_alias` |
| Exceptions wrapped for JS interop | `wrap_exn_raw` |
| Export identifiers of the module | `collect_exported_idents` |

Then `lam_pass_collapse_var_aliases::collapse` removes `let x = y` bindings
(one walk).

### A.4 Lambda passes

`lam_compile_main::simplify_in_arena` runs this sequence. "Walks" counts
whole-term traversals. Every pass reads and appends to the one `LamArena`;
`meta` is `LamStats` (`ident_tbl`, export set, identifier generator).

| # | Pass (function) | Walks | Reads | Writes | Output-visible decisions |
| ---: | --- | ---: | --- | --- | --- |
| 1 | `deep_flatten` | 1 | term | term, fresh ids | see P1 below |
| 2 | `collect_info_with_external_arity` | 1 | term, dependents' arities | `meta.ident_tbl` | none itself; feeds 5, 8, 11, 14 |
| 3 | `simplify_exits` | 2 if any static catch | term | term, fresh ids | see P2 |
| 4 | `collect_info` | 1 | | `ident_tbl` | |
| 5 | `simplify_alias` | 1 (+1 for assigned variables) | term, `ident_tbl`, dependents' closed lambdas | term, fresh ids, `ident_tbl` | see P3 |
| 6 | `deep_flatten` | 1 | | | P1 |
| 7 | `collect_info` | 1 | | | |
| 8 | `simplify_alias` | 2 | | | P3 |
| 9 | `deep_flatten` | 1 | | | P1 |
| 10 | `collect_info` | 1 | | | |
| 11 | `alpha_conversion` | 1 | term, arities | term, fresh ids | see P4 |
| 12 | `simplify_exits` | 2 | | | P2 |
| 13 | `collect_info` | 1 | | | |
| 14 | `simplify_alias` | 2 | | | P3 |
| 15 | `simplify_lets` | 3 (assigned, count, rewrite) | term | term | see P5 |
| 16 | `lam_pass_sroa::simplify` | 1 plus per candidate | term | term, fresh ids | see P6 |
| 17 | `simplify_exits` | 2 | | | P2 |
| 18 | `guard_raises` | 1 | term | term | `if a then raise e else c` becomes a guard followed by `c` |
| 19 | `handle_exports` | spine | term, `meta` | term, export list | see P7 |

About 25 whole-term walks, five of which only refill `ident_tbl`. OCaml's
second `alpha_conversion` is not run (it rewrote nothing in 3,355 modules, as
the comment in `simplify_in_arena` records).

Smart constructors (`LamArena::prim`, `if_`, `seq`, `switch_with`,
`string_switch_with`, `apply`) fold at construction; `let_` and the others
build their node as given (C.5 lists every rewrite). A pass that rebuilds a
node through `shallow_map` rebuilds applications, primitives and both
switches through their smart constructor and every other node plainly, so
folding cascades up along rebuilt spines at those four kinds of node; a
pass that wants `if_` or `seq` on a rebuilt node calls it itself.

**P1 `deep_flatten`** (`lam_pass_deep_flatten.rs`: `flatten`, `aux`,
`regroups_binding`, `eliminate_tuple`, `lambda_of_groups`). Flattens nested
`let` and sequences into a group list and folds it back through
`lam_util::refine_let`. Decisions: a binding named `match`, `include` or
`param` whose value is an immutable block and whose body only projects it is
replaced by one binding per field (the test is on the identifier's name);
`nullable` conversions of non-variables get a fresh temporary
(`Ident::rename`); pure sequence heads are dropped; beta-reduction residue
(`rhs_is_beta_residue`) is deliberately left nested so that pass 15 can
substitute it back. `refine_let` decides the let kind (`Alias`, `StrictOpt`,
`Strict`) and three peepholes (`let x = e in x`, `let x = e in prim(x)`,
`let x = e in f(x)`).

**P2 `simplify_exits`** (`lam_pass_exits.rs`: `count`, `subst_helper`). A
static catch is removed when its label is never raised; its handler is
substituted at the raise sites when the handler is a variable or constant, or
the label is raised once and is non-negative, or the handler has no bound
variables and is small (`size_upto` against `EXIT_INLINE_SIZE`, with at most
two raises, or size below 5). Handler parameters are renamed per substitution
(`Ident::rename`). The count has two quirks that are part of the decision: a
switch default is counted twice when neither case table is full, and a
handler is counted only if its label was raised in the body.

**P3 `simplify_alias`** (`lam_pass_remove_alias.rs`: `Simplifier::simpl`,
`simpl_prim`, `simpl_apply`; `lam_beta_reduce.rs`; `lam_util::field_flatten_get`).
Reads `ident_tbl` as collected before the pass.
- Field of a variable bound to a known block or module becomes the field
  value.
- `if` on a variable known to be true or false, and `if isSome(v)` on a
  known option, are folded; a string switch on a variable bound to a constant
  switches on the constant.
- Unwrapping a known `Some`.
- Inlining. A call of a variable bound to a function is inlined when
  `lfunction_can_be_inlined` and `ok_to_inline_fun_when_app` hold (size and
  argument tests), the function is closed over exports where it is exported
  (`is_closed_with_map`), it is not self-recursive, no argument mentions it,
  and the nesting depth is below `MAX_INLINE_DEPTH` (4) unless it is
  `@inline`. Functors are always reduced. A call of a field of another module
  is inlined from that module's closed lambdas when cross-module inlining is
  on. The reduced body is simplified again in place.
- Beta reduction (`propagate_beta_reduce_with_map`) decides, per parameter,
  substitution or a `let`, from how often and where the parameter is used
  (`lam_closure::free_variables_with_stats`) and from evaluation-order
  constraints (`motion`, `conflict`, `read_before_effects`); it renames every
  binder of the copied body (`rewrite_bounded_vars`).
- In JSX preserve mode a JSX tag that is a module field is left alone.

**P4 `alpha_conversion`** (`lam_pass_alpha_conversion.rs`:
`populate_apply_info`, `transform_under_supply`). From the arity of the
callee (`lam_pass_collect::get_arity_with_external_arity`): a full
application is marked `InferFull` (it prints as a direct call instead of a
curried helper call), an over-application is split in two calls, an
under-application becomes a closure with fresh `param` identifiers, and
operands that are not safe to share get `partial_arg` temporaries.

**P5 `simplify_lets`** (`lam_pass_lets_dce.rs`: `collect_occurs`, `count`,
`LetsState::simplif`, `simplif_alias`). Counts uses, then: an unused `Alias`
or `StrictOpt` binding is dropped; an unused `Strict` binding keeps its value
as a sequence head unless `no_side_effects`; an `Alias` binding is substituted
when used once and not under a function or loop, or used once under one and
its value is a variable or non-allocating constant, or its value is a small
constant or a field of a global module; immediately applied functions are
reduced (`no_names_beta_reduce`); string constants are concatenated at
compile time through a table of string-valued variables. The count's quirks
are part of the decision: uses inside the value of a binding that is itself
unused are not counted (unless `Strict`), a switch default counts twice when
neither table is full, an alias adds its count to its target
(`inherit_use`), and a use under a function, `for` body or `while` sets
`captured`.

**P6 `lam_pass_sroa`** (`analyze`, `rewrite`, `replace`). A local mutable
block whose every use is a statically indexed read or write becomes one
mutable variable per field (fresh identifiers).

**P7 `handle_exports`** (`lam_compile_main.rs`). Every export whose value is
not a variable of the same name gets a fresh identifier with the export's
name and a binding just outside the export block. `add_flat_make_aliases`
appends `A$B$make` aliases and extends the export list.

Order dependence of the passes is the subject of section C.2.

### A.5 Lambda to JS IR

`LambdaCompiler::compile_expr` and the files `lam_compile.rs`,
`lam_compile_primitive.rs`, `lam_compile_external.rs`,
`lam_compile_arguments.rs`, `lam_compile_const.rs`, `lam_compile_variant.rs`,
`untagged_dispatch.rs`, `js_exp_make.rs`, `js_stmt_make.rs`,
`lam_coercion.rs` (about 15,000 lines) are the counterpart of OCaml's
`lam_compile.ml` and `js_exp_make.ml`. One recursive walk of the simplified
Lambda that builds a `JsArena`. Unlike OCaml, which threads a continuation
value, the Rust code has one function per context
(`compile_effect_block_inner`, `compile_return_output_inner`,
`compile_assign_to_target_output`, `compile_let_binding_output`,
`compile_tail_loop_return_output_inner`, ...). The result of an expression is
`Compiled { prelude, expr, finished }` and of a statement context
`BlockOutput { block, finished }`, where `finished` is OCaml's
`Js_output.output_finished` (control has left: `return`, `throw`, `break`,
`continue`).

Before `compile_expr`, on the simplified Lambda:
`drop_toplevel_pure_sequence_heads`, `lambda_traverse::arena_assigned_variables`
(which variables are assigned), `lam_compile_main::awaited_units`.

| Decision | Function |
| --- | --- |
| Statement or expression: `if` as `?:`, `&&`, `\|\|` or an `if` statement; a value that needs statements gets a declared temporary | `compile_if_*`, `compile_short_circuit_*`, `compile_declared_if_block`, `lambda_contains_statement_value_form` |
| `let` becomes a declaration; merging a declaration with the assignment that follows | `compile_let_binding_output`, `prepend_declaration_or_fold_final_assignment` |
| Return context: `return e`, falling off the end for unit, `return` folded into branches | `compile_return_output_inner`, `compile_if_return_output`, `with_return_unit_context`, `try_fold_effect_only_return_tail` |
| Self tail calls become a loop with parameter reassignment | `function_has_self_tailcall`, `try_compile_self_tailcall_block`, `compile_tail_loop_*`, `TailLoopState` |
| Static catch: inline handler, fallthrough, or an `exit` variable and a dispatch `switch`; which labels share one dispatch | `compile_staticcatch_*`, `flatten_nested_caches`, `uses_fallthrough_staticcatch_return`, `emit_multi_staticcatch_prelude`, `compile_exit_dispatch`, `return_staticcatch_requires_explicit_jump` |
| Switch form: `switch` statement, `if` chain, grouping of equal cases, case order, `default`, where `break` is needed | `compile_switch_*`, `grouped_switch_cases`, `stable_group_switch_cases`, `return_case_needs_break`, `lam_compile_variant.rs` |
| Variant and untagged-variant tests (`typeof`, `Array.isArray`, tag reads) | `untagged_dispatch.rs`, `Sw::untagged_plan` |
| Each primitive's JS: operator, `\| 0`, helper call, division checks | `lam_compile_primitive.rs`, `js_exp_make.rs`, `int32_div_expr`, `runtime_call_expr` |
| Folding in JS smart constructors (constant conditions, `!`, string append, sequences) | `js_ir/build.rs` (`exp`, `stmt`), `js_exp_make.rs` |
| Call form: direct call or curried helper by arity; method calls; `new`; spread; externals | `compile_apply_call`, `apply_with_arity`, `compile_external_field_apply`, `lam_compile_external.rs`, `lam_compile_arguments.rs` |
| Reading a field of another module: inlined constant or `M.x` | `resolve_cmj_module_field_*` |
| Loops, labels (`loop_N`, numbered per top-level group), labelled `break` inside a `switch` | `compile_for_loop`, `compile_for_of`, `ensure_current_loop_label`, `switch_depth` |
| `let rec` of non-functions: dummy objects updated in place | `compile_recursive_binding`, `recursive_dummy_object_expr` |
| Record spread as object spread | `try_compile_record_spread` |
| Exceptions: `try`, `throw`, wrapped exception objects | `try_statement`, `compile_try_finally` |
| Exports: which local is exported under which name, reuse of an existing binding, rebinding, undeclared exports after a top-level `throw`, name reservations | `extract_toplevel_exports`, `coerce_toplevel_exports_with_name_reservations`, `resolve_export_aliases`, `lam_coercion.rs` |
| Module purity and its reason text | `module_side_effect_reason`, `required_module_side_effect_reason` |
| Comments attached to expressions: `@__PURE__` on exception creation, constructor names on integer constants | `lam_compile_external.rs`, `lam_compile_const.rs`, `pointer_info_comment_text` |

Order dependence: temporaries and `exit` identifiers are created in traversal
order; loop labels are numbered in traversal order within a top-level group.

### A.6 JS passes

Run in this order in `compile_deps_program_in_arena`, each over the whole
program.

| # | Pass (function, file) | Reads | Writes | Output-visible decisions |
| ---: | --- | --- | --- | --- |
| 1 | `apply_js_flatten_pass` (`js_pass_flatten_and_mark_dead.rs`, `flatten_block`) | block | block | nested blocks are flattened and sequence expressions in statement position become statements (`flatten_sequence_statements`) |
| 2 | `apply_external_shadow_pass` (`js_pass_external_shadow.rs`) | all names | renamed identifiers | a local that shadows a JS global the program refers to is renamed |
| 3 | `apply_js_tailcall_inline_pass` (`js_pass_tailcall_inline.rs`) | block, declaration statistics | block, `ident_info.used_stats` | a pure function binding used once, at the final `return f(...)` of a block, is inlined there, with parameters renamed to variable arguments or replaced by cheap constants; declarations get used or dead statistics |
| 4 | `apply_js_record_rest_pass` (`js_pass_record_rest.rs`) | block | block, fresh ids | `RecordRest` becomes a destructuring declaration; skipped when the program has none |
| 5 | `apply_js_flatten_and_mark_dead_pass` (`Substitute`, `mark_dead_code`) | block | block, fresh ids, `used_stats` | a field read of a local bound to a known block becomes the field's value (materialised into fresh locals where needed); declarations are marked `DeadPure`, `DeadNonPure`, `OncePure`, `Used`, `Exported` |
| 6 | `apply_js_shake_pass` (`js_shake.rs`, `shake_program`) | block, exports | block | unused top-level bindings are removed transitively; same-name export aliases move to the end |

Then `collect_modules_from_js_block` and `populate_required_modules` compute
the import list (A.8).

Order dependence: pass 3 needs the flattened blocks of pass 1; pass 5 reads
the statistics pass 3 wrote and the declarations pass 4 created; pass 6 needs
the dead marks of pass 5. Passes 2 and 4 commute with their neighbours except
through fresh identifier creation.

### A.7 The printer and its naming logic

`js_ir/printer.rs` (`JsPrinter`) and `js_ir/program_printer.rs` are the port
of `js_dump.ml`, `js_dump_program.ml` and `Ext_pp_scope`. One walk. Besides
layout, the printer makes decisions that change the program text in ways a
reformat does not absorb. They are listed here because stage S1 must move
every one of them out of the printer.

Naming (`NameScope`, `add_ident`, `ident_name`, `module_ident_name`,
`with_reserved_ident_scope`, `function_reserved_idents`,
`reserve_idents_in_current_scope`, `reserve_js_names`, `fresh_scoped_name`):

- An identifier's printed name is chosen the first time it is printed in a
  scope. Its base is `convert_ident_atom(name)` (keyword and operator
  mangling). The first identifier with a base gets the base, later ones
  `base$1`, `base$2`, ..., skipping names already used in the scope and, for
  suffixed names, raw JS names the program refers to (`reserve_js_names`).
- Identifiers with stamp 0 print their name unchanged.
- Entering a function: the function's free variables plus its own binding,
  **sorted by `Ident`'s ordering (stamp, then name)**, are first named in the
  enclosing scope if they have no name yet
  (`reserve_idents_in_current_scope`), then a new scope is opened that knows
  only those names. A local of the function may therefore reuse a name of an
  outer variable the function does not capture.
- At the top: imports are named in import order, then
  `Program::name_reservations` (set by export coercion), then statements in
  order, then exports.
- Free variables are computed on demand by `FreeVarScratch`, memoised per
  function.

So names depend on (a) print order, (b) per-function free-variable sets, and
(c) the relative stamp order of same-named identifiers that are named for the
first time by one reservation. Point (c) is the only place where stamp
*order* reaches the output; section E.3 deals with it.

Other printer decisions (each a function in `printer.rs`):

| Decision | Function |
| --- | --- |
| A dead pure declaration is not printed; a dead impure one prints its value as a statement | `statement_desc_prints_anything`, `print_variable_declaration`, `print_expression_statement_with_mark` |
| `let x = undefined` prints `let x` | `print_variable_declaration` |
| `function (a, b) { return g(a, b) }` prints `g` | `eta_reduce_function_body` |
| Arrow or `function`; expression body or block; `{}` for a body that returns undefined; function declaration or `let` | `print_function_expression`, `print_function_declaration`, `single_arrow_function_expr` |
| A unit function drops its final `return`, and an `else` that only returns undefined | `print_function_body`, `print_function_tail_statement`, `else_block_is_omitted_like_ocaml` |
| `else { if ... }` prints `else if` | `single_else_if_stmt_like_ocaml` |
| A call whose only argument is the unit value prints `f()` | `print_expression_desc` (call case) |
| `x === null \|\| x === undefined` prints `x == null` | `nullish_or_target` (compares the two operands' printed text) |
| `0 - x` prints `-x` | `print_expression_desc` (binary case) |
| Runtime shape of blocks: records as objects or arrays, variants with `TAG`, lists as `hd`/`tl`, optional fields omitted when undefined, exceptions, debug-mode names | `print_caml_block`, `try_print_exception_block`, `print_exception_block_literal` |
| JSX syntax or a call of the JSX runtime | `print_jsx`, `print_jsx_call`, `jsx_printable` |
| Property access with `.` or `["..."]`; property names quoted or not; exotic uppercase names unwrapped | `property_access_uses_dot`, `print_property_name`, `unwrap_uppercase_exotic` |
| Number spelling: integer, float normalisation, hex floats, negative numbers, character comments | `print_number`, `transform_float_literal`, `format_char_comment` |
| String escaping; strings are stored as bytes and decoded on print | `print_string`, `decode_internal_utf8_string` |
| `for` loop upper bound bound to `i_finish` when not simple | `for_range_finish_needs_binding` |
| Method functions lose their first parameter to `this` | `method_params_and_binding` |
| Raw JS printed verbatim, parenthesised when it is a function or object; comment-only raw statements kept | `print_raw_js`, `raw_js_expression_needs_paren`, `classify_raw_js_expression_statement` |
| Parentheses by precedence, and deliberately none for right-nested `&&`, `\|\|`, `\|` chains | `op_precedence`, `print_expression_desc` |
| File: directives, header comment, `'use strict'` for CommonJS, leading comment statements, imports, exports, purity trailer, empty-output comment | `print_deps_program_with_directives_and_options`, `print_module_imports`, `print_esmodule_exports`, `print_commonjs_exports` |

Source maps: `mark_source_loc` records a mapping at each statement, variable
initialiser, switch case and expression that carries a location
(`js_ir/source_map.rs`, `SourceMapBuilder`). Locations are `LamLoc` handles
resolved through a `LamLocTable`; a mapping may point into another source
file. Modes are linked, inline and hidden, with optional `sourcesContent` and
a source root.

### A.8 Cross-module information

A dependent module reads, through `ModulePathResolver` and the caches in
`compile_deps_program_in_arena` (`cached_cmj_table`):

| Datum | Type | Produced by | Read by |
| --- | --- | --- | --- |
| Arity of each export | `CmjExportArity` (`Single(Arity)` or `Submodule(Vec<Arity>)`) | `lam_compile_main::cmj_export_arities` from `LamStats` after simplification | `get_arity_with_external_arity` in passes 2, 4, 7, 10, 11, 13; `apply_with_arity` in `lam_compile.rs` |
| Constant exports | `CmjExportConstant` (`true`, `false`, `null`, `undefined`) | `collect_cmj_export_constants_from_simplified_lambda` | `resolve_cmj_module_field_*` when compiling a field read |
| Closed lambdas of exports (only with cross-module inlining, off by default) | `CmjExportLambdas`: a map from name to a boxed `Lambda` tree plus a location table | `collect_cmj_export_lambdas_from_simplified_lambda` (`safe_to_inline`, closed, `@inline` or functor or small) | `simplify_alias` through `ExternalInlineResolver`, imported with `LamArena::import` |
| Purity | `is_pure` | `module_side_effect_reason` and the purity of imports | `required_module_side_effect_reason`, which decides whether an otherwise unused import is kept |
| Package and output path | `CmjModuleMetadata` | driver | import paths |

Import list and order: the modules referenced by the final JS IR
(`collect_modules_from_js_block`), dynamic imports with effects, and
"possible required modules" with effects (`populate_required_modules`) are
inserted into `OcamlModuleSet`, an emulation of OCaml's hash table keyed by
module identity (`ocaml_module_hash`), read out in bucket order and sorted
with OCaml's heap sort (`ocaml_sort_modules`) on name length, name bytes and
kind (`module_sort_cmp`). The sort key is total for distinct modules except
for modules that differ only in fields outside the key, so the emulated
bucket order matters only for such ties.

### A.9 Output-visible decisions, by where they must go

| Decision | Made today by | Level in the new design |
| --- | --- | --- |
| Expression shapes, evaluation order, block shapes | `RawLambdaConverter` | conversion to L |
| Match tests, their order, action sharing, exits | `matching.rs`, `switch.rs` | match compiler writing L |
| Constant and primitive lowering | `lower.rs`, `LamArena` smart constructors | normalising rules, L |
| Let regrouping and let kinds | `deep_flatten`, `refine_let` | pass rules, rounds 1, 3, 4 |
| Exit inlining | `simplify_exits` | pass rules, rounds 1, 5, 7 |
| Field folding, boolean folding, inlining, beta reduction | `simplify_alias`, `lam_beta_reduce` | pass rules, rounds 2, 3, 5 |
| Uncurrying by arity | `alpha_conversion` | pass rule, round 4 |
| Binding removal and substitution, string folding | `simplify_lets` | pass rules, round 6 |
| Scalar replacement | `lam_pass_sroa` | pass rule, round 6 |
| Guard raises, export rebinding, flat aliases | `guard_raises`, `handle_exports`, `add_flat_make_aliases` | round 7 |
| Statement structure, tail loops, catch dispatch, switch form, primitive JS, call form | `lam_compile*.rs` | lowering L to J |
| JS folding | `js_ir/build.rs`, `js_exp_make.rs` | normalising rules, J |
| Flatten, tail-call inline, record rest, block-field substitution, dead marks, shake | JS passes | pass rules, J |
| Global shadow renaming, identifier names and numbers | `js_pass_external_shadow`, `JsPrinter` naming | naming step |
| Printer decisions of A.7 | `JsPrinter` | emit step (oxc AST construction) |
| Import list and order, export list, purity trailer, header, directives | `compile_deps_program_in_arena`, `program_printer.rs` | emit step, program level |
| Layout: line breaks, indentation, spaces, quotes, redundant parentheses, numeric spelling | `JsPrinter` | given up to `oxc_codegen` |

## B. The IR

### B.1 Principles

- Module `compiler-rust/src/bir/`. One `Bir` value per compilation unit, owned
  by the worker that compiles it, dropped whole.
- Typed `Vec` pools with `u32` handles, a small tag per node, cold payloads in
  side tables, no `Box` trees, no allocator of our own. This is the layout of
  `LamArena` and `JsArena` today; what changes is the editing model.
- **Mutable in place, tree-shaped.** Every node has exactly one parent. A
  rewrite overwrites a node or replaces a child handle; it does not rebuild
  the spine. Sharing a subtree means copying it (`Bir::copy_subtree`), which
  is what beta reduction and exit inlining already do in effect, since both
  rename binders in the copy.
- **Facts are maintained, not recollected.** Use counts, purity bits and
  "bound to" facts are updated by the editing functions. No pass recomputes
  them by walking.
- Two levels of operations in one node type (section 0.2, point 2). A node's
  opcode says which level it belongs to. Lowering replaces L nodes by J nodes
  in place where the mapping is one to one and builds new J nodes otherwise.

### B.2 Handles and pools

```rust
pub struct NodeId(u32);    // nodes
pub struct ListId(u32);    // start of a span in `lists`; length precedes it
pub struct VarId(u32);     // vars
pub struct ConstId(u32);   // constants (interned)
pub struct PrimId(u32);    // interned (Primitive, LocId) payloads
pub struct FuncId(u32);    // function headers
pub struct SwitchId(u32);  // switch headers: keys, fullness, dispatch
pub struct ColdId(u32);    // source location and comment, most nodes have none
pub struct StrId(u32);     // text buffer (property names, labels, raw JS)

pub struct Bir {
    nodes: Vec<Node>,            // 16 bytes each
    cold: Vec<ColdId>,           // parallel to nodes only when source maps are on
    lists: Vec<NodeId>,          // length-prefixed child lists
    vars: VarTable,              // struct of arrays, B.4
    consts: Vec<Constant>,
    prims: Vec<PrimPayload>,
    funcs: Vec<FuncHeader>,
    switches: Vec<SwitchHeader>,
    text: String,
    exports: Vec<(VarId, Name)>, // in export order
    imports: ImportTable,        // modules referenced, B.8
    free_nodes: Vec<NodeId>,     // slots of deleted nodes, reused
}
```

Capacity is reserved from the typed tree's expression count, as
`RawArena::for_typed_exprs` does today.

### B.3 Nodes

```rust
#[repr(C)]
pub struct Node {
    op: Op,          // u8
    flags: NodeFlags,// u8: PURE, NO_ALLOC, HAS_LOC, TAIL, VALUE_UNUSED, ...
    aux: u16,        // per-op: let kind, arity, operator, direction, label
    a: u32,          // per-op operands: NodeId, ListId, VarId, payload id
    b: u32,
    c: u32,
}
const _: () = assert!(std::mem::size_of::<Node>() == 16);
```

Accessors return a typed view (`enum View<'a>`) so that code matches on
variants; the packed form is private to `bir/node.rs`.

Level L opcodes (one per `lambda::arena::Node` variant, same operands):

| Op | a, b, c | aux |
| --- | --- | --- |
| `Var` | `VarId` | |
| `Global` | module index in `imports` | |
| `Const` | `ConstId` | |
| `Apply` | callee, args `ListId`, apply-info index | status (`InferFull`, ...) |
| `Fun` | body, `FuncId` | arity |
| `Let` | `VarId`, value, body | kind (`Strict`, `Alias`, `StrictOpt`, `Variable`), `DEAD` bit |
| `LetRec` | first `VarId` of a run, values `ListId`, body | count |
| `Prim` | args `ListId`, `PrimId` | |
| `Switch` | scrutinee, actions `ListId`, `SwitchId` | |
| `StrSwitch` | scrutinee, actions `ListId`, keys | |
| `Exit` | label, args `ListId` | |
| `Catch` | body, handler, catch header (label, params) | |
| `Try` | body, exception `VarId`, handler | |
| `TryFinally` | body, finaliser | |
| `If` | condition, then, else | |
| `Seq` | first, second | |
| `While` | condition, body | |
| `For` | `VarId`, list of start, end, body | direction |
| `ForOf`, `ForAwaitOf` | `VarId`, iterated, body | |
| `Assign` | `VarId`, value | |
| `Break`, `Continue` | | |

Level J opcodes (the content of `js_ir::arena::ExprKind` and `StmtKind`):

| Kind | Ops |
| --- | --- |
| Expressions | `JBin` (operator in `aux`), `JNot`, `JBnot`, `JTypeof`, `JIn`, `JCond`, `JSeq`, `JCall`, `JNew`, `JIndex`, `JDot` (property `StrId`), `JLength`, `JIsNullish`, `JStrAppend`, `JFun`, `JObject`, `JArray`, `JBlockLit` (the runtime shape is fixed here, see E.2), `JOptional`, `JJsx`, `JTemplate`, `JTagged`, `JRaw`, `JAwait`, `JSpread`, `JQualified` (module member), `JNumber`, `JStr`, `JBool`, `JNull`, `JUndefined`; `Var` and `Const` are shared with level L |
| Statements | `SBlock`, `SDecl` (`VarId`, optional value), `SExp`, `SIf`, `SWhile` (label), `SForRange`, `SForOf`, `SForAwaitOf`, `SSwitch`, `SReturn`, `SThrow`, `STry`, `SBreak` (label), `SContinue` (label), `SDebugger`, `SRest` (record rest destructuring) |

What lowering needs is carried as follows:

- **Statement or expression position.** At level L every node is an
  expression. Lowering is called with a continuation, as OCaml's
  `Lam_compile` is: `Effect`, `Declare(kind, var)`, `Assign(var)`,
  `NeedValue`, and a tail flag with the enclosing tail-loop state. It returns
  what `Compiled` and `BlockOutput` carry today: a statement list, an
  optional value node and the `finished` flag. These are values on the stack
  of the lowering, not stored in nodes. A J statement list is a `ListId`.
- **Return and tail context.** The `TAIL` flag is set on L nodes in tail
  position of a function when the function body is built (cheap: it follows
  `Let` body, `If` branches, `Switch` actions, `Catch` body and handler,
  `Seq` second). `function_has_self_tailcall` becomes a flag on `FuncHeader`
  set when a `TAIL` `Apply` of the function's own variable is created or
  rewritten.
- **Declared names.** Every binder is a `VarId`; `SDecl` refers to it. Name
  and number are assigned in the naming step (E.3) and stored in
  `VarTable::printed`.
- **Mutable variables.** `VarFlags::ASSIGNED` is set when an `Assign` to the
  variable is created; it replaces `arena_assigned_variables` (three walks
  today).
- **Loops.** `While`, `For`, `ForOf` keep their L form through level L;
  labels are assigned by lowering (`loop_N`, counter reset per top-level
  group, as `with_fresh_loop_label_counter` does).
- **Exceptions.** `Try`, `TryFinally`; raising is `Prim(Praise)`.
- **Switches and decision trees.** `Switch` with a `SwitchHeader` (constant
  and block keys, fullness, optional default, dispatch kind for untagged
  variants), `StrSwitch`, `If`, `Catch` and `Exit`. A shared action is a
  `Catch` handler reached by `Exit`s, as today.
- **Primitive calls.** `Prim` with an interned `(Primitive, LocId)` payload.
  `Primitive` stays the enum of `lambda/lam_primitive.rs`.
- **Closures.** `Fun` with a `FuncHeader { params: run of VarId, attr,
  loc, flags }`. Free variables are not stored; naming computes them once
  (E.3).

`size_of::<Node>() == 16` and the sizes of the headers are asserted in tests.

### B.4 Variables, use counts and facts

```rust
pub struct VarTable {
    name: Vec<Name>,        // interned atom
    order: Vec<u32>,        // creation order; replaces the stamp (E.3)
    flags: Vec<VarFlags>,   // u8: ASSIGNED, CAPTURED, EXPORTED, PARAM, JS_GLOBAL, MODULE
    uses: Vec<u32>,         // weighted count of Var nodes
    binder: Vec<NodeId>,    // the Let/LetRec/Fun/Catch/For/Try/SDecl that binds it
    fact: Vec<Fact>,        // 8 bytes
    printed: Vec<Name>,     // filled by naming
}

pub enum Fact {             // today's lam_stats::IdKind
    Unknown,
    Param,
    Const(ConstId),
    Block(NodeId),          // immutable block; fields read through the node
    MutableBlock(NodeId),
    Function { node: NodeId, rec: RecFlag },  // arity is read from the node
    Optional(NodeId),       // Some(x), x is the node
    NullableOptional(NodeId, BoxedNullable),
    Module(u32),
    Alias(VarId),
}
```

Invariants, checked by `Bir::validate` in debug builds and in the harness:

1. Tree: every live node is the child of exactly one live node or is the
   root.
2. `uses[v]` equals the sum over live `Var(v)` nodes of the node's weight.
   The weight is 1, except under a `Switch` default that today's counts
   visit twice (default present and neither case table full), where it is 2.
   This reproduces `lam_pass_lets_dce::count` and `lam_pass_exits::count`.
3. `CAPTURED` is set if some `Var(v)` lies under a `Fun`, a `For` body or a
   `While` that does not contain `v`'s binder (`UsedInfo::captured`).
4. `PURE` on a node implies `lam_analysis::no_side_effects` of it.
5. A `Let` with the `DEAD` bit has `uses == 0` and a pure value; every
   reader treats it as its body.

How they are maintained. All edits go through the functions of
`bir/edit.rs`; node fields are not otherwise writable. As built (S2.1, S4.1)
the constructors run no rules (`Engine::build` does, C.6), `replace` has a
variant `replace_local` for rewrites that move no use under a function or
loop, `detach` and `new_node_in` let a rewrite build a new node around
attached children without recounting them, and marking bindings dead is
deferred while an engine exists (C.2 row 5). The original description:

- `new_*` constructors: count the `Var` nodes they receive (a new `Var` node
  increments `uses`), compute `PURE` and `NO_ALLOC` from the children's flags
  and the opcode, then run the normalising rules for the opcode.
- `replace(node, with)`: overwrite `node`'s slot with `with`'s content and
  free `with`'s slot. Children of the old content that are not in the new
  content are released.
- `release(subtree)`: walk the subtree, decrement `uses` for each `Var`, free
  the slots. If a count reaches zero and the binder is a `Let` whose value is
  pure, set `DEAD` on the binder and release its value (which may cascade).
  This is a worklist, not recursion.
- `copy_subtree(node, renaming)`: copy with fresh `VarId`s for binders inside
  the copy (`rewrite_bounded_vars` today), incrementing counts for free
  variables.

`CAPTURED` is set when a `Var` is created under a function or loop (the
builder knows its depth) and when a subtree is moved under one; it is never
cleared, which is conservative in the same direction as today's count.

Rules that need a count as today's snapshot had it are discussed in C.2.

Queries that walk today and do not in `Bir`:

| Today | In `Bir` |
| --- | --- |
| `no_side_effects(lam)` | `PURE` flag |
| `collect_info` (five walks) | `fact`, set when a binder is created or its value replaced |
| `arena_assigned_variables` (three walks) | `ASSIGNED` flag |
| `collect_occurs` | `uses`, `CAPTURED` |
| `count_helper` for exits | a count per catch header, maintained like `uses` |
| `hit_variable(v, lam)` | `uses[v] == 0` answers "no" at once; otherwise the walk remains |
| `free_variables_with_stats`, `size_upto` | remain bounded walks of the candidate body |

### B.5 Size

Measured today: `lambda::arena::Node` is 16 bytes, `js_ir::arena::ExprNode`
and `StmtNode` are 20. `Bir::Node` is 16 with flags included; locations and
comments move to a parallel array allocated only when a source map is
requested. Peak memory is expected to fall (estimated), because there is one
arena instead of three and rewrites do not append.

## C. The rewrite engine

### C.1 Two classes of rules

**Normalising rules** are today's smart constructors: `LamArena::prim`,
`if_`, `seq`, `switch_with`/`decide_switch`, `string_switch_with`, `apply`
(C.5 is the inventory; `let_` has no rule); at level J the constructors of
`js_ir/build.rs` and `js_exp_make.rs`. A normalising rule looks at one node
and a bounded number of levels below it (up to four, C.5). It runs when the
node is built through `Engine::build`, and during a round when the sweep
returns to an ancestor of a rewrite.

Amended in S4.1. The first version of this section said "re-normalise the
parent when a child changes, and continue upward while something changes".
That is not what today's passes do, in two ways. A pass rebuilds the whole
spine above a change, so a constructor two or more levels up runs even when
the nodes between did not change, and it can match because its pattern is
deeper than one level (an application whose callee's body became a
primitive on its parameters). And `shallow_map` rebuilds only applications,
primitives and the two switches through their smart constructor;
conditionals and sequences are rebuilt plainly unless the pass calls `if_`
or `seq` itself. So the engine re-normalises, on the way back up its sweep,
every ancestor of a rewrite whose opcode is in the round's `renorm` mask
(`OpMask::SHALLOW_MAP` for a pass built on `shallow_map`), whether or not
the nodes between changed. The arena stores parent links (S2.1), but the
sweep does not need them for this.

`fold_constants`, `collapse_module_alias` and `make_apply` in
`raw_lambda/lower.rs` are lowering's own code, not constructors: they move
into the `Bir` builder in S5.2. `make_apply` is a copy of `LamArena::apply`;
the S4.1 comparison replays it as rows N13 and N14.

**Pass rules** are the case arms of today's passes. A pass rule may read
facts, use counts and a bounded part of the tree, and may create
identifiers. Pass rules are grouped into **rounds**; a round is one sweep of
the tree in a fixed traversal order, during which each candidate node is
offered to the round's rules once.

```rust
pub struct Round {                // bir/engine.rs, as built in S4.1
    name: &'static str,
    mask: OpMask,                 // opcode classes that can match the rule
    order: Order,                 // Pre or Post
    renorm: OpMask,               // classes re-normalised above a rewrite
    facts: Facts,                 // Current, or Frozen at the round's start
    guard: Option<fn(&Engine, NodeId) -> bool>,  // what to snapshot (C.2 row 1)
    rule: fn(&mut Engine, NodeId) -> Changed,
}
```

Worklist discipline:

1. A round sweeps from the root. For each node it descends into a child only
   if the child's subtree summary intersects the round's mask. As built, the
   summary is a 16-bit set of opcode classes per node (a side array of the
   engine, two bytes a node), set when the engine creates a node and
   recomputed for the nodes on the way back up a sweep; one walk recomputes
   all of them when an edit was made outside a sweep. A summary is always a
   superset: a stale one costs a visit, never a missed rewrite.
2. A rule that changes a node returns `Changed`; the engine re-normalises
   the ancestors in the round's `renorm` mask on the way up.
3. As built, the engine's worklist holds nodes waiting for their normalising
   rule, nothing else (C.6). A use count reaching zero is not an event: no
   normalising rule reads a count, and marking a binding `DEAD` is deferred
   to the round that ports `simplify_lets` (C.2 row 5), where
   `Engine::resume_deaths` marks every unused pure binding in one scan of
   the variable table and the arena keeps doing so as edits remove last
   uses. Removing a `DEAD` `Let` from its parent happens when a sweep next
   passes it.
4. A rule that inlines a body sweeps the inlined copy with the same round
   before returning, as `simpl(reduced)` does today, with the same depth
   limit.
5. Rounds run in the fixed order of table C.3. A round whose mask does not
   intersect the root summary is skipped (most modules have no static catch
   after round 1, no `Assign`, no JSX).

The engine is deliberately not a rewrite-to-fixpoint system. A fixpoint
system would do more than today's pipeline (for example inline deeper than
three sweeps of depth 4 allow), and "more" is a different program.

### C.2 Where output depends on order

For each dependence found in section A: reproduce the order (R), prove
independence (P), or stage it (S: start with R, replace by a measured proof
later).

| # | Dependence | Answer |
| ---: | --- | --- |
| 1 | `simplify_alias` reads `ident_tbl` as of the preceding `collect_info`. In particular the body it inlines for `f` is `f`'s body before the current sweep rewrote it, and the size tests of `ok_to_inline_fun_when_app` see that body. | R. A round that inlines takes a snapshot of each inlinable function's body the first time the sweep is about to rewrite inside it (copy on first write, into a per-round side map `FuncId -> NodeId`). Only functions that pass `lfunction_can_be_inlined` and a size bound are copied, so the cost is bounded by the inline size limit per function. As built (S4.1, C.6): the round names what to protect with `Round::guard`; the engine copies a guarded node before the first edit at or below it and `Engine::as_of_round_start` returns the copy. The map is keyed by node, not by function, because the same holds for every fact that names a node (a block's fields, the content of `Some`): `simplify_alias` reads them as collected before the sweep too. A snapshot is an ordinary detached copy (`copy_subtree`), so until the round ends its variable uses are counted; a round that takes snapshots must not decide on a use count (today's inlining does not: it reads `free_variables_with_stats` of the body). |
| 2 | Three `simplify_alias` sweeps with `collect_info` between them; each sweep nests inlining at most four deep. | R. Three rounds (2, 3, 5 in C.3). Facts are current at the start of each round by construction. |
| 3 | `collect_info` records facts only for bindings it visits; a fact from an earlier sweep stays in `ident_tbl` after its binding was rewritten or removed (OCaml's table is never cleared between sweeps). | S. `Fact` is updated when a binder's value is replaced, which can differ from a stale entry. Start by keeping the stale behaviour where the harness shows a difference (the fact table gets a per-round "frozen" bit for such binders); expected to be empty, since a stale fact describes a binding that no longer exists and can only be queried through a variable that no longer occurs. Unknown until the harness runs. As built (S4.1): a round with `Facts::Frozen` reads a copy of the fact column taken at its start (`Engine::fact`), which is what a `collect_info` before the pass gives; facts for bindings the round creates are added with `Engine::set_fact`. Facts that survive in `ident_tbl` from an earlier sweep after their binding changed kind are not reproduced; S4.4's diagnostic comparison is the judge. |
| 4 | `simplify_exits` runs at three fixed points and counts raises at the start of each. A handler that shrank, or lost a raise, between two runs is inlined by the later run. | R. Three rounds (1, 5, 7). The maintained count equals a fresh count at the start of a round (invariant 2 with weights). |
| 5 | `simplify_lets` decides on a count taken once, with its own rules (B.4, invariant 2 and 3; uses inside dead bindings do not count). | R for the position (one round, 6). P for the count: the maintained count after dead bindings were released equals `collect_occurs`'s, because `release` cascades exactly along `count`'s rule "the value is counted only if the binding is used or strict". The applied-function case (`no_names_beta_reduce` inside `count`) is handled by reducing those applications at the start of round 6, before any decision reads a count. The harness checks the equality directly: in checking builds `collect_occurs` is run on an exported copy and compared with `uses`. Amended in S4.1: marking a binding dead the moment its last use disappears is wrong before round 6. An unused pure binding still has its size (`size_upto` in the inlining tests), its place in a `let` spine (`deep_flatten`) and its node in the Lambda the diagnostic comparison prints after each round. So deaths are deferred while an engine exists (`Bir::defer_deaths`) and `Engine::resume_deaths` at the start of round 6 marks every unused pure binding, cascading, in one scan of the variable table. Open for S4.7: the arena's test is "unused and `PURE`" for every `let` kind, while `simplify_lets` drops an unused `Alias` or `StrictOpt` binding whatever its value and keeps an unused `Strict` one unless `no_side_effects`; `PURE` implies `no_side_effects` but is not equal to it. |
| 6 | `deep_flatten` runs three times, between the inlining sweeps. | R. Rounds 1, 3, 4 include its rules. |
| 7 | `alpha_conversion` runs once, after the second inlining sweep, with arities as known then. | R. Round 4. |
| 8 | `sroa` after `simplify_lets`, `guard_raises` last, `handle_exports` after everything. | R. Rounds 6 and 7. |
| 9 | Fresh identifiers are numbered in the order passes create them, and the number orders same-named identifiers in the printer's reservation (A.7, point c). | S. See E.3: `order` is assigned at creation, and because rounds sweep in today's traversal order the creation order within a round is today's. A measurement in S1 decides whether the dependence can be replaced by a canonical order. |
| 10 | Level J: flatten, shadow renaming, tail-call inline, record rest, substitution and dead marks, shake, in that order. | R for tail-call inline before block-field substitution before dead marks before shake. P for flatten: it is a normalising rule (statement lists are built flat). P for dead marks: `uses == 0` and `PURE` are maintained, and `mark_dead_code` is their fixpoint. Shadow renaming moves to naming. |
| 11 | Lowering creates temporaries, `exit` variables and loop labels in traversal order. | R. Lowering is one recursive walk in today's order. |
| 12 | Match compilation numbers exits in creation order; negative labels are not inlined. | R. The algorithm is unchanged (section D). |
| 13 | Printer: names are chosen in print order. | R. The naming step walks in print order (E.3). |
| 14 | Import order: emulated OCaml hash table order, then heap sort. | R. `OcamlModuleSet` and `ocaml_sort_modules` are kept as they are and move to the emit step. |

### C.3 Rounds

Level L rounds replace `simplify_in_arena`. "Sweeps" compares with A.4.

| Round | Rules (today's function) | Order | Skipped when |
| ---: | --- | --- | --- |
| 0 | alias collapse (`collapse`) | no sweep: when conversion builds `let[Alias] x = y`, later uses of `x` are built as `y`; the binding itself is built only if `x` is exported | |
| 1 | `deep_flatten`; then exits (`subst_helper`) | `aux`'s recursion; then pre-order | exits: no `Catch` |
| 2 | `simplify_alias` | `simpl`'s recursion | |
| 3 | `deep_flatten`, then `simplify_alias` | two sweeps | |
| 4 | `deep_flatten`, then `alpha_conversion` | two sweeps | flatten: no `Let` whose value is a `Let`, `Seq`, `LetRec` or named block |
| 5 | exits, then `simplify_alias` | two sweeps | exits: no `Catch` |
| 6 | `simplify_lets`, `sroa` | `simplif`'s recursion | sroa: no mutable block |
| 7 | exits, `guard_raises`, `handle_exports`, flat `make` aliases | pre-order; spine | |

That is at most 11 sweeps against about 25 walks, none of them rebuilds a
spine or refills a table, and several are skipped per module. Fusing the two
sweeps of rounds 3, 4 and 5 into one each is possible only where the second
pass's rule at a node does not read anything the first pass changes below it;
that is left for after S4, with the harness as judge.

Level J rounds replace the JS passes:

| Round | Rules | Notes |
| ---: | --- | --- |
| J1 | tail-call inline (`TailcallInlineState`) | reads `uses`, `PURE`; candidates are functions called by a final `return f(...)`, collected during lowering |
| J2 | record rest (`RecordRest`) | skipped unless lowering created an `SRest` candidate |
| J3 | block-field substitution (`Substitute`) | candidates are `SDecl`s bound to a block literal, collected during lowering |
| J4 | shake (`shake_program`) | `uses == 0` on top-level `SDecl`, cascade through `release`; export aliases moved |

### C.4 Mapping of each optimisation

| Today | Rule in `Bir` | Class |
| --- | --- | --- |
| `LamArena::prim` folding (`fold_prim`, `fold_makeblock_module_alias`) | rows N1 to N3 of C.5 | normalising, L |
| `fold_constants`, `collapse_module_alias`, `make_apply` in `raw_lambda/lower.rs` | lowering's own code; into the `Bir` builder in S5.2 | |
| `LamArena::if_`, `seq`, `switch_with`, `string_switch_with`, `apply` | rows N4 to N14 of C.5 (`bir/l/norm.rs`) | normalising, L |
| `LamArena::let_` | none: it builds the node as given | |
| `refine_let` | `refine_let` called by flatten and lets rules | pass rule (it is called explicitly today) |
| `deep_flatten` (`flatten`, `eliminate_tuple`) | `flatten_let` | pass, rounds 1, 3, 4 |
| `simplify_exits` | `inline_exit`, `drop_catch` | pass, rounds 1, 5, 7 |
| `simplify_alias` field, option, boolean cases | `fold_field`, `fold_is_some`, `fold_if_var`, `fold_str_switch`, `unwrap_some` | pass, rounds 2, 3, 5 |
| `simplify_alias` inlining, `lam_beta_reduce` | `inline_call`, `inline_external`, `beta` | pass, rounds 2, 3, 5 |
| `alpha_conversion`, `transform_under_supply` | `uncurry_apply` | pass, round 4 |
| `simplify_lets` | `drop_let`, `subst_alias`, `reduce_applied_fun`, `fold_string_add` | pass, round 6 |
| `lam_pass_sroa` | `scalarise_block` | pass, round 6 |
| `guard_raises` | `guard_raise` | pass, round 7 |
| `handle_exports`, `add_flat_make_aliases` | `bind_exports`, `flat_make_aliases` | round 7, spine only |
| `js_ir/build.rs`, `js_exp_make.rs` constructors | `jnorm_*` | normalising, J |
| `flatten_block` | flat statement lists by construction | normalising, J |
| `apply_js_tailcall_inline_pass` | `inline_return_call` | pass, J1 |
| `apply_js_record_rest_pass` | `materialise_rest` | pass, J2 |
| `Substitute` | `subst_block_field` | pass, J3 |
| `mark_dead_code` | invariant 5 and `uses` | maintained |
| `shake_program` | `shake` | pass, J4 |
| `apply_external_shadow_pass` | naming step | E.3 |

Each rule is a port of the cited function with the same tests in the same
order. The port changes how the result is written (in place) and where facts
come from (the tables), nothing else. A reviewer checks a rule against the
function it cites.

### C.5 The L-level normalising rules (S4.1)

The inventory of every rewrite `LamArena`'s constructors perform when a node
is built, in `compiler-rust/src/lambda/arena.rs`. This table is the
specification of `bir/l/norm.rs`; each rule there cites its row.

| Row | Constructor (function) | Trigger shape | Result | Fires again on its result? |
| --- | --- | --- | --- | --- |
| N1 | `prim`, `prim_with` (`fold_prim`) | one constant argument: `Pnegint` on an integer, `Pintoffloat` on a float, `Pstringlength` on a string, `Pnot` on a boolean | the constant | no: a constant has no rule |
| N2 | `prim`, `prim_with` (`fold_prim`) | two constant arguments: integer comparison and arithmetic (not division or modulo by zero), float comparison, `==`/`!=` on pointers, `&&`/`||` on booleans, string concatenation, string index | the constant | no |
| N3 | `prim` (`fold_makeblock_module_alias`) | `Pmakeblock(Module fields)` whose arguments are, in order, field `i` named `fields[i]` of one variable or module | that variable or module | no |
| N4 | `if_` | constant condition (`eval_as_bool`) | the branch taken | no: the branch was normalised when built |
| N5 | `if_` (`is_assertfalse`) | the else branch, or else the then branch, is `assert false` | `seq(condition, other branch)` | as a sequence: N8, N9 |
| N6 | `if_` (`has_boolean_type`) | `if c then true else false`, `c` a boolean-valued primitive | `c` | no |
| N7 | `if_` (`lambda_not`) | `if c then false else true`, `c` a boolean-valued primitive | `a == b` when `c` is `a != b` (built plainly); otherwise `Pnot(c)` | no: `Pnot` folds constants only |
| N8 | `seq` | first is `Pmakeblock` with at least one argument | `seq(...seq(seq(a0, a1), a2)..., second)` | only the innermost, `seq(a0, a1)` (or `seq(a0, second)` for one argument): N8, N9 on `a0`. A sequence built by `seq` is always a sequence node, so the outer ones cannot match |
| N9 | `seq` | first is `PnullToOpt` or `PnullUndefinedToOpt` with one argument | `seq(argument, second)` | N8, N9 on the argument |
| N10 | `switch_with` (`decide_switch`) | constant scrutinee: a constructor, an integer or a block | the action of the matching key, else the default; no rewrite when neither exists | no |
| N11 | `switch_with` (`decide_switch`, `untagged_plan_with`) | constant scrutinee, dispatch on an untagged variant with payload types | the action the generated dispatch reaches for the constant's JavaScript value | no |
| N12 | `string_switch_with` | constant string scrutinee | the action of the equal key, else the default | no |
| N13 | `apply`, `apply_with` (`eta_reduce_function_apply`, `eta_conversion_args`, `evaluates_args_as_call`) | callee is a function that may be inlined (`lfunction_can_be_inlined`: not async, no directive) whose body is `p(params)`, `w(p(params))` for a null check, null conversion or `typeof` `w`, or `p(params); constant`; the parameters in order; as many arguments; for `&&`/`||` every argument after the first a constant or variable | `p(args)`, `w(p(args))`, `p(args); constant` | each new primitive: N1 to N3; the sequence: N8, N9 |
| N14 | `apply`, `apply_with` | callee is `let x = v in f`, `f` a function | `let x = v in apply(f, args)` | the inner application: N13 |

No rule: `let_`, `let_with`, `letrec`, `function_`, `static_raise`,
`static_catch`, `try_`, `try_finally`, `while_`, `for_`, `for_of`,
`for_await_of`, `assign`, and every `*_raw` constructor. `switch` and
`string_switch` are `switch_with` and `string_switch_with` from owned keys.

Three things the port keeps exactly. `fold_prim` parses a float's spelling
with Rust's `str::parse::<f64>` and converts with `as i32`, not with the
OCaml-compatible parser the `Bir` constant pool caches; a spelling Rust does
not parse (hexadecimal, underscores) is not folded. N3 compares a variable
with a variable and a module with a module; `fold_makeblock_module_alias`
would also accept a variable and a module reference of one identifier, which
lowered Lambda does not contain. N11 is the one rule whose attempt is not
bounded by the pattern: the dispatch plan compares actions with `eq_approx`,
a structural walk that stops at the first difference and at any node outside
its ten shapes. It is attempted only on a constant scrutinee of an untagged
variant, and the engine counts the node pairs compared (`Stats::compared`;
zero on the three in-repository corpora).

Termination. Let Φ = 3·(conditionals + switches + string switches) +
2·(applications + functions) + primitives, counted in the subtree of the
node being normalised. N1 to N13 each lower Φ (N7 removes a conditional and
adds one primitive; N8 and N9 remove a primitive and add only sequences; N13
removes an application and a function and replaces the body's primitives by
as many). N14 leaves Φ and lowers the number of applications whose callee
is a `let`. Nothing raises either, so a normalisation stops after at most Φ
plus that number of rewrites: linear in the nodes it started from.

### C.6 The engine's contract and costs (S4.1)

`bir/engine.rs`. A step is one node read, one node allocation or one
worklist push; the tests named below count them.

**When a normalising rule sees a node.** (a) When the node is built through
`Engine::build`: the node is created plainly and then offered. (b) When a
rule pushes it: the node it rewrote, or a node it created, exactly where the
constructor would have called another constructor. (c) During a round, when
the sweep returns to an ancestor of a rewrite and the ancestor's opcode is
in the round's `renorm` mask. Never on a use-count change: no normalising
rule reads a count.

**The worklist** is a stack of nodes waiting for their rule. Rules never
call each other; a rule edits, pushes and returns, and the engine pops until
the stack is empty. That removes recursion (a block nested 10,000 deep in
first position is a loop) and fixes the order: entries pop in reverse push
order, pushes happen in rule code order, nothing iterates a hash table and
no other thread takes part, so the result is a function of the tree. A rule
pushes only the node it was given or nodes it created below it, parent
before child; an entry is therefore live when it is popped.

**A round** is one sweep with one rule (C.1), pre- or post-order, with an
explicit stack. A round whose mask misses the root's summary does nothing.

**Edits.** Rules edit through the engine: `promote(target, descendant)`,
`put(target, new node)`, `fill`, `detach`, `node`, and `replace` for a
rewrite that moves a use under a function or loop. A rule may edit the node
it was offered and what is below it, nothing else; summaries and snapshots
rely on that.

**A snapshot** (C.2 rows 1 and 3) lets a rule read a subtree as it was when
the round started. It costs one copy of the subtree, taken before the first
edit at or below a node the round's `guard` selected, and nothing for a
guarded node that is not edited. Snapshots are released when the round ends.

| Operation | Cost | Test |
| --- | --- | --- |
| `Engine::push` | 1 step | `pushing_is_one_step_and_an_attempt_on_a_leaf_is_one_read`: 10,000 pushes, 10,000 steps; draining them, 10,000 more |
| a rule attempt | the pattern of its row: the node and up to four levels below, plus the arguments for N3 and N8 and the keys for N10 to N12; N11 as said in C.5 | `an_attempt_reads_the_pattern_not_the_subtrees`: 8 steps on a conditional over two 40,000-node branches |
| `promote`, `put`, `fill` | the nodes removed; plus a recount of the kept content only when it changes use weight, that is when it enters or leaves a switch default that the counts visit twice (B.4, invariant 2) | `replacing_a_node_by_its_child_costs_the_removed_nodes`: 44 steps to replace a conditional by its 40,000-node branch; `an_edit_keeps_counts_in_a_doubled_default_without_a_walk`: 71 steps |
| a round | the nodes entered plus the rewrites | `a_round_is_linear_in_a_deep_chain_and_in_a_wide_node`: 70,003 nodes, 20,000 rewrites, 1,080,024 steps; `a_round_enters_only_subtrees_that_can_hold_a_candidate`: 1,002 of 12,001 nodes entered |
| a normalising pass over a unit (`normalise_tree`) | linear in the nodes plus the rewrites | `a_normalising_pass_is_linear_in_a_deep_chain` (10,000 nested sequences, conditionals, lets: 15 to 24 steps a node), `..._in_a_wide_node` (a 10,000-element block in a sequence, a 10,000-field module alias, 10,000 folds below one block: 12 to 27), `..._inside_a_doubled_switch_default` (26); each test asserts at most 32 |
| a snapshot | the size of the subtree, once a round, only if edited | `a_guarded_function_is_copied_before_the_first_edit_inside_it_only` |
| freezing facts | one copy of the fact column (a vector copy, no tree walk) | `a_frozen_round_reads_facts_as_they_were_at_its_start` |
| `resume_deaths` | one scan of the variable table, plus the bindings it releases | `an_unused_binding_stays_until_deaths_resume` |

No rule recomputes a whole-tree fact. Purity is the `PURE` flag; a rule
that needs free variables or a size walks the candidate body it is about to
copy, bounded by the limit that makes it a candidate (B.4, last table).

What S4.1 changed in the arena to make these costs hold (`bir/edit.rs`):
`replace` no longer recounts and rechecks content that keeps its weight,
and no longer rescans the parent's children when the replaced child's two
effect bits are unchanged; `detach` and `new_node_in` build a new node
around attached children, a detached root keeping the use weight of the
slot it came from; `replace`, `detach` and `release` work during bulk
construction, so a unit can be built through the rules and finished in one
pass.

### C.7 How to add a round (S4.2 to S4.8)

1. One file per pass in `bir/l/`, one function per case arm of the pass,
   citing it. The rule has the signature `fn(&mut Engine, NodeId) -> Changed`
   and edits only the node it is offered and below it.
2. Declare the round:

   ```rust
   pub static FLATTEN: Round = Round {
       name: "deep_flatten",
       mask: OpMask::LET.or(OpMask::LETREC).or(OpMask::SEQ),  // what the rule matches
       order: Order::Post,          // Pre when the pass decides before descending
       renorm: OpMask::NONE,        // SHALLOW_MAP if the pass rebuilds through shallow_map
       facts: Facts::Current,       // Frozen if it reads ident_tbl
       guard: None,                 // which nodes to snapshot (inlining rounds)
       rule: flatten_let,
   };
   ```

   `renorm` is decided by reading how the pass rebuilds a node whose child
   changed: `shallow_map` gives `SHALLOW_MAP`; a pass that also calls `if_`
   or `seq` on its own rebuilt nodes calls `engine.normalise(node)` in the
   rule for those; a pass that rebuilds with `*_raw` constructors gives
   `NONE`.
3. Where the pass calls a smart constructor on a node it builds, build the
   node with `engine.node` and `engine.push` it (or `engine.build` for a
   detached node); where it calls a `*_raw` constructor, do not push.
4. A pass with its own recursion order (`simpl`, `aux`) that neither `Pre`
   nor `Post` gives: use `Pre`, do in the rule what the pass does before it
   recurses, and what it does after in a second round; if the pass threads
   state down the recursion that a sweep cannot carry, say so in the stage's
   pull request and extend `Round` there. This is the one part of the round
   interface S4.1 could not test against a real pass.
5. Fresh identifiers: `Bir::new_var_id` in the order the pass creates them
   (C.2 row 9). A rule that copies a body uses `copy_subtree` and
   `engine.replace`, not `put`, because the copy may move uses under a
   function.
6. A round that reads `ident_tbl` uses `Facts::Frozen` and `engine.fact`. If
   it reads a node through a fact (a function body, a block's fields), give
   the round a `guard` selecting those nodes and read them through
   `engine.as_of_round_start`. A rule that replaces a binding's value from
   the binding (not from inside the value) calls `engine.preserve(value)`
   first.
7. Run the rounds from `bir/shadow.rs` in check mode after the import, in
   the order of C.3, and compare the export with the legacy pipeline cut at
   the same point (G.3): add a stage name, report through `report`, and add
   the stage to `STAGES` in `scripts/test_backend_coverage.py` and to
   `compiler-rust/tests/backend_coverage.txt` with `--record`. A shape the
   round does not handle yet returns `Unsupported(reason)`.
8. Give every rule a test in the form of `bir/l/norm.rs`'s: the same input
   to the legacy function and to the rule, dumps compared. Add a step-count
   test on a 10,000-deep chain and a 10,000-wide node for the round.
9. Deaths stay deferred until the round that ports `simplify_lets`, which
   starts with `engine.resume_deaths()`. Before that, an export never meets
   a released `let` value.

## D. Match compilation into the IR

### D.1 What stays and what changes

The algorithm of `matching.rs` and `switch.rs` stays: every choice it makes
is visible (A.2). Three things change.

1. **Output.** The builder calls that create raw Lambda (`make_catch`,
   `make_exit`, `bind`, the `combine_*` functions, `switch.rs`'s action
   construction) write `Bir` L nodes. Today the tree goes through
   `RawArena`, then `lower`, then `LamArena`; the constant and primitive
   lowering of `lower.rs` becomes part of the constructors (`norm_prim`,
   `lower_constant`), so a decision tree is written once.
2. **Action sharing.** `StoreExp` decides that two actions are the same by
   comparing strings built by `MakeKeyWriter` and `key_encode.rs`
   (`Lambda.make_key`). In `Bir` the key is a 64-bit structural hash of the
   normalised action computed bottom-up by the same normalisation
   (`make_key` renames bound variables to positions and drops locations),
   confirmed by a structural comparison on hash equality. The equivalence
   classes are the same by construction; the harness compares exit structure.
3. **Pattern storage.** Rows are slices of pattern indices into `PatArena`;
   specialisation writes new rows into a row pool instead of cloning
   `Pattern` values (`normalize_pat_owned`, `alloc_cow`, `with_desc` today).
   Contexts and jump summaries (`Ctx`, `Jumps`) keep their definitions but
   are built lazily: they are needed only to decide whether a failure branch
   can be reached below a split, and a match that the checker marked total
   with no guard and no or-pattern under a constructor never asks.

A fast path is allowed only where it provably produces the general
algorithm's tree: a single-column match on constructors or constants with no
guards, no or-patterns and variable or wildcard sub-patterns. It emits the
`Switch` directly.

Saving: match compilation is about 3.5% of the build (measured, half of
7.1%). How that divides between key strings, pattern copying and context
operations is unknown; S5 starts with a profile of `matching.rs` on the
application and the three changes are ordered by it. Estimated result: 1.2%.

### D.2 Sharing the decision tree with exhaustiveness checking

`types/parmatch.rs` decides exhaustiveness and unused clauses on the same
matrices before the typed tree exists, and the match compiler then repeats
the specialisation.

- Saving: unknown. The shares given for this design do not separate
  `parmatch` from the rest of type checking. An upper bound is the match
  compiler's own 3.5%, since both do one specialisation per constructor per
  column; the realistic saving is a fraction of that.
- Risk: high. (a) The warnings' text contains counter-example patterns
  built by `parmatch`'s own search, and diagnostic text is part of the
  correctness contract. (b) The match compiler takes the checker's `partial`
  flag as input, so sharing inverts a dependency: the tree would have to be
  built assuming partiality and pruned afterwards, and the pruned tree must
  equal today's. (c) `parmatch` works on patterns before the typed tree's
  final form and also runs for matches that are never compiled (type-level
  errors, unused code).

Recommendation: do not share. Revisit only if a profile after S5 shows
`parmatch` above 1% of the build, and then by caching specialised matrices
keyed by (matrix, constructor) in a table both can read, not by deriving
warnings from the decision tree.

## E. Lowering to oxc and printing

Pinned version: `oxc_allocator`, `oxc_ast`, `oxc_codegen`, `oxc_parser`,
`oxc_span`, `oxc_syntax` at `=0.158.0`, the version the reformat tool
`scripts/js-reformat` pins. `compiler-rust/Cargo.toml` depends on oxc 0.49 today (`oxc_parser` for
classifying raw JS in `binary_ast/ppx.rs`); S1 moves that use to the pinned
version so that one oxc is linked. The facts about oxc below were checked
against 0.158.0 by reading `oxc_codegen` and by small experiments (building a
program by hand, reformatting the 676 committed outputs under
`tests/tests/src`).

oxc's API changes between releases (0.158 builds nodes with constructors on
the AST types, such as `Expression::new_call_expression(span, .., &builder)`,
not with methods on the builder as earlier versions did). All construction
goes through one module, `emit/build.rs`, so an upgrade touches one file.

### E.1 The emit step

```
J-level Bir (or, in S1, the JsArena program)
  -> naming            (E.3)   fills printed names
  -> build oxc AST     (E.2)   one walk, in print order
  -> oxc_codegen       (E.8)   text and, on request, source-map tokens
  -> file assembly     (E.4)   directives, header, body, trailer, map comment
```

Module layout: `compiler-rust/src/emit/` with `naming.rs`, `build.rs` (the
only file that names oxc types), `program.rs` (imports, exports, file
assembly), `literal.rs` (numbers, strings), `raw.rs` (raw JS), `sourcemap.rs`.

### E.2 Mapping to oxc AST nodes

Statements:

| IR | oxc node | Notes |
| --- | --- | --- |
| `SDecl` | `VariableDeclaration` (`let`, one declarator) | no initialiser when the value is `undefined`; omitted when dead and pure; an `ExpressionStatement` of the value when dead and impure |
| `SDecl` of a function at top level | `FunctionDeclaration` where `print_function_declaration` is used today | same test as today |
| `SRest` | `VariableDeclaration` with `ObjectPattern` and `BindingRestElement` | property shorthand when the local's printed name equals the label |
| `SExp` | `ExpressionStatement` | dropped when the expression is a variable, a number or `undefined`; a sequence whose side is trivial keeps the other side (`print_exp_statement_of`) |
| `SIf` | `IfStatement` with `BlockStatement` branches | `else` omitted when empty or omitted today; `else { if }` built as `else if` in the cases of `single_else_if_stmt_like_ocaml` |
| `SWhile` | `WhileStatement`, wrapped in `LabeledStatement` when labelled | |
| `SForRange` | `ForStatement` with `let i = a, i_finish = b` when the bound is not simple | `for_range_finish_needs_binding` |
| `SForOf`, `SForAwaitOf` | `ForOfStatement` (`await` flag) | |
| `SSwitch` | `SwitchStatement`, `SwitchCase` | case tests are numeric, string or (for variant tags) `null`, `undefined`, booleans (`print_switch_case_tag`); a `break` is added to an empty case body as today |
| `SReturn` | `ReturnStatement` | argument omitted in the unit-function tail cases |
| `SThrow`, `STry` | `ThrowStatement`, `TryStatement`, `CatchClause` | exception objects per `try_print_exception_block` |
| `SBreak`, `SContinue` | `BreakStatement`, `ContinueStatement` with `LabelIdentifier` | |
| `SDebugger` | `DebuggerStatement` | |
| `SBlock` | spliced into the parent list | no block statement is printed today |

Expressions:

| IR | oxc node | Notes |
| --- | --- | --- |
| `Var` | `IdentifierReference` | printed name from naming |
| `JQualified` | `StaticMemberExpression` or `ComputedMemberExpression` on the import's name | reserved member names are mangled as today |
| `JNumber`, `Const` numbers | `NumericLiteral`; negative values as `UnaryExpression(-)` over the positive literal; `BigIntLiteral`; `Infinity` and `NaN` as identifiers | E.6 |
| `JStr` | `StringLiteral` | E.6 |
| `JTemplate`, `JTagged` | `TemplateLiteral`, `TaggedTemplateExpression` | quasis need both raw and cooked text |
| `JBool`, `JNull` | `BooleanLiteral`, `NullLiteral` | |
| `JUndefined` | `IdentifierReference("undefined")` | today prints `undefined`; `void 0` occurs only inside raw JS |
| `JBin`, `JStrAppend`, `JIn` | `BinaryExpression`, `LogicalExpression` | association rewritten per E.5 |
| `JNot`, `JBnot`, `JTypeof` | `UnaryExpression` | |
| `JIsNullish` | `BinaryExpression(==, x, null)` | also built for the `nullish_or_target` pattern |
| `JCond` | `ConditionalExpression` | |
| `JSeq` | `SequenceExpression`, flattened per E.5 | |
| `JCall` | `CallExpression`; `pure = true` for the `@__PURE__` case | a single unit argument is dropped |
| `JNew` | `NewExpression` | |
| `JIndex` | `ComputedMemberExpression` | |
| `JDot` | `StaticMemberExpression`, or `ComputedMemberExpression` with a string when `property_access_uses_dot` is false | byte-visible, E.9 |
| `JLength` | `StaticMemberExpression(.length)` | |
| `JFun` | `ArrowFunctionExpression` (expression body flag, or block), `FunctionExpression` for methods; `async`; a `Directive` in the body for function directives | eta-reduced to the callee when `eta_reduce_function_body` applies |
| `JObject` | `ObjectExpression`, `ObjectProperty` with `IdentifierName`, `StringLiteral` or `NumericLiteral` keys; `SpreadElement` | key form per `print_property_name`; byte-visible |
| `JArray` | `ArrayExpression` | |
| `JBlockLit` | object, array or exception literal | the choice `print_caml_block` makes today is made when the J node is built |
| `JOptional` | the value, or a helper call, as today | |
| `JJsx` | `JSXElement` or `JSXFragment` in preserve mode when `jsx_printable`; otherwise the runtime call | E.7 |
| `JRaw` | the parsed raw JS, spliced | E.4.3 |
| `JAwait`, `JSpread` | `AwaitExpression`, `SpreadElement` | |

Program:

| Item | oxc node |
| --- | --- |
| ES module import | `ImportDeclaration` with `ImportNamespaceSpecifier` or `ImportDefaultSpecifier`; `WithClause` for import attributes |
| CommonJS import | `let X = require("...")`, with `.default` for default externals |
| ES module exports | one `ExportNamedDeclaration` with `ExportSpecifier`s, `local as exported` when the names differ |
| CommonJS exports | `exports.x = x;` statements, `exports.__esModule = true` after `default` |
| `'use strict'` | a `Directive` of the program |

### E.3 Identifier naming and numbering

Names are decided today while printing (A.7). The naming step reproduces
`Ext_pp_scope` as a walk over the J-level program in print order, before the
oxc AST is built. In S1 it runs over `JsArena`; from S3 over `Bir`.

Algorithm (each line names the function it replaces):

1. Reserve raw JS names (`reserve_js_names`): the set of stamp-0 or JS-flagged
   names of the form `base$N` that the program mentions. Usually empty; the
   arena already knows (`may_use_js_name_of_renamed_local`).
2. Rename locals that shadow a JS global the program refers to
   (`apply_external_shadow_pass`). This is a naming decision and moves here.
3. Top scope: name imports in import order, then name reservations, then
   walk statements, then exports.
4. `name(var)`: if the variable already has a printed name visible from this
   scope, use it. Otherwise take the mangled base
   (`convert_ident_atom`), and pick the first of `base`, `base$1`, ... not
   used in the scope and, for suffixed candidates, not reserved
   (`add_ident`).
5. Entering a function: compute its free variables (once per function;
   `FreeVarScratch`), add the function's own binding, sort by `(order, name)`,
   name each in the enclosing scope if unnamed, then open a scope seeded with
   those names' suffix tables (`with_reserved_ident_scope`).
6. Walk in the order the printer prints: declaration name before value except
   where today reserves first (`print_variable_declaration` reserves the
   function's environment before naming the binding), parameters before body,
   `for` variable before bounds, `catch` variable before handler.
7. Fresh names the printer invents (`fresh_scoped_name`: `i_finish`, the
   `this` binding of methods) are created here in the same positions.

Data: `printed: Vec<Name>` indexed by variable; a scope is a small map from
base name to (next suffix, list of (variable, printed)). Scopes are pooled as
`spare_name_scopes` are today.

The walk order must equal print order including the cases where the printer
prints something other than the tree (eta-reduced functions, omitted dead
declarations, omitted `else`). Therefore naming and AST building share one
traversal skeleton (`emit::walk`), with naming as its first pass and building
as its second; a decision such as "this declaration is not printed" is
computed once and read by both.

Stamps. Step 5 is the only place where the order of two identifiers, rather
than their identity, reaches the output: when two not-yet-named identifiers
with the same base name are free in the same function, the one with the
smaller stamp gets the unsuffixed name. `Bir` keeps a per-variable `order`
(creation sequence number) for this. Variables from the typed tree take the
order of their type-checker identifier; variables the backend creates take
the next number. Because rounds sweep in today's traversal order (C.2, row
9), relative order is preserved for the cases that matter.

Since type-checker stamp parity is not a requirement, this dependence should
not survive. S1 adds a counter to the naming step (how often step 5 names two
same-base identifiers in one reservation) and reports it over all corpora. If
it is zero everywhere, the sort key is redefined as "position of the binder
in print order", which needs no stamps, and row 9 of C.2 is closed. If not,
the cases are listed and the canonical key is chosen to match them. Unknown
until measured.

Cost (estimated): one walk with a hash lookup per binder and none per use
(a use reads `printed[var]`), about 300 instructions per source line.

### E.4 Text outside the AST: directives, header, comments, raw JS

**E.4.1 File assembly.** These are written as text around `oxc_codegen`'s
output, not as AST nodes:

- file-level directives from the source (`file_directives`), one per line,
  before the header. They are arbitrary text (the committed
  `tests/tests/src/directives.mjs` starts with `first directive;`, which oxc
  does not parse);
- `// Generated by ReScript, PLEASE EDIT WITH CARE` unless
  `no_version_header`;
- the empty-output comment, in which case nothing else is written;
- the purity trailer `/* No side effect */` or `/* <reason> Not a pure
  module */`;
- the `sourceMappingURL` comment.

`'use strict'` for CommonJS and function directives are oxc `Directive`s.

**E.4.2 Comments.** oxc prints a comment only if it is in
`Program::comments`, has `position = Leading`, and its `attached_to` equals
the start offset of a node at one of the places `oxc_codegen` looks
(statements, declarations, some expression positions); the text is read from
`Program::source_text` at the comment's span. Checked by experiment: a
hand-built program with a synthetic source text and two comments attached to
statement spans prints both.

Comments today's output contains (counted over `tests/tests/src`):

| Comment | Count | In the new backend |
| --- | ---: | --- |
| Header, trailer, empty-output | every file | file assembly (E.4.1) |
| `/* @__PURE__ */` before exception creation calls | 74 | `CallExpression::pure`; oxc prints the annotation itself |
| Comment-only raw JS statements written by the user (`// ...`, `/* ... */`) | 2 | statement-level oxc comments, text in the synthetic source |
| Constructor names on integer constants, `/* [] */0` | 372 | dropped |
| Character comments on numbers, `/* 'a' */97` | 108 | dropped |

The last two are decorations from `pointer_info_comment_text` and
`format_char_comment`. oxc cannot print a comment at an arbitrary expression
position: reformatting the reference keeps `tl: /* [] */ 0` in a property
value and drops `return /* [] */0` (1,230 comments in, 1,108 out over the
test outputs). Reproducing oxc's partial behaviour would tie the output to an
accident. Decision: decoration comments are not part of the output contract
and are not emitted; the gate removes them from the reference (S0). This is
the one visible change to the emitted text besides layout, and it needs the
project owner's confirmation (section I).

**E.4.3 Raw JS.** `%raw` expressions and statements are printed verbatim
today. oxc has no verbatim node, so raw JS is parsed with `oxc_parser` into
the module's allocator and spliced:

- an expression: `Parser::parse_expression`; a statement: parsed as a
  program and its statements spliced;
- comments inside the snippet are carried: the snippet text is appended to
  the synthetic source text, and the snippet's spans and comment spans are
  shifted by its offset with a `VisitMut` over the spliced subtree. Without
  the shift, checked by experiment, the snippet's own spans leak into the
  source map and its comments are lost;
- the result of the parse is cached per snippet text within a module (the
  purity test `raw_js_is_pure` and `classify_js_stmt` already parse it once
  with oxc; they can share the parse);
- a snippet oxc cannot parse (today it is emitted as is, whatever it is) is
  emitted as a placeholder identifier that file assembly replaces with the
  verbatim text after printing. Such a module cannot be checked by the
  reformat gate, in the reference or the candidate; the gate lists it as
  "verbatim" and compares the text around the placeholders.

Parentheses around raw functions and objects (`raw_js_expression_needs_paren`)
are no longer decided by us: oxc parenthesises a spliced expression by
precedence.

### E.5 Parentheses and association

`oxc_codegen` inserts parentheses from precedence, so the emit step never
builds a `ParenthesizedExpression` (with one exception, E.7). The reference
is reformatted with `preserve_parens` off, so redundant parentheses in it
vanish.

The catch: the gate compares against what today's *text* parses to, which is
not always the tree today's IR holds. Where the printer omits parentheses that
the tree's shape would need, the text re-associates:

- `And(a, And(b, c))` prints `a && b && c`, which parses as
  `(a && b) && c`; the same for `||` and `|`
  (`test_print_chained_logical_and_without_right_nested_parens_like_ocaml`
  and its siblings);
- `Seq(a, Seq(b, c))` prints `a, b, c`, one flat sequence;
- string concatenation chains.

These are meaning-preserving (the operators are associative on the values
involved), and the emit step must build the re-associated tree: left-nested
`LogicalExpression`s, one flat `SequenceExpression`. The complete list is
whatever `print_expression_desc` and `op_precedence` print without
parentheses although the child has equal precedence on the non-associative
side; S1 derives it from that function case by case, and the oracle (old
text, reformatted, against new text) finds any case missed.

Statement-start ambiguities (`{`, `function`, `let [`) and arrow bodies that
are object literals are parenthesised by oxc.

### E.6 Literals

Numbers. `oxc_codegen` prints a `NumericLiteral` from its `f64` value in the
shortest form it knows, ignoring the source spelling (checked: `0x10` prints
`16`, `1.50` prints `1.5`, `1_000` prints `1e3`, `0.1e-7` prints `1e-8`, and
`123456789012345680000` prints `0x6b14e9f812f368000`). The emit step
therefore passes values:

- integers and floats: parse the IR's spelling (after
  `transform_float_literal` and `normalize_hex_float_literal`) to `f64` with a
  correctly rounded parser. Both JavaScript and the reference reformat read
  the same spelling to the same value, so the bytes agree;
- negative numbers: `UnaryExpression(-, literal)`, which is what the
  reference text parses to;
- `bigint`: `BigIntLiteral` with the decimal digits;
- 64-bit integers and other values the IR already spells as calls or
  strings are unaffected.

Strings. The JS IR stores string values as bytes (`string_literal::bytes_of`):
valid UTF-8 sequences are characters, other bytes above 127 are printed as
`\xHH` (`print_string`). The emit step decodes with the same rule to a Rust
`str` (an invalid byte `b` becomes the character U+00`b`) and passes the
value; oxc chooses quotes and escapes (checked: it prints non-ASCII
characters and some control characters unescaped, and escapes `</script`).
Template literals need raw and cooked text for each quasi; JSON literals
(`JsonLiteral`) are parsed as expressions. Property names follow the same
decoding.

Both spellings are absorbed by the gate, because the reference goes through
the same printer.

### E.7 JSX preserve mode

With `jsx_preserve`, a `JJsx` node that `jsx_printable` accepts becomes a
`JSXElement` (or `JSXFragment`), with `JSXIdentifier` or
`JSXMemberExpression` names, `JSXAttribute` with string or expression
container values, `JSXSpreadAttribute`, and children as elements or
`JSXExpressionContainer`s. Otherwise it becomes the runtime call
(`print_jsx_call`). The tests that decide are today's (`is_jsx_tag`,
`is_jsx_value_name`, `is_jsx_attribute_name`, `is_empty_fragment`).

Known oxc defect (0.158.0, checked): a sequence expression inside a JSX
expression container prints without parentheses, `{a, b}`, which does not
parse. The committed `jsx_preserve_cases.mjs` hits it. The emit step wraps
such a child in an explicit `ParenthesizedExpression`; the reformat tool
applies the same wrap to the reference after parsing (S0), and the defect is
reported upstream.

The inlining rule that protects JSX tags in preserve mode
(`simplify_alias`, the `Pjsx` case) is unaffected.

### E.8 Printing, source maps, allocator

Printing: `Codegen::new().with_options(options).build(&program)`, default
options (tabs, double quotes), as the reformat tool. Layout options are not
exposed; if two-space indentation is wanted it is one option
(`indent_char`, `indent_width`) set identically in the compiler and the tool.

Source maps. What today's contract needs (`js_ir/source_map.rs`): Source Map
v3 with `file`, `sourceRoot`, `sources` relative to the output, optional
`sourcesContent`, mappings at statements, initialisers, cases and located
expressions, possibly into more than one source (inlined code keeps its
file), in linked, inline or hidden mode.

What oxc offers: when `CodegenOptions::source_map_path` is set, `build`
returns an `oxc_sourcemap::SourceMap` whose tokens map generated positions to
line and column in `Program::source_text`, computed from each node's
`span.start` (and some `span.end`s). It supports one source and takes the
source text from the program.

Design: the program's `source_text` is a **synthetic text**: the `.res`
source, followed by other source files that located nodes refer to (rare),
followed by the pool of comment and raw-JS text (E.4). A node that should be
mapped gets a span at its original offset; every other node gets an empty
span, which oxc skips. After printing, `emit/sourcemap.rs` reads the tokens,
drops those that point into the pool, splits the rest by which file's region
they fall in, rebases lines, and feeds them to today's `SourceMapBuilder` for
JSON output (so `sources`, `sourceRoot`, `sourcesContent` and the three modes
are unchanged). Checked by experiment: tokens come out for exactly the nodes
with non-empty spans, plus end-of-node tokens for some of them.

`LamLoc` handles must resolve to byte offsets; `LamLocTable` stores positions
with `cnum`, so this is a lookup.

Source maps cannot stay byte-identical to the OCaml compiler's, because
generated columns change with layout. The gate for maps becomes: the ordered
list of original positions (source, line, column) of the mappings, with
consecutive duplicates removed and oxc's end-of-node tokens excluded, equals
the list from today's printer for the same module. S1 specifies it against
`tests/build_tests/source_map`.

Allocator ownership. One `oxc_allocator::Allocator` per worker thread, held
in the worker's compilation context beside its other scratch state. For each
module: build the AST, print, then `Allocator::reset()` (which keeps the
largest chunk). The AST, the synthetic source text and parsed raw JS live in
it and never outlive the module; nothing from it is stored in `Bir`, in
summaries or across modules. `Program<'a>` borrows the allocator, so the emit
function has the shape
`fn emit(bir: &Bir, alloc: &Allocator, opts: &EmitOptions) -> Emitted` with
`Emitted { code: String, map: Option<String> }` owning its data.

Cost (estimated): building the AST is about one allocation and a few writes
per J node, about 350 instructions per source line; oxc printing is 950
(measured); naming 300. Total 1,600 against 5,800 today.

### E.9 What the reformat gate absorbs and what it does not

Absorbed (the reference and the candidate both pass through `oxc_codegen`):

| Difference | Why it is harmless |
| --- | --- |
| Line breaks, indentation, spaces, blank lines | layout |
| Quote style and escape choice in strings | same value |
| Numeric spelling | same value |
| Redundant parentheses | same tree |
| Parentheses around a single arrow parameter | same tree |
| Semicolons and trailing commas (`export { a, }`) | same tree |
| `new Foo` and `new Foo()` | same tree |
| Space before `:` in `case 1 :` | layout |

Not absorbed; the emit step must build exactly what today's text parses to:

| Construct | Byte-visible choice |
| --- | --- |
| Member access | `a.b` or `a["b"]` |
| Object keys | identifier, string or number key; shorthand or not |
| Functions | arrow or `function`; expression body or block; declaration or `let` |
| Declarations | one `let` per binding or several declarators; with or without initialiser |
| `undefined` | `undefined` or `void 0` |
| `if` | `else if` or `else { if }`; empty `else` present or not; braces |
| Empty statements | `;` is a statement in the AST |
| Sequences and operator chains | nesting (E.5) |
| Negative numbers | unary minus on a literal or a negative literal's spelling |
| Strings and templates | `"a"` or `` `a` `` |
| Calls | argument list, including the dropped unit argument |
| Switch | case order, grouping, `break`, `default` position |
| Labels | name and presence |
| Imports and exports | form (`* as`, default), order, attributes, `as` names |
| Directives | `'use strict'`, function directives |
| Comments | which exist and what they are attached to (E.4.2) |
| JSX | element or call; attribute forms; text children |

Outside the gate (the reformat cannot see them):

| Item | Check |
| --- | --- |
| File directives, header, trailer | compared as text by the tool (S0) |
| Modules with unparsable raw JS | text comparison around placeholders |
| Source maps | the mapping-sequence gate of E.8 |
| Programs the reformat rejects in the reference | listed by the tool; today one committed file after the directive fix |

### E.10 The two committed outputs the reformat tool rejects today

`scripts/js-reformat check` over the committed outputs reports every file of
`packages/@rescript/runtime/lib` and all but two of `tests/tests/src` as fixed
points. The two exceptions, and what each means for S0 and S1:

| File | Cause | Resolution |
| --- | --- | --- |
| `directives.mjs` | The file starts with the source's file-level directives, `first directive;` and `second directive;`, written verbatim before the header (`print_deps_program_with_directives_and_options`). They are arbitrary text, here two identifiers in a row, which is not JavaScript. | Neither the output nor the parser options change. Directives are not part of the AST: file assembly writes them (E.4.1), and the tool splits the lines before the header off both files and compares them as text (S0.1). The rest of the file parses. |
| `jsx_preserve_cases.mjs` | The file parses, but `oxc_codegen` prints a sequence expression inside a JSX expression container without parentheses (`{a, b}`), which does not parse again. | The emit step never relies on oxc here: it wraps the sequence in an explicit `ParenthesizedExpression` (E.7). The tool applies the same wrap to the parsed reference, so both sides print `{(a, b)}`. |

After S0.1 the tool must report zero failures on both trees; any file it
cannot parse later is listed, not skipped silently.

## F. Cross-module data

What a dependent reads is listed in A.8. Nothing about it is output-visible
except through the decisions it feeds (inlining, call form, constant
propagation, whether an import is kept), so its content must be the same and
its representation is free.

| Datum | From `Bir` | Notes |
| --- | --- | --- |
| Arity of each export | read from the export's `Fact` after round 7: `Function` gives the arity of the node (`get_arity` on it), `Block` gives one arity per field | no spine walk; today `cmj_export_arities` walks the spine and searches bindings |
| Constant exports | `Fact::Const` of the export, restricted to `true`, `false`, `null`, `undefined` | |
| Purity | the root's `PURE` flag after round 7, with the reason text computed as `module_side_effect_reason` does on the top-level spine | the reason names the first effectful binding and is printed in the trailer |
| Closed lambdas | a **fragment**: the export's subtree copied into a self-contained `Bir` slice | below |

Fragments. With cross-module inlining on, an exported function that passes
today's tests (`safe_to_inline`, closed, and `@inline`, functor, or small) is
stored as a fragment: the nodes of its subtree in a contiguous run with
handles relative to the run, plus the rows of the payload tables it refers to
(constants, primitives, function headers, variable names), in the same
relative encoding. Exporting is `copy_subtree` into an empty `Bir`.
Importing into a dependent is appending the runs and adding offsets to
handles, one linear pass over the fragment with no tree walk and no
per-node allocation; this is what "without re-encoding" means here. The
in-memory registry holds fragments behind an `Arc`; the on-disk form for
incremental builds is the same arrays as bytes plus a string table. Today
the same data is a boxed `Lambda` tree per export (`LamArena::export`),
serialised with serde and re-imported with `LamArena::import`.

Locations inside a fragment keep their file (`LamLocTable::import_lambda`
does this today); the fragment carries the rows of the location table it
uses.

Transition. Summaries are produced at the end of level L, so they change
representation in S6, after S4. Until then a module compiled by the new path
exports today's types (arities and constants are small values; closed lambdas
are exported from `Bir` to a `Lambda` tree, a cost only when cross-module
inlining is on). Modules compiled by either path can therefore depend on each
other in the same build at every stage.

## G. The oracle harness and the switch-over

### G.1 Running both

`CompilerOptions` gets `backend: BackendMode`:

| Mode | Behaviour |
| --- | --- |
| `Legacy` | today's code only |
| `New` | the new path; if it reports `Unsupported(reason)` for a module, the legacy path compiles that module |
| `Check` | both paths compile every module the new path supports; outputs are compared; the legacy output is used; a difference is an error naming the module, the stage and the first differing line |

The mode comes from the build configuration or the environment variable
`RESCRIPT_BACKEND`; the default is `New` once a stage has switched over and
`Legacy` before. The JS printer has the same switch during S1
(`RESCRIPT_JS_PRINTER`).

Both paths start from the same input for the stage being replaced (the
simplified Lambda in S3, the lowered Lambda in S4, the typed tree in S5) and
each has its own identifier counter started at the same value. The new path
never touches the thread-local legacy counter (`Ident::set_current_time`).

What is compared:

- the emitted text, byte for byte. From S1 on both paths end in the same
  emit step, so no reformatting is involved in comparing old and new;
- the summaries of section F, structurally;
- the import list.

`Unsupported` is returned by the new path at the first construct it has no
rule for. It is an ordinary value, not a panic, and it carries a static
reason string. A stage is built by removing reasons.

### G.2 Coverage and the ratchet

In `Check` and `New` modes the build can write a report (`RESCRIPT_BACKEND_STATS`):
modules compiled by the new path, modules that fell back, and a histogram of
reasons. CI runs the repository's corpora (`tests/tests`, the runtime
library, the parity fixtures) in `Check` mode and fails on any difference.
The number of fallback modules per corpus is committed in
`compiler-rust/tests/backend_coverage.txt`; CI fails if it grows. The
external-corpus mode of `scripts/test_js_output_parity.sh`
(`--with-external`) is run in `Check` mode before a stage is declared
complete.

Reference parity against the OCaml compiler's output stays the release gate
throughout and after: `scripts/test_js_output_parity.sh`,
`scripts/test_stdlib_output_parity.sh` and the gentype suite, switched to
reformat-and-compare in S1.

### G.3 Granularity

- S1 switches per build (one option), since the printer either handles a JS
  IR node kind or is unfinished.
- S3 and S5 take over module by module, growing construct by construct: a
  module is compiled by the new path when every construct in it is
  supported.
- S4 has no useful per-construct split (a pass sees every node). Its rounds
  land one by one behind `Check`-only use, with a diagnostic comparison of
  the exported Lambda after each round against the legacy pipeline cut at the
  same point, and switch on together.

### G.4 Deletion

A stage's legacy code is deleted in its own pull request when the fallback
count is zero on every corpus including the external one, `Check` mode has
been clean on trunk for two weeks, and the instruction count shows the
expected saving. Unit tests that assert the legacy code's printed text
(`lam_compile_tests.rs` and its siblings, the tests in `printer.rs`) are
deleted with it; the cases worth keeping are moved first to source fixtures
with expected JavaScript, which survive any backend.

## H. Staged plan

Every pull request leaves trunk passing and shipping: new code is dormant
(`Legacy` default or `Unsupported` fallback) until its stage switches.
Dormant code can still move the instruction count through code layout; a
pull request that does so beyond 0.1% carries the
`Instruction-count-increase:` trailer with that explanation.

Savings arithmetic, in instructions per source line (today 33,600):

| After | Conversion | Rewrites | Lowering, JS passes | Emit | Files, other | Bridges | Total | Saved, share of build |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Today | 8,700 | 8,400 | 9,500 | 5,800 | 1,200 | 0 | 33,600 | |
| S1 | 8,700 | 8,400 | 9,500 | 2,300 | 1,200 | 0 | 30,100 | 2.8% |
| S3 | 8,700 | 8,400 | 2,000 | 1,600 | 1,200 | 500 | 22,400 | 6.3% |
| S4 | 8,700 | 1,800 | 2,000 | 1,600 | 1,200 | 500 | 15,800 | 5.4% |
| S5 | 2,900 | 1,800 | 2,000 | 1,600 | 1,200 | 0 | 9,500 | 5.1% |
| S6 | 2,900 | 1,800 | 2,000 | 1,600 | 700 | 0 | 9,000 | 0.4% |

"Bridges" is the linear copy from the legacy arena of the stage in front
into `Bir` (estimated at 500). In S1 naming still runs on `Ident` hash maps,
hence 2,300 for emit instead of 1,600.

### H.1 Pull requests

"Hand-off" says whether the pull request can be given to a less capable
model with this document as its specification.

| PR | Change | Files | Gate | Size (lines) | Depends on | Hand-off |
| --- | --- | --- | --- | ---: | --- | --- |
| S0.1 | Reformat tool as a library and binary; modes: split preamble and trailer and compare them as text; drop decoration comments (a block comment directly before a numeric literal); wrap sequences in JSX containers; list unparsable files instead of failing | `scripts/js-reformat/` | its tests; `check` accounts for every file of `tests/tests/src` and the runtime library (two fail today, E.10) | 400 | none | yes |
| S0.2 | Parity scripts get a `--reformat` mode beside the exact mode | `scripts/parity_lib.sh`, `scripts/test_js_output_parity.sh`, `scripts/test_js_output_parity_fixtures.sh`, `scripts/test_stdlib_output_parity.sh` | both modes pass on trunk | 200 | S0.1 | yes |
| S1.1 | `emit/`: naming, oxc AST from `JsArena`, program assembly, literals, raw JS; `RESCRIPT_JS_PRINTER=oxc`; default legacy | `compiler-rust/src/emit/*`, `Cargo.toml`, `driver.rs` (`render_js_program`) | H.2 | 3,500 | S0.1 | yes, H.2 is the spec; E.5 needs a careful reviewer |
| S1.2 | Source maps through oxc tokens; mapping-sequence gate | `emit/sourcemap.rs`, `js_ir/source_map.rs`, `tests/build_tests/source_map` | E.8 gate on the fixture and on `tests/tests` built with maps | 500 | S1.1 | yes |
| S1.3 | Switch parity suites and CI to reformat-and-compare | scripts, `.github/workflows` | suites pass with the oxc printer and with the legacy printer | 150 | S0.2, S1.1 | yes |
| S1.4 | Default printer is oxc. Second commit: regenerate committed outputs (about 900 files with the generated header under `tests/`, `packages/@rescript/runtime/lib`, `rewatch/testrepo`). Changelog entry | option default, generated files | all suites; instruction count falls by about 2.8% | 20 plus generated | S1.2, S1.3 | yes |
| S1.5 | Remove the legacy printer's layout code from release builds; it stays under `cfg(test)` while `lam_compile` tests print with it | `js_ir/printer.rs`, `js_ir/program_printer.rs` | suites | −3,000 | S1.4, two clean weeks | yes |
| S2.1 | `Bir`: nodes, pools, views, constructors without rules, `validate`, text dump | `compiler-rust/src/bir/{mod,node,pools,vars,edit,validate,dump}.rs` | unit tests; size assertions; invariants of B.4 under random edits | 2,500 | none | yes, section B is the spec |
| S2.2 | Bridges: import from `LamArena` and from `JsArena`, export to `LamArena`; `BackendMode`, `Unsupported`, the report, the ratchet file, the CI job | `bir/bridge.rs`, `driver.rs`, `rewatch/src/build/compile.rs`, workflow | import then export is the identity on all corpora (compared with `sexp_lambda`) | 1,500 | S2.1 | yes |
| S3.1 | Emit reads J-level `Bir` (the emit walk is written against a view trait implemented by `JsArena` and `Bir`); naming on `VarId` | `emit/*` | `JsArena` to `Bir` to text equals `JsArena` to text on all corpora | 800 | S1.4, S2.2 | yes |
| S3.2 | J normalising rules and rounds J1 to J4, fed by importing the JS IR before the JS passes | `bir/j/{norm,inline_return,rest,subst,shake}.rs` | `Check` against the legacy JS passes | 3,000 | S3.1 | yes, each rule cites its function (C.4) |
| S3.3 | Lowering L to J, first set: constants, variables, primitives, calls by arity, functions, `let`, `if` and short circuits, sequences, exports and their coercion; everything else `Unsupported` | `bir/lower/{mod,expr,prim,call,export}.rs` | `Check`; coverage reported | 4,000 | S3.2 | partly: needs a table mapping each context function of `lam_compile.rs` (A.5) to a continuation case, written by whoever starts the stage |
| S3.4 to S3.9 | One construct group each: switches and variants; static catch and exits; tail loops; loops, `try`, `let rec`; externals and FFI arguments; JSX, record spread, `await`, dynamic import | `bir/lower/*` | `Check`; the ratchet falls | 1,500 to 3,000 each | S3.3 | partly, as S3.3; static catch is the hardest and should go to the strongest reviewer |
| S3.10 | Default `New` for level J; then delete `lam_compile*.rs`, `js_pass_*.rs`, `js_shake.rs`, `js_exp_make.rs`, `js_ir/` except what emit's tests need | | fallback zero; instruction count falls by about 6.3% | −45,000 with tests | S3.9 | yes |
| S4.1 | Engine: rounds, summaries, worklist, snapshots; L normalising rules (built: C.5 to C.7) | `bir/engine.rs`, `bir/l/norm.rs`, `bir/replay.rs` | building through the rules equals `LamArena`'s constructors on all corpora: shadow stage `lambda-norm` | 2,000 | S2.2 | no: C.1 and C.2 rows 1, 3, 5 need design judgement while building |
| S4.2 to S4.8 | One round each, in pipeline order (C.3), each with the diagnostic comparison of G.3 | `bir/l/{flatten,exits,alias,beta,alpha,lets,sroa,exports}.rs` | diagnostic comparison clean on all corpora; `Check` once all rounds exist | 600 to 2,000 each | S4.1 | yes for the rules; `alias` and `beta` need a strong reviewer |
| S4.9 | Default `New` for level L; delete `lam_pass_*.rs`, `lam_beta_reduce.rs`, `lam_compile_main.rs` and the analyses only they use | | fallback zero; instruction count falls by about 5.4% | −8,000 | S4.8, S3.10 | yes |
| S5.1 | Profile of conversion and match compilation on the application; a builder trait implemented by `RawArena`, with the converter and match compiler generic over it | `raw_lambda/*` | no output change, no instruction increase | 1,500 | none | yes |
| S5.2 | `Bir` builder implementing the trait; `lower.rs`'s rewriting inside the constructors | `bir/build.rs` | `Check` from the typed tree | 2,500 | S5.1, S4.9 | yes |
| S5.3 to S5.5 | Match compiler: structural-hash action sharing; row pool; lazy contexts and the single-column fast path | `raw_lambda/matching.rs` | `Check`; each shows its saving | 800 to 1,500 each | S5.1 | no: each needs the profile and an argument that the tree is unchanged |
| S5.6 | Default `New` from the typed tree; delete `RawArena`, `lower.rs`, `LamArena`, the bridges, `key_encode.rs` | | fallback zero; instruction count falls by about 5.1% | −15,000 | S5.5 | yes |
| S6 | Summaries from facts; fragments for closed lambdas; stored format | `bir/summary.rs`, `cmi/persistent_env.rs`, `lambda/lam_loc.rs` | `Check` on summaries; a build with cross-module inlining on | 1,200 | S4.9 | yes, section F is the spec |
| S7 | For modules whose typed tree nobody reads, the type checker calls the `Bir` builder directly | type checker | own design | | S5.6 and the type checker rewrite | no |

### H.2 Stage S1 in full

S1 is built first and is specified here completely.

**Input.** A `JsDepsProgram` after the six JS passes (`Program { arena,
block, exports, export_set, name_reservations }`, `modules`,
`side_effect`), `JsFileSettings` (`file_directives`, `debug`,
`jsx_preserve`), the `ModulePathResolver`, and the source-map options.

**Output.** The same `(String, Option<String>)` that
`print_deps_program_with_directives_and_options` and
`print_deps_program_with_source_map` return, selected in
`driver::render_js_program` by `options.js_printer`.

**Structure.**

1. `emit::walk` defines the traversal in print order and the print-time
   decisions as pure functions of the JS IR, each a port of the printer
   function named in A.7: `prints_declaration`, `eta_target`,
   `function_form` (arrow, expression body, empty body, declaration),
   `drops_tail_return`, `else_form`, `drops_unit_argument`, `nullish_target`
   (compare the two operands structurally instead of by printed text; the
   harness confirms equality with the textual test), `negation_form`,
   `block_literal_shape`, `jsx_form`, `member_form`, `property_key_form`,
   `finish_binding`.
2. `emit::naming` runs the walk once and fills a map from `Ident` to printed
   name per scope, following E.3 exactly. The shadowing rename
   (`apply_external_shadow_pass`) stays a JS pass in S1 and moves into naming
   in S3.2.
3. `emit::build` runs the walk a second time and constructs the oxc AST
   (E.2), re-associating per E.5, with literals per E.6, raw JS per E.4.3,
   comments per E.4.2.
4. `emit::program` builds imports and exports, calls `Codegen`, and
   assembles the file (E.4.1).
5. The allocator is created per call in S1.1 and moved to the worker context
   in S3.1, when the emit step gets its permanent signature.

**Invariants.**

- Naming and building visit binders and uses in the same order and take the
  same print-time decisions; both call the functions of step 1 and nothing
  else decides.
- No oxc type appears outside `emit/build.rs` and `emit/program.rs`.
- Nothing allocated in the oxc allocator is reachable after `emit` returns.
- With the legacy printer selected, output is byte-identical to before.

**Gate.**

1. Oracle: for every module of `tests/tests`, the runtime library, the
   parity fixtures and the external corpus, in ES module and CommonJS format,
   with and without JSX preserve and debug mode where fixtures exist:
   `reformat(legacy printer text)` equals the oxc printer's text, where
   `reformat` is the S0.1 library with decoration comments dropped. A test
   in `compiler-rust/tests/` runs this for the in-repository corpora.
2. Fixed point: reformatting the oxc printer's text returns it unchanged.
3. Reference: the parity suites in `--reformat` mode pass with the oxc
   printer.
4. Naming counter of E.3 reported for all corpora.
5. `cargo test` and `cargo clippy` for `compiler-rust` and `rewatch`; the
   playground (wasm) build links.
6. After S1.4, the instruction-count workflow shows the saving.

**Not in S1.** Any change to which names are chosen, which declarations are
dead, or any JS IR node; removal of decoration comments is the only
difference in emitted tokens.

### H.3 What can run in parallel with the type checker rewrite

The type checker rewrite keeps the typed tree as its interface until both
projects have landed.

| Stage | Reads the typed tree | Parallel with the type checker rewrite |
| --- | --- | --- |
| S0, S1, S2, S3, S4, S6 | no | yes |
| S5.1 (profile, builder trait) | yes, through today's converter | yes, but it touches `convert.rs` and `matching.rs` widely; land it in one piece and early |
| S5.2 to S5.6 | yes | yes while the typed tree is unchanged; any change to typed patterns (`PatArena`, `tast_arena`) must be coordinated |
| S7 | replaces it | no: after both |

Within the backend, S1 and S2 are independent of each other; S4.1 to S4.8
can be developed while S3 is in progress, since both only need S2.2, but S4
switches on after S3.

## I. Risks and open questions

Each with the recommended answer.

1. **Decoration comments disappear from the output** (`/* [] */`, character
   comments; E.4.2). Recommended: accept and state it in the changelog. They
   carry no meaning for tools, and oxc cannot place them reliably. Needs the
   project owner's confirmation before S0.1 encodes it in the gate.
2. **Indentation becomes tabs** with default codegen options. Recommended:
   keep the defaults, as decided for the gate; if spaces are wanted it is one
   option, set identically in the tool and the compiler, before S1.4
   regenerates outputs.
3. **Naming depends on stamp order in one corner** (E.3). Recommended:
   measure in S1 (gate item 4), then replace the stamp by binder position if
   the count is zero. If it is not zero, the type checker rewrite must
   preserve relative identifier order for those cases or accept the same
   canonical key; decide with the measurement in hand.
4. **Facts that today go stale between sweeps** (C.2, row 3). Unknown
   whether any output depends on them. Recommended: build S4 with current
   facts and let the harness answer; the frozen-bit fallback is specified.
5. **Snapshots for inlining** (C.2, row 1) cost a copy per inlinable function
   per inlining round. Recommended: copy on first write only; if the profile
   shows more than 0.2% of the build, restrict snapshots to functions that
   have at least one call site left (`uses > 0`).
6. **Sweep order is today's order, so the engine cannot fuse rounds freely.**
   The estimate of 1,800 instructions per line for rewrites assumes pruned
   sweeps and no spine rebuilding, not fewer rounds. If the measured cost
   after S4 is above 2,500, the next step is fusing pairs of sweeps where
   independence can be shown rule by rule (C.3), not relaxing the order.
7. **oxc is a moving dependency with defects** (JSX sequences, E.7; partial
   comment support). Recommended: pin exact versions, keep oxc types in two
   files, upgrade deliberately with the fixed-point gate, report defects
   upstream, and never work around a defect on one side of the gate only.
8. **Raw JS that oxc cannot parse.** Recommended: verbatim placeholders
   (E.4.3). Open: whether to warn; the compiler accepts such code today, so
   no.
9. **Source-map parity changes meaning** from bytes to mapping sequence
   (E.8), and maps gain oxc's extra end-of-node tokens. Recommended: adopt
   the sequence gate; confirm with the project owner that byte-identical maps
   are no longer required once layout differs.
10. **Several output targets recompile the whole backend** per target (A.1).
    `Bir` could be lowered once and emitted per target if only import paths
    differed. Unknown whether anything else depends on the target (dynamic
    import paths are built during lowering). Recommended: keep per-target
    runs through S5, then make the import path a late-bound value resolved at
    emit.
11. **Sharing the decision tree with exhaustiveness checking** (D.2).
    Recommended: no.
12. **Dumps and tooling that show Lambda** (`-drawlambda`, `-dlambda`, the
    playground's intermediate views, `scripts/test_lambda_parity.sh`) lose
    their subject in S4 and S5. Recommended: a `Bir` dump replaces them; the
    Lambda parity script is retired with the Lambda arena, since Lambda parity
    is a diagnostic, not a requirement.
13. **Dormant code and the instruction-count check.** Recommended: the
    trailer, with the reason "dormant backend code, layout only", verified by
    showing the hot functions' counts unchanged.
14. **Binary size and the playground build** grow with `oxc_codegen` and
    `oxc_parser`. Unknown by how much. Checked in S1.1 (gate item 5).
15. **The match compiler's fast path and lazy contexts** (D.1) are the only
    places where this design changes an algorithm rather than its data.
    Recommended: land them last (S5.3 to S5.5), each behind `Check`, and drop
    any that the harness cannot make exact.

What could not be determined from the code, and the experiment that would:

| Question | Experiment |
| --- | --- |
| How match compilation's 3.5% divides between key strings, pattern copies and contexts | profile of `matching.rs` on the application (S5.1) |
| The cost of `types/parmatch.rs` | same profile, type-checking phase |
| How often naming resolves two same-named identifiers by stamp | the counter of S1 |
| Whether stale facts affect any module | `Check` in S4 |
| Whether the emulated hash-table order ever decides import order | assert in `Check` that sorting alone gives the same list |
| The cost of building the oxc AST (350 per line is an estimate) | measured in S1.1 |
| Whether the 0.6% for writing files can be reduced | not examined; outside this design |
| CommonJS and debug-mode coverage of the committed corpora | count in S0.2 |
