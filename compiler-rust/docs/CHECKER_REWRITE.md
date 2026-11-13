# The type checker, rewritten: design for the highest ceiling

This document designs a type checker written from nothing. It takes as given
that in-place changes to `types/typecore.rs`, `types/ctype.rs`,
`types/typemod.rs`, `types/env.rs` and `types/thread_store.rs` (72,566 lines,
STATUS.md 1.5) will not make type checking cost less than half of what it
costs today, and that "a new core saves nothing" (CHECKER_REDESIGN I.6) is
not an answer until every cost item has been measured and a design for it
has been tried.

The contract does not move: the same programs are accepted and rejected;
errors and warnings are the same in text and location; the generated
JavaScript is byte-identical; output does not depend on worker count or
scheduling; no `.cmi` files; the artifacts editor tooling reads stay usable.
Everything else may change.

Sections:

1. Where the instructions go (measured).
2. What a design that owes nothing to today's code pays for each item, and
   what is observable.
3. The design.
4. Proof by prototype.
5. The route and the slices.
6. Worker prompts.
7. The ceiling, and the questions for the owner.

Conventions. "The application" is a 3,735-module application. "The test
project" is `tests/tests`. An instruction count is retired instructions
under Valgrind with one worker (`RAYON_NUM_THREADS=1`), clean build. Every
number is labelled *measured* (by this document, with the method), *quoted*
(with its source), *extrapolated* (from a prototype) or *estimated*.

## 1. Where the instructions go

### 1.1 Method

- Machine: x86-64 Linux, 8 cores. Trunk 7e1dbc2bd4. `rescript` built with
  the release profile (fat LTO) and line tables
  (`CARGO_PROFILE_RELEASE_DEBUG=line-tables-only`,
  `CARGO_PROFILE_RELEASE_STRIP=none`), not the profile-guided build.
- Two runs per project, each a clean build with one worker:
  1. `valgrind --tool=callgrind --dump-instr=yes --collect-atstart=no
     --toggle-collect=rescript_compiler::types::typemod::type_structure`:
     only `type_structure` and everything it calls is counted, into the
     allocator, `memcpy`, hashing and drop glue. This is "the checker" of
     the tables below, the same definition as CHECKER_REDESIGN K.1.
  2. `valgrind --tool=callgrind` with no toggle: the whole build, for the
     build total and for the inclusive cost of the functions around
     `type_structure` (1.4). The inclusive cost of `type_structure` in
     this run is 26,713 M on the application against 26,698 M counted by
     the toggle: the two agree to 0.06%.
- Attribution is per instruction address. Every address of the executable
  is resolved to its stack of inlined frames (`llvm-symbolizer --inlines`).
  An address belongs to the **item** of the innermost frame that an item
  rule matches (a rule is a file pattern and a function-name pattern; the
  rules are the first table of
  [classify.py](prototypes/checker-attribution/classify.py)). An address
  no rule matches (library code, the node store's accessors, `memcpy`,
  hashing, drop glue) inherits the item of the call sites that reach its
  function, in proportion to the inclusive cost of each call, iterated over
  the call graph to a fixed point. 34.4% of the application's checker
  instructions are assigned by that proportional rule, 65.6% by a frame.
- The allocator is its own item, as the task's list has it: the code of
  mimalloc and the `memcpy` it calls when a `Vec` grows. A second run of
  the classifier (`--alloc-inherit`) charges it to its callers instead;
  1.3 shows both.
- Each address also has a **kind** of work, by the innermost frame that
  belongs to a mechanism: allocation, copying and dropping, reference
  counts, hashing and table probes, addressing a type node or a type list,
  `Cell` and `RefCell` bookkeeping, the mutation journal, or none of those
  ("own": the checking itself). Kinds do not inherit.
- Operation counts: `RESCRIPT_COMPILER_COUNTERS=1`, one worker, the same
  executable.
- Source lines: every physical `.res` and `.resi` file under the project,
  as `scripts/bench_project.py` counts them: 656,677 for the application.
- One run each. Callgrind's count of one executable moved by 0.05% between
  two runs of the test project (4,070.96 M and 4,072.95 M).
- The scripts are under
  [prototypes/checker-attribution](prototypes/checker-attribution)
  (measurement prototypes, not reviewed code): `cg.py` parses the profile
  and drives the symbolizer, `classify.py` holds the rules and prints the
  tables, `incl.py` prints inclusive costs.

### 1.2 The cost table

The checker is 26,698 M instructions on the application (39.4% of the
build's 67,739 M; 40,656 per source line) and 1,310 M on the test project
(32.2% of 4,073 M). Shares are of the checker. Items are closed: they add
up to the total, and nothing is left over.

| # | Item | Application, M | Share | Per line | Test project, M | Share | The functions that make it up (share of the application's checker) |
|---|---|---:|---:|---:|---:|---:|---|
| 1 | **Unification**: unifying two types, occurrence checks, the unified-pairs set, links | 4,574 | 17.1% | 6,966 | 186 | 14.2% | `ctype::unify_types` 2.30, `unify` 1.79, `binding_facts::walk` 1.67, `link_type` 1.42, `surely_occur_free` 0.82, `surely_univar_free` 0.71, `mark_unified` 0.70, `reaches_quick` 0.51, `already_unified` 0.30, `typecore::unify_expression_types` 0.32; under them `repr_chain` 0.56 |
| 2 | **The walk**: dispatch on the expression, expected-type handling, typed-node construction, attributes, locations, the typed environment table | 3,553 | 13.3% | 5,411 | 144 | 11.0% | `typecore::type_application_parts` 1.12, `type_expect_with_recarg_unscoped` 0.62, `TypeContext::store_typed_env` 0.45, `type_expect_full` 0.37, `type_record` 0.33, `type_function_nary` 0.31, `build_record_label_descriptions_info` 0.27, `extract_concrete_record_type_info` 0.22, `TypedArena::push_iter` 0.22, `with_exp_attributes` 0.20, `type_identifier` 0.19; `memcpy` under them 0.58 |
| 3 | **Environment lookups**: finding a value, type, module, constructor or label by name or by path; extending an environment | 3,467 | 13.0% | 5,279 | 119 | 9.1% | `env::IdTbl::get` 0.54, `typecore::lookup_type_decl_for_path_with_cache_mode` 0.48, `find_by_ident` 0.40, `recent_named` 0.37, `find_by_key_with_path` 0.35, `is_empty` 0.30, `open_slot_use_by_key` 0.27, `env_lazy::type_item` 0.26, `Env::clone` 0.24, `collect_all_key` 0.20, `with_resolved_module_components_for_path_with_cache_mode` 0.20; hashing under them 4.3 |
| 4 | **Instantiation**: copying the generic part of a type for one use | 2,850 | 10.7% | 4,341 | 134 | 10.2% | `ctype::copy_type_cached` 2.90, `new_type_list_from` 0.65, `instance` 0.59, `end_copy_session` 0.37, `begin_copy_session` 0.27, `new_type_args_from` 0.24; under them the copy cache (`TypeExprRefMap::insert` 0.48, `get` 0.34), `store_desc` 0.39, `page_node` 0.35, `alloc_type` 0.31 |
| 5 | **The allocator**: `malloc`, `free`, `realloc` and the copy a growing vector makes | 2,274 | 8.5% | 3,463 | 110 | 8.4% | `mi_theap_malloc_zero_aligned_at` 1.19, `mi_page_malloc_zero` 0.68, `mi_malloc_aligned` 0.43, `mi_free_ex` 0.20, the rest of mimalloc 4.2; `memcpy` called by it 1.79 |
| 6 | **Loading dependencies**: stored interfaces, module views, the world, the persistent environment | 1,968 | 7.4% | 2,996 | 105 | 8.0% | `world::ty` 0.26, `poison_store_build_for` 0.19, `persistent_env::cache_lookup_entry` 0.15, `outside_load_path` 0.15, `resolve_first_char_case_key` 0.15, `substitute_type_expr_path` 0.14, `materialize_expected` 0.09; `memset` under them 0.51, hashing 2.6 |
| 7 | **Expansion of abbreviations**: is this constructor an abbreviation, its memo, the substitution of its manifest | 1,624 | 6.1% | 2,474 | 66 | 5.0% | `ctype::try_expand_head_with_mode` 1.23, `TypeContext::read_abbrev` 0.73, `expand_head_with_mode` 0.72, `with_abbrev` 0.67, `alloc_abbrev` 0.53, `find_abbrev_repr` 0.53, `proper_abbrevs` 0.23, `scan_abbrev_chain` 0.14 |
| 8 | **Levels and generalisation** | 1,341 | 5.0% | 2,042 | 65 | 4.9% | `ctype::lower_plain_levels::lower` 1.27, `update_level_checked` 0.64, `generalize_rec` 0.34, `lower_args` 0.25, `update_level_checked_above` 0.16, `update_level_children` 0.14, `begin_def` and `end_def` 0.20 |
| 9 | **Substitution copies**: the copy of a looked-up item or a signature under a path substitution, path rewriting | 1,009 | 3.8% | 1,537 | 130 | 9.9% | `typecore::copy_lookup_type_expr_with_paths` 0.46, `ctype::subst_identity_copy_rec` 0.13, `nondep_type_rec` 0.06, `typemod::rewrite_type_paths_in_place` 0.06, `record_label_param_subst` 0.06; under them the copy map 0.36, `store_desc` 0.13 |
| 10 | **Patterns and exhaustiveness** | 971 | 3.6% | 1,478 | 65 | 4.9% | `parmatch::le_pat` 0.31, `typecore::type_pattern_inner` 0.19, `parmatch::Desc::clone` 0.18, `filter_all` 0.17, `records_args` 0.17, `type_pattern_construct` 0.09, `enter_variable` 0.09 |
| 11 | **Warnings and usage marking** | 907 | 3.4% | 1,382 | 22 | 1.7% | `typecore::mark_open_lid_use` 0.39, `usage::mark_value_used` 0.16, `mark_module_lid_used` 0.12, `mark_type_used` 0.08, `diagnostics::{parse_opt, is_active}` 0.17, `check_value_usage` 0.05; hashing under them 1.3 |
| 12 | **The mutation journal**: a snapshot around every top-level unification and the log of writes made under it | 874 | 3.3% | 1,331 | 45 | 3.4% | `TypeContext::snapshot_type_state_with` 1.04, `TypeMutationJournal::finish` 0.57, `TypeMutationSnapshot::drop` 0.51, `record_type_mutation` 0.46, `set_level_as_under_new_snapshot` 0.30 |
| 13 | **Type and value declarations** | 668 | 2.5% | 1,017 | 61 | 4.7% | `decl::*::clone` 0.46, `predef::is_predef_type_ident` 0.18, `decl::same_constructor` 0.05, `ctype::compute_variance_rec` 0.04, `decl_loc::*` 0.10; `memcmp` under them 0.24 |
| 14 | **Modules, signatures, inclusion** | 304 | 1.1% | 462 | 46 | 3.5% | `typemod::type_structure_item` 0.11, `with_warning_scope` 0.04, `includemod::*` |
| 15 | **Disambiguation** of constructors and labels | 242 | 0.9% | 369 | 8 | 0.6% | `typecore::lookup_label_by_expected_type` 0.17, `disambiguate_constructor` 0.08, `disambiguate_label` 0.05, `env::find_all_labels` 0.03 |
| 16 | **Type annotations** in source | 64 | 0.2% | 98 | 6 | 0.5% | `typecore::transl_type_inner` 0.09 |
| 17 | **Error-path preparation** that is not the journal | 9 | 0.03% | 14 | 0.5 | 0.04% | `typecore::type_clash_context_for_function_argument` 0.03 |
| | Other | 0 | 0.0% | 0 | 0 | 0.0% | |
| | **Sum** | 26,698 | 100% | 40,656 | 1,310 | 100% | |

Three remarks on what the rows hide.

- Row 12 is error-path preparation paid on the success path. The snapshot
  that `unify` opens at its top level exists so that a *failed* unification
  can undo path compression before the trace is expanded
  (`compiler/ml/ctype.ml`, the outer `unify`). 3,997,259 snapshots are
  opened on the application and 36,012 are ever restored (0.9%).
  In OCaml a snapshot is a counter; here it is 219 instructions and every
  write under it is logged.
- Row 1 contains 3.9% of the checker in four functions that answer one
  question, "does this variable occur in that type" (`binding_facts::walk`,
  `surely_occur_free`, `surely_univar_free`, `reaches_quick`), and 1.0% in
  a hash set of pairs (`mark_unified`, `already_unified`) that OCaml does
  not have.
- Rows 3, 6 and 9 are one subject, names: 24.1% of the checker on the
  application, 27.0% on the test project.

### 1.3 The same instructions by kind of work

Application, share of the checker. The last column charges the allocator to
the item that called it.

| Item | Allocation | Copy, drop | Ref counts | Hashing | Node and list addressing | `Cell`, `RefCell` | Journal | Own | All | With its allocator calls |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Unification | 0.13 | 1.39 | 0.48 | 1.41 | 4.46 | 1.84 | | 7.42 | 17.13 | 17.45 |
| The walk | 0.56 | 2.88 | 0.18 | 0.91 | 0.86 | 0.24 | | 7.68 | 13.31 | 16.04 |
| Environment lookups | 0.21 | 1.76 | 0.49 | 4.34 | 0.25 | 0.18 | | 5.75 | 12.98 | 14.37 |
| Instantiation | 0.08 | 1.37 | 0.21 | 1.59 | 3.04 | 0.49 | | 3.89 | 10.68 | 10.82 |
| The allocator | 6.71 | 1.80 | | | | | | | 8.52 | |
| Loading dependencies | 0.10 | 1.49 | 0.24 | 2.62 | 0.60 | 0.10 | 0.03 | 2.19 | 7.37 | 8.01 |
| Expansion | 0.18 | 0.62 | 0.10 | 0.12 | 0.74 | 0.73 | | 3.59 | 6.08 | 6.69 |
| Levels | 0.04 | 0.95 | 0.15 | 0.07 | 1.49 | 0.52 | | 1.80 | 5.02 | 5.10 |
| Substitution copies | 0.03 | 0.49 | 0.08 | 1.08 | 0.96 | 0.12 | | 1.01 | 3.78 | 4.02 |
| Patterns | 0.25 | 0.86 | 0.04 | 0.12 | 0.03 | 0.02 | | 2.32 | 3.64 | 4.65 |
| Warnings | 0.06 | 0.31 | 0.01 | 1.28 | 0.20 | 0.06 | | 1.47 | 3.40 | 3.65 |
| The journal | 0.03 | 0.62 | 0.01 | | 0.34 | 0.32 | 1.92 | 0.02 | 3.27 | 3.28 |
| Declarations | 0.17 | 0.95 | 0.08 | 0.59 | 0.03 | 0.02 | | 0.68 | 2.50 | 3.04 |
| Modules | 0.07 | 0.27 | 0.02 | 0.34 | 0.01 | 0.01 | | 0.41 | 1.14 | 1.49 |
| Disambiguation | 0.02 | 0.20 | 0.02 | 0.15 | 0.06 | 0.01 | | 0.45 | 0.91 | 1.08 |
| Annotations, error preparation | 0.02 | 0.05 | | 0.02 | 0.01 | | | 0.16 | 0.27 | 0.32 |
| **All** | **8.67** | **16.01** | **2.12** | **14.65** | **13.08** | **4.67** | **1.95** | **38.84** | **100** | **100** |

61% of the checker is not checking. The test project has the same shape
(allocation 9.1, copies 16.2, reference counts 2.1, hashing 15.4, addressing
12.4, cells 4.3, journal 2.0, own 38.5).

Against CHECKER_REDESIGN K.2, measured before the slices C1 to C3 and W2
merged: node and list addressing with cells and journal was 32.0% of the
checker and is 19.7%; the checker was 31.20 G of 74.21 G and is 26.70 G of
67.74 G. The checker's share of the build went from 42.0% to 39.4%.

### 1.4 What surrounds `type_structure`

Inclusive costs from the untoggled profile. These are not in the table of
1.2; the budget of section 7 counts them.

| Work | Function | Application, M | Of the build | Test project, M | Of the build |
|---|---|---:|---:|---:|---:|
| Checking implementations | `typemod::type_structure` | 26,713 | 39.44% | 1,310 | 32.15% |
| Checking interfaces | `driver::typecheck_preprocessed_signature_in_process` | 475 | 0.70% | 76 | 1.87% |
| Implementation against its interface | `includemod::compunit_with_warnings` | 423 | 0.62% | 114 | 2.79% |
| Publishing the signature | `driver::publish_signature` | 906 | 1.34% | 128 | 3.14% |
| Per-module setup | `driver::in_process_type_check_context` | 260 | 0.38% | 40 | 0.98% |
| Per-module teardown | drop glue of `TypeContext`, `TypeCheckContext`, `TypedArena` | 788 | 1.16% | 46 | 1.12% |
| **The checker with its surroundings** | | **29,565** | **43.6%** | **1,714** | **42.1%** |
| Unit reads, a second walk of the typed tree | `unit_reads::structure_reads` | 1,712 | 2.53% | 45 | 1.11% |
| **With the unit reads** | | **31,277** | **46.2%** | **1,759** | **43.2%** |

Per source line of the application: 40,656 for `type_structure`, 45,022
with its surroundings, 47,629 with the unit reads. The budget is 18,000 to
22,000. So the checker and what surrounds it must lose 51% to 60% of their
instructions.

### 1.5 What one operation costs today

Application, one worker. Counts from the compiler counters; instructions
from 1.2.

| Operation | Count | Per source line | Instructions of its item | Per operation |
|---|---:|---:|---:|---:|
| `instance` calls | 5,426,224 | 8.3 | 2,850 M | 525 a call |
| nodes those calls copy | 4,817,581 | 7.3 | | 592 a copied node |
| top-level unifications | 3,866,475 | 5.9 | 4,574 M + 874 M journal | 1,409 a unification |
| of which the two sides are already one node | 1,192,030 | 1.8 | | |
| of which two identical variable-free types | 877,885 | 1.3 | | |
| of which a variable against a variable-free type | 967,464 | 1.5 | | |
| snapshots opened / restored | 3,997,259 / 36,012 | 6.1 | 874 M | 219 a snapshot |
| nodes visited by level updates and generalisation | 4,204,961 | 6.4 | 1,341 M | 319 a node |
| type nodes created | 10,286,886 | 15.7 | | |
| of which by `instance` | 4,898,740 | | | |
| of which by lookup copies (substitution) | 1,976,499 | | 1,009 M | 511 a node |
| of which fresh variables | 1,827,770 | | | |
| fresh variables made only to be an expected type | 369,643 | 0.6 | | |
| descriptor reads of frozen (dependency) nodes | 23,968,453 | 36.5 | | |

These are the numbers section 2 argues from. A copy of a node is a load, a
test and a store; it costs 592 instructions. A unification of two types
that are already the same node costs a snapshot. That is the gap a design
can close without touching what is observable.
