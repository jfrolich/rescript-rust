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

Short version:

- The checker is 40,656 instructions per source line of a 3,735-module
  application (45,022 with publication, interfaces, setup and teardown),
  39% of a build. 61% of it is not checking: allocation, copying, hashing,
  addressing nodes, cells, a journal. Names (lookups, loading
  dependencies, substitution copies) are 24%, unification with its journal
  20%, the walk 13%, instantiation 11% (section 1).
- The identity of type nodes stays observable and the design keeps it. It
  changes what every operation on the graph costs: 16-byte nodes in one
  array, schemes as templates, binders as indices and names resolved once,
  rows instead of a typed tree, nothing kept for an error that does not
  happen (sections 2 and 3).
- Two prototypes on trunk, both with identical output on both projects.
  Unification without a journal on the success path: predicted 2.1% to
  2.4% of the checker, measured 2.2% and 2.1%. Instantiation from
  templates: predicted 4% to 5%, measured 0.6% and 0.9%; the cost is
  creating nodes in today's storage, not the copy (section 4).
- The design reaches about 14,200 instructions per line on its own
  figures and about 22,500 when every unconfirmed figure is doubled; the
  budget is 18,000 to 22,000. 4% of that reduction is measured in a
  checker, the rest on a stand-alone kernel or estimated (section 7).
- It is built beside the old checker, a unit at a time behind one switch,
  in slices R0 to R10 with two hard measurement gates; the last slices
  delete the old checker's files and the switch (sections 5 and 6).

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
- Row 1 contains 3.7% of the checker in four functions that answer one
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

## 2. What a design that owes nothing to today's code would pay

### 2.1 What is observable

CHECKER_REDESIGN I.2 and I.3.3 found that the identity of type nodes is
observable. This is the complete list this document works from: each
observation, the fixture that shows it, and whether a representation has to
**store** something for it or whether it **follows** from stored facts.
Fixtures are under `tests/build_tests/super_errors/fixtures/` unless a path
is given; all exist on trunk except where "to add" is written.

| # | Observation | Fixture | Stored or follows |
|---|---|---|---|
| O1 | The name a type is printed with is the path in its representative node. The printer, genType, the stored interface and the immediacy test of the backend expand nothing | `alias_name_follows_unification.res` | **stored**: a path in every constructor node |
| O2 | A link changes which node a handle resolves to, in a fixed direction: a variable becomes the other node; a plain node becomes the *unexpanded* abbreviation node; of two abbreviations the first link names the node | `checker_identity_10_abbreviations.res`, `checker_identity_11_arrow_tuple.res` | **stored**: links between nodes, written in the direction of CHECKER_REDESIGN I.2.1's table |
| O3 | Every use of a binding that was not generalised is the same node | `alias_name_follows_unification.res`, `checker_identity_04_local.res`, `checker_identity_05_weak.res` | follows from O10: `instance` returns a node that is not generic |
| O4 | Every use of a generalised binding, of a record field, of a constructor is its own copy | `checker_identity_02_annotated.res`, `checker_identity_03_generalized.res`, `checker_identity_06_field.res` | follows from O10: `instance` copies a generic node |
| O5 | Two positions of one scheme that are one node are one node in every instance | `checker_identity_07b_sharing.res` | **stored**: a scheme is a graph, not a tree. A template (2.3, item 4) keeps it with relative references |
| O6 | A link can land on a node inside the type of another binding | `checker_identity_07_tuple.res` | follows from O2: there is no name per binding, only per node |
| O7 | Names and sharing cross a module boundary | `tests/build_tests/super_errors_multi/fixtures/checker_identity_08/`, `tests/gentype_tests/typescript-react-example/src/CheckerIdentity08A.res` | **stored** in the published signature: the representative's descriptor, and one stored node per node of the exporter inside each item |
| O8 | The JavaScript of a comparison depends on the name: `a > Green` is `Primitive_object.greaterthan` after `a`'s node was linked to `id<color>` | `checker_identity_comparison.res` | follows from O1 |
| O9 | An abbreviation with a phantom parameter turns a ground occurrence into a type with a variable; the check for weak variables expands first | `checker_identity_09_phantom.res`, `checker_identity_09b_weak_phantom.res` | follows from O2 and from expansion |
| O10 | Whether a node is generic decides copy or share, per node, for structure nodes as for variables. It is set by `generalize` (every node above the current level) and by `generalize_structure` (annotations, patterns that are not a plain variable) | `checker_identity_02_annotated.res` against `alias_name_follows_unification.res` | **stored**: a level in every node |
| O11 | A copy of a nullary constructor links to the node whose expansion is memoised, while that memo lives (`find_repr` in `Ctype.copy`, `compiler/ml/ctype.ml`; `copy_type_cached` in Rust) | R0 found no isolating program in the five shapes tested below | **stored** if observable: the simple-abbreviation memo |
| O12 | Lowering a level can fail (a type constructor would escape its scope) and can expand an abbreviation to avoid that, which renames | `weak_variable_escapes_later_type.res`, `gadt_existential_escape.res` | follows from O10 with the scope of each path; the walk must run where OCaml's runs |
| O13 | Programs with a cyclic type are rejected | `occurs_check_function_type.res`, `occurs_check_large_type.res`, `occurs_check_through_constructor.res` | follows: a check, not a state |
| O14 | Weak variables: a variable that is not generalised stays one node for the rest of the unit; one left at the end is an error | `non_generalizable.res`, `identity_does_not_generalize.res` | follows from O10 |
| O15 | Diagnostics come in the order the checker meets them, and the warnings met before the first error are printed before it | `fun_return_poly1.res`, `unused_warnings.res` | **order of work**: a lookup-time warning is raised when the walk reaches the use, not before |
| O16 | A type clash prints the two types as they stood when unification failed, with the trace expanded | every `type clash` fixture, e.g. `checker_identity_02_annotated.res` | **failure path only** (2.4, idea 8) |
| O17 | The names of type variables in printed types (`'a`, `'b`, weak `_a`) follow the order the printer meets them and the names variables carry | `fun_return_poly2.res` | **stored**: the name in a variable node; `link_type`'s rule for which name survives |
| O18 | The output does not depend on worker count or scheduling | `scripts/test_worker_determinism.py` | **order of work**: nothing shared is written in an order that depends on scheduling |

**O11 experiment (R0).** No tested program isolated the rule. The reference
OCaml compiler was built with OCaml 5.5.1 and compared with a separate build
changing only `compiler/ml/ctype.ml:781`: `find_repr p !abbrevs` becomes
`if tl = [] then None else find_repr p !abbrevs` in `copy`. Both were run
with `-nopervasives -bs-no-version-header -I .`, with a 10-second timeout
per invocation. The common declarations were `type a = int`, `type b = int`,
`external forceInt: int => int = "%identity"`, and
`let id = (x: a) => x`. These five shapes were tried:

- Two instantiations with expansion between them:
  `let observed = (id, forceInt(id(1)), id)`.
- Through a record field: `type box = {value: a => a}` and
  `let record = {value: id}`, then
  `(record.value, forceInt(record.value(1)), record.value)`.
- Through a constructor argument: `type box = Box(a => a)`,
  `let unwrap = x => switch x { | Box(f) => f }`, `let value = Box(id)`,
  then `(unwrap(value), forceInt(unwrap(value)(1)), unwrap(value))`.
- Across two units: compile the common declarations in `A.res`, then
  `(A.id, forceInt(A.id(1)), A.id)` in the consumer, loading that build's
  own `A.cmi` and `A.cmj`.
- A later unification that could print a different name:
  `(id, forceInt(id(1)), (id: b => b), id)`.

Each was compiled both as an accepted program and with
`let _: string = observed` appended. All five accepted programs produced
identical JavaScript; all five forced clashes produced identical diagnostics
(text and locations). The last clash printed
`(a => a, int, b => b, a => a)` in both builds; the cross-unit clash printed
`(A.a => A.a, int, A.a => A.a)`. This is a negative experiment, not a proof
that the rule is unobservable: O11 remains a constraint pending an isolating
program or an explicit decision to drop it.

What a representation is therefore free to change: where a node is stored
and how large it is; how a copy is made; how a descriptor is found; whether
a snapshot exists when nothing fails; how names are looked up; the typed
tree; the order of work inside a unit wherever O15 does not see it.

What it is not free to change: one node per occurrence (O2, O6), a level on
every node (O10, O12), a path in every constructor node (O1), sharing
inside a scheme (O5, O7). This is CHECKER_REDESIGN I.3.3 rules 1 to 8, and
this document does not reopen them: the design of section 3 keeps the
graph and changes the price of every operation on it.

### 2.2 The price of one operation, measured on a kernel

Before item by item: what does the graph of 2.1 cost when nothing else is
in the way? [The kernel](prototypes/checker-kernel/src/main.rs) is a
stand-alone program of 520 lines with eight tests (measurement probe, not
compiler code): a
16-byte node (tag and arity, level, two words), one `Vec` of nodes and one
of list slots, templates with relative references, unification with
links in the specified direction and levels written on every node, the
occurrence check and the level update of a binding in one walk,
generalisation from the root, scopes as a dense table from interned name to
binding with an undo log. No journal unless a speculation is open.

Method: `valgrind --tool=cachegrind`, each operation 1,000,000 times, a run
of zero iterations subtracted, the empty loop (18 instructions) subtracted;
where an operation needs fresh nodes, the run that only makes them is
subtracted (`measure.sh`). Release profile, fat LTO.

| Operation | Instructions | Today, for comparison (1.5) |
|---|---:|---|
| `instance` of a scheme of 1 node (`int`) | 89 | 525 a call, 0.89 nodes a call |
| of 3 nodes (`option<array<int>>`) | 169 | |
| of 5 nodes (`(string, int) => option<string>`) | 221 | |
| of 7 nodes (`(array<'a>, 'a => 'b) => array<'b>`) | 250 | |
| so: per call, and per node with its list slot | 62 + 27 a node | 592 a copied node |
| unify two types that are one node | 26 | at least 219 (the snapshot) |
| unify `int` with `int` (two nodes, one link) | 118 | 1,409 a top-level unification, all shapes |
| unify two `option<array<int>>` | 386 (129 a pair of nodes) | |
| unify two `(string, int) => option<string>` | 631 (126 a pair) | |
| bind a fresh variable to `option<array<int>>`: occurrence check, levels, link | 300 | |
| generalise a 7-node type | 404 (58 a node) | 319 a visited node |
| a whole application `xs->Array.map(f)`: instance of the 7-node scheme, two argument types built, two unifications | 1,220 | |
| look up a name in the current scope | 5 | 299 (H.2.11: 603 M for 2,017,342 lookups) |
| look up a binder by its index | 5 | 105 (H.2.11: 684 M for 6,487,233) |
| bind a name and undo it at scope exit | 44 | 932 (H.2.11: 246 M for 263,680 value bindings) |

The H.2.11 figures are quoted from CHECKER_REDESIGN (trunk `da56e056f`,
measured there with `#[inline(never)]` entry points).

Two things the kernel says. A node pair costs about 125 instructions to
unify and a node 27 to copy even when nothing is in the way: the pencil
figure of "a load, a test and a store" is wrong by a factor of five, and
the numbers below use the kernel's, not the pencil's. And today's
operations cost four to thirty times the kernel's.

What the kernel does not have, and what every number extrapolated from it
therefore lacks: abbreviations (it fails on one), rows, objects and
universal variables, the scope test of a level update (O12), the two tiers
of handles, variable names. Section 2.3 adds 40% to 50% to a kernel figure
for these and says so each time.

### 2.3 Item by item

Per source line of the application. "Today" is 1.2. Every item above 2% of
the checker has a mechanism and a number; the label says what the number
rests on. Section 7 collects them.

**1 and 12. Unification and the journal: 8,297 today (6,966 + 1,331).**

- *No snapshot for a unification that succeeds.* The top-level snapshot
  serves one purpose, undoing path compression before a failed
  unification's trace is printed (O16). The design takes none: a failure
  makes the unit be checked again in the explaining mode (2.4, idea 8).
  Writes are logged only inside a speculation (36,012 restores on the
  application against 3,997,259 snapshots). Prototyped: section 4.2.
- *No set of unified pairs on the paths that link.* `mark_unified` and
  `already_unified` (1.0% of the checker) guard against cycles. A pair that
  is linked before its children are unified (variable, arrow, tuple,
  constructor that is not an abbreviation) is found again as one node. The
  set is needed where nothing is linked: two abbreviations, rows, objects.
- *One walk when a variable is bound.* Today a binding walks the type up to
  four times (`binding_facts::walk`, `surely_occur_free`,
  `surely_univar_free`, then `lower_plain_levels`): 3.7% of the checker
  before the level update. One walk answers all of it, and a subtree whose
  root is below the variable's level is skipped for the occurrence check
  (a node's level is never below its children's, so the variable cannot be
  inside), exactly as the level update already skips it.
- *The expected type is not a variable.* 369,643 fresh variables (20% of
  all) still exist only to be unified with what an expression turns out to
  have; 350,692 of them are made by `type_application`. In the design a
  construct either checks against a known type or returns the type it
  found (2.4, idea 1).
- *Descriptors without cells.* 4.46% of the checker is addressing nodes
  under unification and 1.84% `Cell` and `RefCell` flags. A node is 16
  bytes in one `Vec`; a read is an indexed load.

Number: the application's 3,866,475 top-level unifications by shape (1.5),
priced with the kernel: 1,192,030 same-node at 26; 877,885 identical
variable-free at 260 (two pairs of nodes assumed); 967,464 variable against
variable-free at 300; 240,836 variable against variable at 120; 152,334
variable against a type with variables at 400; 390,023 structure against
structure at 500; 45,903 different variable-free types, which is the
expansion road, at 900. Sum 876 M, **1,330 a line**; with 45% for what the
kernel lacks, **1,930**. *Extrapolated from the kernel; the sizes (pairs
per unification) are assumed, not counted.* The journal part, 1,331 today,
is *measured* by the prototype (4.2).

**2. The walk: 5,411 today, 6,521 with its allocator calls.**

- 7.68% of the checker is the walk's own work: dispatch on the expression,
  the cases. That stays, on a flat syntax tree with handles.
- 2.88% is copies and drops, 0.56% allocation, 2.73% the allocator under
  it, 0.91% hashing: owned vectors of arguments, `Arc` descriptions stored
  in 72-byte typed nodes, the environment snapshot stored per node
  (`store_typed_env`, 0.45%), attribute vectors. The design writes one
  12-byte row per expression into a table indexed by the syntax node
  (THREE_TREES T8) and no typed tree; a value passed down the walk is 16
  bytes; lists go to the arena's pools.

Number: CHECKER_REDESIGN K.4 *measured* that rewriting the application
family this way removed 54% of its allocation and copying. Applied to the
walk's 7.1% of non-own work (with the allocator): 3.8% of the checker,
1,560 a line, leaving 4,960. A flat dispatch without owned intermediate
values is *estimated* to take another 25% of the own part (780). **About
4,200.** *Extrapolated from K.4 for the first part, estimated for the
second.* THREE_TREES section 6 measured typed-tree construction and
destruction at 1.28% of a build as a floor.

**3, 6 and 9. Names: environment lookups 5,279, loading dependencies 2,996,
substitution copies 1,537; 9,812 today, 10,750 with their allocator
calls.**

- *A binder is an index.* Every value, type, module, constructor and label
  bound in a unit gets a dense binder index when it is bound. What the
  checker knows about it lives in arrays indexed by it. 6,487,233 of the
  application's 9,025,904 lookups are by identifier (H.2.11): each becomes
  an indexed load.
- *A name is looked up once.* The current scope is a dense table from
  interned name to the innermost binder, with an undo log, for each of the
  five namespaces. An opened module is one layer: a frozen table from name
  to item. A lookup probes the dense table, then the open layers that are
  younger than what it found (two on average on the application is
  *assumed*). The result is written in the row of the syntax node, so the
  backend, genType and tooling never look a name up again.
- *An environment is two integers.* What a typed node, a closure or a
  delayed check keeps of "the environment here" is a scope index and a
  binder watermark. No table is cloned (1,640,668 clones today), no
  identity is compared by walking (19,948,094 identity and scope queries
  today). H.2.11 measured a binding *log* at 1.9 times the cost of today's
  tables, because it kept environments as first-class versioned values and
  every read resolved a version. The design has no versions: a lookup by
  name happens at the current scope during the walk and nowhere else.
- *A dependency's item is read, not copied.* A path `M.x` resolves to a
  unit, then to an item of its frozen export table (section 3): the type is
  a template in the unit's segment with absolute paths. There is no
  substitution on lookup, no per-worker view, no store build, no replay.
  Substitution remains for `include`, functor application and module type
  instantiation (CHECKER_REDESIGN B.6).

Number: H.2.11's operation counts priced with the kernel and a factor of
two for layers and namespaces: 2,017,342 lookups by name at 60; 6,487,233
by identifier at 10; 521,329 by path at 80; 453,619 bindings at 90;
19,948,094 identity and scope queries at 2; 12,001,915 flag queries at 4;
1,000,905 open-slot marks at 20. Sum 377 M, 570 a line, for environment
lookups; loading and substitution are *estimated* at 600 and 250 from
CHECKER_REDESIGN J.6 (what stays is reading a unit's table once per unit
and the `include` copies). **About 1,450, against 9,812.** *Extrapolated
from the kernel for lookups, estimated for the rest. This is the least
certain large number in the document: nothing of it is prototyped, and the
one earlier attempt at a different environment structure measured worse.*

**4. Instantiation: 4,341 today.**

- A scheme's generic part is a *template*: its nodes in the order the copy
  allocates them, child references relative to the template's first node or
  absolute to a node that is not generic. An instance is one pass that
  copies nodes and list slots and adds an offset: no copy session, no map
  from node to copy, no recursion, no placeholder written twice, no memo
  cell allocated per constructor. Sharing inside the scheme (O5) is the
  relative reference. A node that is not generic is referenced and not
  copied (O3). The identifiers and the order of the copies are those of
  `Ctype.copy`.
- A dependency's item is stored as a template when it is published. A local
  scheme gets one the second time it is instantiated.

Number: 5,426,224 calls and 4,817,581 copied nodes. CHECKER_REDESIGN I.3.1
counted that 63% of variable-free instantiations copy nothing because the
root is not generic; with that share for all calls, 2.0 M calls copy and
3.4 M return at once. 3.4 M at 8, 2.0 M at 62, 4.82 M nodes at 27: 281 M,
430 a line; with 40% for what the kernel lacks, **600**. *Extrapolated from
the kernel. The prototype (4.1) measured this mechanism inside today's
checker and contradicts the first prediction made from it; 4.1 has both
numbers and section 7 uses the corrected one.*

**5. The allocator: 3,463 today.** No call in a walk: nodes, lists, rows
and patterns go to pools that are reset per unit. What remains is pool
growth and the per-unit tables. **500**, *estimated* at 15% of today.

**7. Expansion of abbreviations: 2,474 today.** Whether a constructor is an
abbreviation is one bit in the declaration row its type index names; today
it is a declaration lookup by path and a walk of a memo chain behind two
`RefCell`s (`read_abbrev`, `with_abbrev`, `alloc_abbrev`, `find_abbrev_repr`:
2.5% of the checker). The memo is a slot in the constructor's argument
list; a cell is made when an expansion is memoised, not for every copied
constructor. The expansion itself is an instance of the declaration's
template with the parameters bound to the arguments (62 + 27 a node).
**800**, *estimated*: the number of expansions was not counted.

**8. Levels and generalisation: 2,042 today.** 4,204,961 visited nodes at
the kernel's 58, with 45%: 354 M, 540 a line. `begin_def` and `end_def`
are an increment and a decrement. **550.** *Extrapolated from the kernel.*

**10. Patterns and exhaustiveness: 1,478 today.** Typing a pattern is the
walk again. The exhaustiveness check works on matrices of patterns; 1.3%
of the checker in it is cloning and dropping pattern descriptions and the
allocator. Rows of handles into a pattern pool instead of owned
descriptions. **1,000**, *estimated*.

**11. Warnings and usage: 1,382 today.** A use sets a bit in an array
indexed by binder; today it hashes a location or a path (1.28% of the
checker is hashing here). Whether a warning is active is a bit set read
once per unit, not parsed per query. **400**, *estimated*.

**13. Declarations: 1,017 today.** 0.46% of the checker clones
declarations. A declaration is a row; a reader takes its index. **700**,
*estimated*.

Items under 2% (modules 462, disambiguation 369, annotations 98, error
preparation 14) are carried at 80% of today's cost: 750.

### 2.4 The ideas, one by one

**1. Checking against a known type without creating and unifying variables:
adopted in a changed form.**

Adopted: a construct is called in one of two modes, *check against this
node* or *infer and return a node*, and no variable is made to carry a
result. That removes the 369,643 expected-type variables and their
bindings.

Not adopted: skipping the instance of a constructor, a label or a function
type when the expected type is known, and reading the argument types off
the expected type instead. It is tempting because the copy is "absorbed":
`unify(copy, expected)` links every copied node to a node of the expected
type. It is not always absorbed. The program that breaks it:

```rescript
type myint = int
type box<'a> = {value: 'a, count: myint}
let f = (b: box<string>) => b.count
let g = n => { let b: box<string> = {value: "", count: n}; (n, b) }
```

Typing the record against `box<string>` instantiates the label `count` at
`myint` and unifies that copy with `n`'s node. `n`'s node, a variable,
links to the *copy* of `myint`: the copy survives as the representative and
`g` is printed `myint => (myint, box<string>)` (compiled with trunk for
this document, with a type clash forced on `g`). A check that read the field
type "from the expected type" has no node to give `n`. So the rule is: the
copy of a declaration's node may be skipped only where the unifier's table
(CHECKER_REDESIGN I.2.1) says the copy would be linked *away*, and that
depends on the other side, which is only known when the argument has been
typed. The design therefore instantiates as OCaml does (the template makes
it 62 + 27 a node) and does not fuse instantiation with checking. What it
would buy if it were sound everywhere is bounded by item 4: 600 a line.

**2. Union-find with ranks instead of level walks; generalisation by
regions: rejected, with one part adopted.**

- Ranks on representatives work for variables. They do not work for
  structure nodes, whose level is observable one by one (O10): `(a: int)`
  generalises the structure of the annotation, and `takesMyInt(a)` then
  renames a copy, not the parameter
  (`checker_identity_02_annotated.res`); a plain parameter is renamed
  (`alias_name_follows_unification.res`). A level per equivalence class
  cannot tell the annotation's nodes from the parameter's.
- Regions: generalising a binding by scanning the nodes allocated since
  its `begin_def` visits every young node. Generalisation from the root
  visits 838,695 nodes on the application; 10,286,886 are created. A scan
  would visit twelve times as many nodes, and would make generic the nodes
  of sub-expressions that OCaml leaves at their level.
- Adopted: the level update of a binding and its occurrence check are one
  walk that stops at the first node at or below the target level (item 1).

**3. Ground and closed types that are never copied, with the identity
carried where it is observed: rejected for the checker, adopted for the
world.**

Rejected: CHECKER_REDESIGN I.3.1 stands. Identity is observed at every
node (O6: `checker_identity_07_tuple.res`), so "carried where it is
observed" is a node. Its lazy form (one cell per occurrence, copied a
level at a time when something takes its children) was bounded there at
0.9% of the build, because 84% of the copied nodes are the root or its
children, which the next operation opens. The kernel changes the argument's
other half: a copied node costs 27 instructions, not 592, so there is
little left to avoid.

Adopted: a published item is never copied *into a worker*. It is frozen,
read in place by every compilation, and instantiated straight from the
frozen template into the unit's nodes.

**4. Environments as indexed scopes with resolved references cached per
syntax node: adopted.** Item 3 above.

**5. Resolving names once before typing: adopted in a changed form.**

A separate pass that resolves every identifier before typing breaks two
observations.

- O15. A deprecation warning or an unused-open mark is raised when a name
  is looked up. With a resolution pass, all of a unit's lookup warnings
  exist before the first type error; OCaml prints only those met before it
  (`fun_return_poly1.res` has a warning before an error). The order of the
  walk is not the order of the source: arguments, bindings and cases are
  typed in OCaml's order.
- Labels and constructors are resolved by the expected type
  (`disambiguate`), which a pass before typing does not have.

Changed form: *declarations* are resolved when their item is entered (the
binder indices exist before any body is typed), and a *use* is resolved
when the walk reaches it, once, with the result stored in the node's row.
The cost is the same single lookup; only its moment is the walk's.

**6. Typing declarations and bodies as separate passes, bodies in any
order and in parallel within a module: rejected.**

- It buys no instruction. The budget is instructions per line; parallel
  bodies would move wall time on large units only, and units are already
  checked in parallel.
- It is not sound in any order. `checker_identity_05_weak.res`:
  `let r = ref(None)` leaves a weak variable, a later item's `r := Some(x)`
  fixes it, and items after that see `ref<option<int>>`. The type of an
  earlier item changes while later bodies are checked, so bodies have an
  order whenever a weak variable is alive; and a `let` without annotation
  has no declared type for a later body to check against: its type *is*
  the result of checking its body.
- What the design keeps of it: type declarations of a recursive group are
  entered before their bodies, as OCaml does, and nothing in the data
  structures prevents checking independent items on a second core later
  (binder indices and rows are per item).

**7. Result tables instead of a typed tree (THREE_TREES T8 to T10):
adopted.** The checker writes tables indexed by syntax node and a pattern
pool; it builds no typed tree. Section 3 gives the rows. The condition
THREE_TREES states holds: editor tooling needs a tree until it is ported,
and gets one from a bridge that is deleted with the last reader (section
5).

**8. Diagnostics built only on the failure path, by re-running the failing
item in a slow, explaining mode: adopted, with the unit as the item.**

The success path keeps nothing whose only reader is an error message: no
snapshot per unification, no trace, no clash context, no expansion of a
trace. When a unit has a type error, the unit is checked again from its
first item in the explaining mode, which does keep them, and the
diagnostics are that run's. The unit and not the item, because the state a
message prints (O16) includes links made by earlier items of the same unit
(weak variables, O14) and because the warnings before the error (O15) are
those of the whole run up to it. A failing unit costs one more check; the
application has none, the test project has none, and an edit-compile loop
has one failing unit at a time.

Two conditions make it sound.

- The success path must fail *whenever* the explaining mode would report
  an error, at any point: it may be less precise about where and why, not
  about whether.
- A failure that the checker itself catches and recovers from (a
  speculative unification) is not a failure of the unit. Those run under a
  snapshot in both modes; the success path differs only when no snapshot
  is open.

The prototype of 4.2 is this mechanism on today's checker: the application
and the test project compile with no unit checked twice.

## 3. The design

### 3.1 One page

**Types are a graph in one array.** A type node is 16 bytes: tag and arity,
level, two words. A unit's nodes are one `Vec`, cleared when the unit is
done. A handle is 4 bytes with one tier bit: a node of this unit, or a
frozen node of the world. The graph is the one of 2.1: one node per
occurrence, links in OCaml's direction, a level on every node, a path in
every constructor. Nothing is shared because it is equal and nothing is
interned.

**A scheme is a template.** The generic part of a value's type, of a
constructor's or a label's declaration, of an abbreviation's manifest is a
contiguous run of nodes with relative references. An instance is one pass
that copies the run and adds an offset. A dependency's templates are
frozen in its segment and instantiated from there; nothing of a dependency
is copied into a worker.

**A name is resolved once.** A binder is a dense index; everything known
about it is in arrays indexed by it. The current scope is a dense table
from interned name to binder with an undo log, and an opened module is one
frozen layer. A use is looked up when the walk reaches it and the answer is
written in the row of its syntax node. An environment, wherever one has to
be remembered, is a scope index.

**The walk writes rows, not a tree.** One pass over a unit's items, in
order; inside an item one bidirectional pass over the expression, each
construct either checked against a node or returning one. The result is a
12-byte row per expression and per pattern, indexed by the syntax node, and
a pool for the patterns the match compiler needs. There is no typed tree.

**Nothing is kept for an error that does not happen.** The success path
has no snapshot per unification, no trace, no clash context. A unit with an
error is checked again from its first item in the explaining mode, the same
checker with those kept, and its diagnostics are that run's.

**The world is frozen segments.** A checked unit publishes one segment: its
export table, its declaration rows, its templates. Segments are immutable
and read in place by every worker. A worker owns one checker context for
the whole build and resets its vectors between units.

The algorithms that decide what is accepted are OCaml's and are ported,
not redesigned: unification's cases, expansion, rows and objects, the
exhaustiveness check, signature inclusion, variance. The rewrite is the
representation under them, the walk above them, and the names beside them.

### 3.2 The data structures

Sizes are pinned by a `size_of` test in the slice that introduces the type
(section 5). All of this lives in a new directory, `compiler-rust/src/tc/`.

| Type | Bytes | One per | Layout |
|---|---:|---|---|
| `Ty` | 4 | reference | `u32`; bit 31 set: frozen node (segment page and offset in the other 31 bits); clear: index into the unit's nodes |
| `Node` | 16 | type occurrence | `head: u32` (tag in bits 0..4, flags in 4..8, arity in 8..32), `level: u32`, `a: u32`, `b: u32`. Variable: `a` name, `b` serial. Link: `a` target. Constructor: `a` type index, `b` first slot of its list (slot 0 is the abbreviation memo, then the arguments). Tuple: `b` list. Arrow: `a` result, `b` first parameter. Object, field, row, universal variable, polymorphic type, package: `a` and `b` index their pools |
| list slot | 4 | argument, component | `Ty` in the unit's list pool |
| `Param` | 12 | arrow parameter | `ty: Ty`, `label: u32` (interned name, low bit optional), `loc: u32` |
| `Template` | 16 | scheme | `nodes: u32`, `lists: u32`, `node_len: u16`, `list_len: u16`, `externals: u32` (first of its references to nodes that are not generic). A reference inside a template with bit 30 set is relative to the instance's first node |
| `TypeDecl` | 32 | type declaration | `kind: u8`, `flags: u8` (abbreviation, private, immediate, unboxed, has a local constraint), `arity: u16`, `params: Template`'s index, `manifest: u32` (template or none), `members: u32` and `member_len: u32` (constructors or labels), `path: u32`, `loc: u32`, `variance: u32` |
| `MemberDecl` | 16 | constructor, label | `name: u32`, `args: u32` (template), `tag_or_pos: u32`, `flags: u32` |
| `Binder` | arrays | bound name | `binder_ty: Vec<Ty>` (4), `binder_name: Vec<u32>` (4), `binder_loc: Vec<u32>` (4), `binder_kind: Vec<u8>` (1), one used bit |
| scope log entry | 8 | binding in scope | `name: u32`, `previous: u32` |
| `Scope` | 12 | scope | `parent: u32`, `first_binder: u32`, `opens: u32` (innermost opened layer) |
| `Expected` | 8 | passed down | `Infer` or `Check(Ty)` |
| `Walk` | 16 | passed down | `expected: Expected`, `scope: u32`, `flags: u32` (in a function body, in a pattern, generalisable so far) |
| `ExprRow` | 12 | expression node | `ty: Ty`, `scope: u32`, `resolved: u32` (a binder, an export item, a member declaration or a primitive, by the node's kind); flags in a parallel byte |
| `PatRow` | 12 | pattern node | `ty: Ty`, `scope: u32`, `resolved: u32` |
| `CoreTypeRow` | 8 | type annotation node | `ty: Ty`, `resolved: u32` |
| `ModRow` | 8 | module expression | module type index, coercion index |
| trail entry | 20 | write under a speculation | node index and the node's previous 16 bytes |
| `ExportItem` | 12 | exported name | `name: u32`, `kind: u8`, `payload: u32` (template, declaration, member or child table) |
| `Segment` | per unit | published unit | boxed slices: nodes, list slots, params, templates, type declarations, members, export items sorted by name, child tables; a digest |

There is no `Rc`, `Arc`, `RefCell`, `Cell` or lock in any of them. A
segment is `Send + Sync` because it is plain data.

Today, for scale: `TypeNode` 32 bytes with a 24-byte descriptor in `Cell`s,
typed expressions and patterns 72 bytes with `Arc` descriptions, an `Env`
of persistent maps behind `Rc`.

### 3.3 What every operation costs

The table specifies path halving for `repr`; slice R1 instead builds full
compression in two iterative loops so a second lookup follows just one link.
Compression writes are logged only while a speculation is open.

`n` is the number of nodes an operation is defined to visit. "Kernel" gives
the measurement of 2.2 where one exists.

| Operation | Cost | Kernel |
|---|---|---|
| Read a local node | one indexed load of 16 bytes | |
| Read a frozen node | page table load, then the indexed load; done once per template, not per node | |
| `repr` | one load when the node is a representative; one load and one store per link otherwise (path halving) | in every row below |
| `instance(root)`, root not generic | two loads and a compare | 8 |
| `instance(root)`, root generic with a template | O(template): one copy per node and per list slot, one compare per reference to a node that is not generic | 62 + 27 a node |
| `instance(root)`, first use of a local scheme | the general copy, O(generic nodes), with the forwarding address in a side array indexed by node, no hashing | |
| template capture, second use of a local scheme | O(generic nodes), once per scheme | |
| `unify`, one node on both sides | two `repr` and a compare, inline | 26 |
| `unify`, variable against a type | O(nodes of the type at or above the variable's level): one walk for occurrence, universal variables and levels; one link | 100 a node |
| `unify`, two structures of one constructor that is not an abbreviation | O(pairs): two level compares, one link, the children | 126 a pair |
| `unify`, an abbreviation on either side | one bit test to know; then expansion and OCaml's `unify2`, `unify3` | not in the kernel |
| expansion of an abbreviation | the memo slot when present; else an instance of the manifest's template with the parameters bound, and one memo cell | 62 + 27 a node |
| level update | O(nodes above the target level); one compare when the root is not | 58 a node |
| `generalize` | O(nodes above the current level reachable from the root) | 58 a node |
| `begin_def`, `end_def` | an increment, a decrement | |
| open a speculation, close it without restoring | set a flag and remember the trail's length; clear it | |
| restore a speculation | O(writes made under it) | |
| bind a name | one binder row, one log entry, one table write | 44 with its undo |
| look up a name | one table load, plus one probe per opened layer younger than the hit | 5 without layers |
| look up a binder, a declaration, a member | one indexed load | 5 |
| leave a scope | O(names bound in it) | in the 44 |
| open a module | O(1): push a layer that points at the module's export table | |
| mark a use | set one bit | |
| write a row | one 12-byte store at the node's index | |
| type an expression node | its case; no allocation, no `Vec`, no reference count | |
| exhaustiveness of a match | OCaml's algorithm, on rows of pattern handles | |
| publish a unit | O(exported nodes): one walk that writes the segment, the canonical hash and the digests | |
| reset a checker context for the next unit | O(number of pools): set lengths to zero | |
| check a failing unit again | one more check of that unit, in the explaining mode | |

The step-count tests of the slices (section 6) pin the rows that have a
loop or a recursion, at 10,000 elements.

### 3.4 The passes, in order

For one unit, on its worker:

1. **Reset** the worker's checker context: the lengths of its pools go to
   zero; the frozen prefix (predefined types, the opened initial modules)
   is scope 0 and is not rebuilt.
2. **Items in order**, one walk:
   - a type declaration group: enter the binders of the whole group, then
     translate the bodies into `TypeDecl` rows and templates, then the
     checks of OCaml's `Typedecl` (well-foundedness, variance, immediacy);
   - an external, an exception, a module type: its row;
   - a module binding: type the module expression; a structure is a nested
     run of this pass in a child scope; a path is an export table lookup;
     a functor application and a constraint go through signature inclusion
     and substitution, ported from `Includemod` and `Subst`;
   - a `let`: `begin_def`, the patterns, the bodies with the bidirectional
     walk, `end_def`, generalisation, the binders' types written.
   A use of a name inside a body is resolved when the walk reaches it
   (2.4, idea 5). Unit reads for incremental builds are logged at that
   lookup (THREE_TREES T3), not collected by a second walk.
3. **End of unit**: the delayed checks (unused values, opens, types) are a
   scan of the binder arrays' used bits in binder order; weak variables
   left in the signature are an error (O14).
4. **Against the interface**, when there is one: signature inclusion of
   the inferred signature in the interface's segment.
5. **Publish**: one walk over the exported items writes the segment
   (templates with absolute paths), the canonical signature hash and the
   digests the build system compares.
6. **Hand over**: the rows, the pattern pool and the unit's nodes stay
   alive for the backend and genType, then the context is reset by the
   next unit's step 1.

An interface file runs steps 1, 2 for signature items, and 5.

If step 2, 3 or 4 fails, or a unification fails outside a speculation, the
worker runs the unit again from step 1 in the explaining mode and reports
what that run finds. The mode is a field of the checker context set when
the context is prepared for the unit, not a flag flipped during a walk.

### 3.5 The explaining mode

The same code with three things switched on by the mode: a top-level
unification opens a speculation so that a failure can undo path compression
and expand its trace (`compiler/ml/ctype.ml`, the outer `unify`); the walk
passes the clash site of each construct (today's `ClashSite`); a failed
unification keeps its trace. Printing types, the messages and the code
frames are today's `printtyp.rs` and `driver/type_clash.rs` ported to the
new graph. Nothing else differs, so the two modes accept the same programs
by construction, and the oracle of section 5 checks it: every fixture of
`super_errors` is checked in both modes and must fail in both.

### 3.6 What is shared between compilations

The world of CHECKER_REDESIGN J, with its storage replaced. What the
rewrite does with each slice of J and K:

| Slice | State on trunk (STATUS 1.3, 1.4) | Under the rewrite |
|---|---|---|
| W1 determinism gate | done | **kept**: `scripts/test_worker_determinism.py` is a gate of every slice |
| W2 frozen writes in one table | done | **kept as a mechanism**: 322 of 358,825 published nodes are not generic and can be linked by a dependent; that write goes to the compilation's table |
| W3 the world object | done | **kept**: the unit table and its slots hold segments instead of `SharedGraph`s |
| W4, W5 module views by substitution, adoption | done in part | **subsumed**: a segment already has absolute paths and one export table per module path, children included; there is no view to build and nothing to adopt. `module_view.rs` is deleted with the old checker |
| W5's remaining deletions (registration tables, per-worker views) | not made | **must not be built**: they are edits to `TypeContext` and `env_lazy.rs`, which the rewrite deletes whole |
| W6 delete store builds | not started | **must not be built**: the new checker has no store build to delete; the old one is deleted whole |
| W7 delete the worker-store tier | not started | **must not be built**, same reason; `Ty` has two tiers from the start |
| W8 publication is one export walk | not started | **subsumed**: step 5 of 3.4 is that walk |
| W9 one checker context per worker | not started | **subsumed**: step 1 of 3.4. The reset list is a dozen vectors, not the hundred fields of `TypeContext` (CHECKER_REDESIGN I.6) |
| W10 the opened initial environment once per worker | not started | **subsumed**: scope 0 is frozen in the world, once per build |
| W11 the world outlives a build in watch mode | not started | **kept**, unchanged in intent: segments are keyed by unit digest |
| C4 the other walk families in place | not started | **must not be built**: the walk is replaced |
| C5 snapshots without journal bookkeeping | not started | **must not be built**: 3.5 replaces it; the prototype of 4.2 measures it |
| P6 `env_log.rs` (test-only, 4,466 lines) | built, not switched on | **deleted** by the slice that builds scopes (R4) |

What must keep being built in the meantime: nothing in the checker. Work
that is not the checker (the backend, the printer, the build system) is
independent.

### 3.7 What the backend and the tooling read

Today the conversion to Lambda, match compilation, genType and the unit
reads walk the typed tree and call the checker's own functions on its
types and environments (THREE_TREES section 4: 13 and 27 environment uses
in the two backend files). They cannot keep doing that across a change of
representation. The design puts one interface between the checker and its
readers:

- **Rows** (3.2): type, scope and resolved reference per expression,
  pattern and annotation, read by the syntax node's handle; the pattern
  pool for match compilation.
- **`TypeFacts`**, a trait with the questions readers ask about a type and
  nothing else: its head after expansion, whether it is immediate, the
  runtime representation of a variant or a record (today
  `variant_layout.rs`, `variant_runtime.rs`, `record_runtime.rs`), the
  declaration behind a path, the labels and constructors of a
  declaration. About twenty methods; each is O(1) or one expansion.
- **The published segment** for genType's and the build system's view of a
  unit's signature.

The readers are ported to this interface late (slices R9 and R10), not
first. Until then the new checker's results are converted to what the
readers take today, a typed tree and types in the old representation, by
`tc::bridge::to_old`, lazily and per unit. That keeps the backend untouched
while the checker under it changes, gives byte-identical JavaScript a
single owner (the unchanged backend) during the whole beside period, and
makes the conversion's cost visible in every profile until the readers are
ported and the bridge deleted. Its price is bounded by what it rebuilds:
the typed tree (1.28% of a build as a floor, THREE_TREES section 6) and
the bindings of an `Env` (0.7% of a build, H.2.11: 450 M of 75.3 G).

Editor tooling asks for a typed tree. After slice R8 it checks with the
new checker and takes the tree from the same bridge; slice R10 ports it to
rows and deletes the bridge.

### 3.8 What is not designed here

- The module language beyond paths and structures (functors, first-class
  modules, `module type of`, recursive modules): ported onto the new
  graph, with substitution as OCaml has it. 1.1% of the checker on the
  application, 3.5% on the test project.
- Rows, objects, polymorphic variants, universal variables, GADT
  equations: ported. They are the `false` branches of the kernel.
- The exhaustiveness algorithm: ported onto pattern handles.

### 3.9 Derived items

Trunk types a derived item (`Pstr_derived`, DERIVED_CODECS.md) without
typing a body: `types/derived.rs::discharge` establishes the obligations
of the item's plan in order, and when one fails it undoes what it did and
the item's general form is typed as ordinary syntax, so every diagnostic
comes from the code that types syntax. The new checker keeps exactly that
shape. A value obligation is one name lookup at the current scope (3.3:
one table load and the open layers), one `instance` of the value's
template, and one unification with the obligation's skeleton, which is
built as nodes of the unit's graph; a type obligation resolves a path to a
`TypeDecl` row and reads its members (`MemberDecl` rows: the labels of a
record, the constructors of a variant) by index, with no copy of the
declaration. The item is discharged under one speculation (3.3), in both
modes: a failed obligation restores it, takes back the warnings and usage
marks recorded since the item began, and the item's general form goes
through the walk of 3.4 like a hand-written `let`. That fallback is local
to the item and is not a failure of the unit; the unit is checked again in
the explaining mode only if the general form then fails. A discharged item
writes no `ExprRow`, because it has no expression nodes: it writes one
binder per binding (type, name, location, as any `let`) and two dense
tables indexed by the plan's handles, one row per binding (binder index,
4 bytes) and one per obligation (`resolved: u32`, the same reference an
`ExprRow` carries: a binder, an export item or a member declaration).
These are today's tables of `types/derived.rs` with handles of the new
checker; `raw_lambda/convert/derived.rs` reads them through
`tc::bridge::to_old` until R9a and directly after. Unit reads are logged
at the obligation's lookup. The cost of a discharge is O(obligations +
skeleton nodes), as today. Slice R6g carries it; until then a unit with a
plan is declined.

## 4. Proof by prototype

The two items with the largest predicted saving that a patch on trunk can
test are unification with its journal (8,297 instructions a line, 2.3 items
1 and 12) and instantiation (4,341, item 4). Names are larger (9,812) but
no patch on today's `Env` tests the design for them: that design removes
`Env`, and CHECKER_REDESIGN H.2.11 is what a replacement behind `Env`'s API
measures.

Both patches apply to trunk 7e1dbc2bd4 (`git apply`), build, and compile
both projects with no difference in signatures, diagnostics or generated
files. They are measurement prototypes, not reviewed code. The
unification patch applies at 7e1dbc2bd4 and not after trunk commit
5471bf8060, which changed the part of `driver.rs` it edits (checked with
`git apply --check` on trunk 5fc812e1ac: the `driver.rs` hunk is
rejected). The instantiation patch still applies there.

### 4.1 Instantiation from templates

[instantiation-prototype.patch](prototypes/instantiation-prototype.patch):
429 lines added, of which `types/templates.rs` is 349.

**What it does.** `ctype::instance` of a generic root asks for the root's
template. The second time a root is instantiated its generic part is
captured: the nodes in the order `copy_type_cached` allocates their
copies, child references relative or to a node that is not generic. From
then on an instance is one loop over the template that allocates each node
with its final descriptor: no `CopyCache`, no map from node to copy, no
recursion, no placeholder written twice. It allocates the same nodes in
the same order with the same identifiers as the general copy, so the two
paths leave the same graph. Local roots are looked up in a dense table by
node index, frozen roots in a hash map.

What keeps it exact:

- A template is stale when one of its generic nodes is written. A write
  to a local node tests one watermark (nodes that existed when a template
  was last captured) and, below it, whether the node is generic; then an
  epoch is bumped. 374 templates went stale on the application.
- A reference to a node that was not generic is checked at each instance:
  its representative is taken as it stands, and if it has become generic
  the template is rebuilt.
- O11: when the simple-abbreviation memo holds an expansion of a nullary
  constructor the template contains, the general copy runs (42,882 times
  on the application).
- Frozen roots are skipped as soon as the compilation has written to any
  frozen node.
- Rows, objects, polymorphic types, the multi-root copies
  (`instance_constructor`, `instance_label`, `instance_list`) and copies
  under a non-empty abbreviation context take the general copy.

**Prediction, made before the measurement.** Plain `instance` was taken to
cover about 60% of the copied nodes, and a templated node to cost about
120 instructions against 592: 4% to 5% of the checker.

**Measured.**

| Workload | Measure | Trunk | Prototype | Change |
|---|---|---:|---:|---:|
| Test project | instructions of type checking, mean of 3 | 1,310.10 M | 1,301.78 M | **-0.64%** |
| Test project | the same binary with `RESCRIPT_NO_TEMPLATES=1` (the write guard alone) | | 1,313.76 M | +0.28% |
| Application | instructions of type checking, one run (trunk: 26,698 M and 26,729 M in two runs) | 26,714 M | 26,487 M | **-0.85%** |
| Application | instructions of the build (cachegrind) | 67,829 M | 67,615 M | -0.32% |
| Both | `scripts/compare_checker_builds.py` | | | no difference: 738 and 3,735 signatures, 1 and 18 diagnostics files, 732 and 3,980 generated files |

| Counter | Test project | Application |
|---|---:|---:|
| Nodes copied by `instance` and its variants (1.5) | 255,735 | 4,817,581 |
| Instances made from a template | 40,239 | 658,001 |
| of which from a frozen root | 8,961 | 193,565 |
| Nodes they made | 74,513 (29%) | 1,667,361 (35%) |
| Templates captured | 6,943 | 149,859 |
| Instances per template | 5.8 | 4.4 |

**The prediction was wrong by a factor of six, for three reasons that the
numbers separate.**

1. *Coverage is 29% to 35% of the copied nodes, not 60%.* The first use of
   a root, the multi-root copies of constructors and labels and the roots
   with rows take the general copy.
2. *A templated node costs about 230 instructions in today's checker, not
   120.* On the test project the template path saves 12.0 M against the
   same binary without it, and capturing costs about 10 M (callgrind,
   inclusive cost of the capture); so 74,513 nodes save 22 M before
   capture, 295 a node, of the general copy's 523. What is left is not
   the copy: it is creating a node today. `alloc_type` (a store-build
   test, an atomic increment for the identifier, the push) and the memo
   cell pushed on a `RefCell<Vec<RefCell<_>>>` for every copied
   constructor are 32.6 M and 26.2 M inclusive on the test project (2.5%
   and 2.0% of the checker), and a list is allocated in a pool through a
   `SmallVec`; a template pays all three.
3. *Capture eats half of the gain.* At 4.4 to 5.8 instances per template
   and about 1,400 instructions a capture, a scheme has to be
   instantiated three times before its template has paid for itself.

**What the design changes because of it.**

- The saving of instantiation is not in the copy algorithm. Section 1
  charges `alloc_type`, the list pools and the memo cells to the item that
  calls them, so "instantiation, 10.7%" is mostly the price of making a
  node, and so is a part of every other item that makes nodes. The design
  already replaces those (a 16-byte push, a list slot, a memo slot that
  costs nothing until an expansion is memoised); the prototype shows that
  *this* is the part that carries the number, and that a template on
  today's storage is worth 0.3% of a build. It is not worth landing on
  trunk.
- A dependency's templates are written once, at publication, into the
  segment (3.4 step 5): 29% of the templated instances come from frozen
  roots and their capture is paid once per build, not once per
  compilation as in the prototype.
- A local scheme is captured at its *third* instance, not its second, and
  its first two copies use the forwarding array (3.3).
- The estimate of item 4 is corrected in section 7: the kernel's figure
  (600 a line) is kept as the design's, and the figure the prototype
  supports is stated beside it: a templated node at 44% of a copied
  node's cost (230 of 523 on the test project) is 1,900 a line if only
  the copy changed and every node were covered.

No program was found for which the prototype's output differs; the
smallest program that would show a difference if the guard were missing is
`checker_identity_02_annotated.res`, where an annotation's generic
structure is instantiated twice and one copy is then linked.

### 4.2 Unification without a journal on the success path

[unify-prototype.patch](prototypes/unify-prototype.patch): 90 lines added,
14 deleted, in `ctype.rs`, `context.rs` and `driver.rs`.

**What it does.** A checker context has a mode. In the success mode a
top-level `unify` opens no snapshot unless a speculation is already open;
a failure there is recorded in the context. The driver checks a unit in
the success mode; if the unit has an error, or any unification failed
without its snapshot, that attempt is thrown away and the unit is checked
again by the checker as it is today. So the output of the success mode is
used only when the snapshot would never have been read. This is the
mechanism of 2.4 idea 8 with today's checker as the explaining mode.

**Prediction, made before the measurement.** The bookkeeping of the
snapshot is `snapshot_type_state_with`, `TypeMutationJournal::finish` and
`TypeMutationSnapshot::drop`: 2.12% of the checker on both projects (1.2,
row 12), plus a part of the per-write mode test. 2.1% to 2.4% of the
checker; no unit of either project checked twice.

**Measured.**

| Workload | Measure | Trunk | Prototype | Change |
|---|---|---:|---:|---:|
| Test project | instructions of type checking, mean of 3 | 1,310.10 M | 1,280.96 M | **-2.22%** |
| Test project | instructions of the build (cachegrind, one run; two runs of trunk differ by 0.09%) | 4,078.9 M | 4,049.7 M | -0.72% |
| Application | instructions of type checking, one run | 26,714 M | 26,146 M | **-2.13%** |
| Application | instructions of the build (cachegrind) | 67,829 M | 67,234 M | **-0.88%** |
| Both | units checked twice | | | 0 of 738, 0 of 3,735 |
| Both | `scripts/compare_checker_builds.py` | | | no difference |

The prediction holds. 865 instructions a line of the journal's 1,331 are
gone; what is left of row 12 is the per-write test of whether a
speculation is open and the 131,000 snapshots that are real speculations.

**What it shows beyond its own number.** A unit can be checked on a path
that keeps nothing for error messages, and a failing unit checked again,
with identical output on 4,473 units and without one unit taking the slow
road on code that compiles. That is the assumption every other item of the
design leans on when it drops a trace, a clash context or an owned
string.

**What it does not show.** The error fixtures. The patch changes only the
build path (`compile_until_js`); the single-file path the `super_errors`
runner uses is untouched, so the 746 fixtures were not run through the
re-check. Their output is today's by construction (the second attempt *is*
today's checker), but that the success mode fails for each of them was not
tested here. Slice R8 tests it.

### 4.2 as landed

Implementation record for `65fdcaa71`; this describes the review candidate,
not a claim that its branch has already merged.

**One attempt owner.** `driver::type_structure_two_modes` serves all six
entry points below. Parsing/frontend work happens first; frontend diagnostics
are reported once outside the attempt. Each iteration then creates a fresh
`TypeContext`, defers its counters **before environment setup**, fixes its
`CheckMode`, and runs checking plus the validating continuation. The continuation
keeps the context alive without a self-referential owner. Reports and dumps are
private until `AttemptOutput::publish` retains the counters and permits output.
The typed result, environment, reports and context of an abandoned check are
dropped before the next check begins. No reports are deduplicated.

Success-mode unification skips diagnostic-only snapshots, but still snapshots
under live speculation: `Explain || mutation_logging.compress()`. A type-check
error, a caught unexplained unification failure, or a continuation validation
error before publication reruns in Explain. After publication, a later error
cannot replay that attempt's externally visible work.

**Derived fallback shares this loop.** `CheckAttempt::after` applies each retry
reason at most once: `DerivedFallback` changes from planned to general syntax
without changing mode; `Explain` changes mode without changing syntax. The
fallback provider runs only when needed, and the loop owns the resulting
`GeneralSyntax` (arena, tree and warning-location provider). Checking, diagnostic
placement, census and lowering all use that syntax. A fallback followed by an
error therefore takes at most three attempts: planned Success, general Success,
general Explain. Without a provider, `DerivedRetry` escapes rather than silently
checking the wrong tree. Source compilation and batch builds supply providers;
interfaces have no derived implementation plans, and tooling uses general syntax.

Location retries remain requests to the source owner for a located parse, not
checker failures. A pending `LocationRetry` discards reports and counters without
an Explain rerun. The located compile starts its own loop and explains an actual
error there. Consequently the three-attempt bound is **per loop invocation**, not
per whole build: a location retry after fallback can regenerate planned syntax
and fall back again. Its extra abandoned work is not a retained diagnostic.

**Entry-point boundaries.** Every row starts its attempt after frontend
preparation, before initial-environment setup. The end is the validating
continuation's retained result (or its explained failure); publication begins
at the boundary shown, never at the first successful `type_structure` return.

| Entry point | Validation before retention | Publication starts |
| --- | --- | --- |
| `compile_source_to_js_with_options_inner` | `type_structure`; inferred/interface coercion; `check_nongen_schemes`; signature normalization; delayed warnings; raw conversion; lowering/JS diagnostics; fatal warnings | Explicit `attempt_output.publish` before externally written outputs; buffered reports, GenType/source maps and returned JS (typed-only has its own validated boundary) |
| `compile_until_js` (batch/playground) | `type_structure`; interface inclusion; JS names; non-generalizable schemes; normalization; delayed checks; deprecation payload; raw conversion and late/fatal warnings | `publish_checked` retains before `signature_ready` and the returned pre-JS result; check-only validates inclusion warnings before this callback |
| `typecheck_interface_source` | `transl_signature`; persistent-environment errors; JS names; self-inclusion; delayed/fatal warnings | Owner publishes buffered reports after the continuation, before returning |
| `typecheck_preprocessed_signature_in_process` | `transl_signature`; persistent errors; JS-name/self-inclusion checks; delayed/fatal warnings; GenType read; saved-signature/deprecation payload work | Explicit `attempt_output.publish` before extracting/publishing the retained interface result |
| `typecheck_structure_for_tooling` | `type_structure`; interface inclusion for dependency recording; error conversion | Owner retains before returning typed arena, context and typed result/error |
| `typecheck_signature_for_tooling` | `transl_signature` and error conversion | Owner retains before returning typed arena, context and typed result/error |

The batch path freezes its **private** inferred signature before raw translation
mutates type nodes; moving that freeze later breaks the Belt snapshot proof.
The frozen result does not escape via `signature_ready` until validation succeeds.
Its freeze/hash/publication counters belong to the attempt, not process totals.
Signature-check report bytes are prepared privately and written only on retention.
The shared final context use of all six entry points asserts that a published
Success attempt has no unexplained unification failure, including after hooks.

**Post-structure failures are included.** `non_generalizable.res` gets through
structure checking and fails validation of its inferred signature. Its first
Success attempt is discarded; Explain runs once and emits the same diagnostic
as forced Explain. The regression `post_structure_validation_is_rechecked_before_publication`
exercises this boundary. Warning-before-error and caught-unification-failure
regressions also compare output with forced Explain.

**Counter ownership.** The lazily allocated 1,432-byte `AttemptCounters` holds
journal, lookup, frozen/store, copy/qualification/freshening, checker census,
export, publication, GenType and per-attempt signature-decode counts. Keep
publishes once; later probes flush on drop. Discard publishes none. Item census
snapshots read only the current context. Shared world/importer work, retry
observations and identity allocation have explicit, different lifetimes; see
[the counter audit](CHECKER_SNAPSHOT_ELISION_COUNTER_REVIEW.md) for the complete
inventory, commit/drop sites, exceptions and personally rerun tests.

`RESCRIPT_CHECK_MODE=explain` selects the reference snapshot policy.
`RESCRIPT_COMPILER_COUNTERS=1` reports attempts and reruns; the CLI resets those
two counters after dependency preparation. Frontend failures then have zero
attempts. The fixture gate excludes them by observation, not fixture names.

**Evidence by revision.** Whole-project measurements below compare `913faa5ed`
with `be1b3a482`; they predate the review corrections. The corrected-head
late-failure measurement and its command are in the measurement record.
Checker census remains explicitly gated to `RAYON_NUM_THREADS=1`.

Current fixture gate (explicit binary/runtime and source-only temporary inputs):

- `RAYON_NUM_THREADS=1 python3 scripts/test_check_modes.py --rescript "$RESCRIPT"
  --runtime packages/@rescript/runtime --jobs 4`: **747 fixtures, 597 rechecked,
  63 frontend-only, 0 failures**. Diagnostic bytes and exit status must agree.
  Both modes must agree on whether checking began; an Explain run that reaches
  checking and reports a type error requires a default-mode Explain rerun.
  Zero attempts in both modes is a frontend-only result, not an exemption by
  fixture name. Counter-enabled runs observe each mode separately from the
  uninstrumented diagnostic comparison.
- Diagnostic parity: 2,137 cases; JS parity: 737 snapshots; both Rust suites and
  both `super_errors` suites pass.
- Clean single-worker `tests/tests`: 944 attempts, **0 Explain reruns**;
  application: 4,005 attempts, **0 Explain reruns** (includes runtime/dependencies).
  Ordinary default `tests/tests` build also succeeds, compiling 743 modules.
- Matched outputs: 743 and 3,735 signatures, respectively, with no differences
  in diagnostics, JavaScript, generated TypeScript or source maps.
- Five-run minimum instructions: **−0.620%** for `tests/tests`, **−0.740%** for
  the application. Application hyperfine: base 12.999 ± 0.840 s, candidate
  13.094 ± 0.511 s; overlapping ranges, no demonstrated wall-time improvement.

[The measurement record](CHECKER_SNAPSHOT_ELISION_MEASUREMENTS.md) includes exact
commands and raw counts. Its earlier 1.597× same-failure retry harness result
belongs to an older revision, not final-head evidence or a universal cost bound.

### 4.3 What the two prototypes do not prove

- Nothing about names (2.3, items 3, 6 and 9), the largest group and the
  least certain number.
- Nothing about the walk, the allocator or expansion.
- The kernel's per-operation costs inside a full checker. Prototype 4.1
  is the caution: a mechanism measured alone at a fifth of today's cost
  delivered a sixth of the predicted saving when everything around it
  stayed. The design's numbers hold only if the storage, the names and
  the walk change together, which is why it is a rewrite, and why slice
  R5c and slice R7 carry hard measurement gates (5.3).

### 4.4 How the numbers were measured

- Trunk 7e1dbc2bd4; each prototype built in its own complete checkout with
  the same profile as the trunk binary of section 1 (fat LTO, line
  tables).
- Type checking: `valgrind --tool=callgrind --collect-atstart=no
  --toggle-collect=rescript_compiler::types::typemod::type_structure`,
  one worker, clean build. The test project three times a side,
  interleaved; the spread of one side is 0.16% (trunk: 1,309.04 to
  1,311.11 M). The application once a side, trunk twice (0.12% apart).
- Whole build: `valgrind --tool=cachegrind --cache-sim=no`, one worker,
  clean build, once a side on the application.
- Counters: `RESCRIPT_TEMPLATE_STATS=1` and `RESCRIPT_EXPLAIN_RERUNS=1`,
  switches of the prototypes.
- Output: `scripts/compare_checker_builds.py PROJECT trunk prototype` on
  both projects.
- Not measured: wall time, cycles, cache misses, memory, the profile-guided
  build, more than one worker.

## 5. The route

### 5.1 Beside the old checker, one switch, a unit at a time

The new checker is built beside the old one in `compiler-rust/src/tc/`,
behind one switch, `RESCRIPT_CHECKER`:

- `old`: today's checker. The default until slice R7.
- `new`: every unit is offered to the new checker first. It either checks
  the unit or **declines** it, before it has published anything, with a
  reason from a closed enum (`Declined::Polyvariant`, `Declined::Gadt`,
  ...). A declined unit, and a unit the new checker finds an error in, is
  checked by the old checker.
- `both`: every unit is checked by both and compared before either result
  is used: canonical signature (`--dump sig`), warnings with their
  locations, and the unit reads. `scripts/compare_checker_builds.py`
  compares the generated JavaScript of an `old` build and a `new` build of
  the same project. This is the oracle of every slice.

Why not family by family inside the old checker: a unit's type graph cannot
be half 32-byte nodes behind cells and half 16-byte nodes in a `Vec`. The
type representation is the thing being replaced, every function of the old
checker reads it, so the smallest piece that can change hands is the
checking of one unit. Fast paths in front of old code are what sections I
and K already did, and what this task rules out.

Why a unit at a time and not a build at a time: a slice has to show a
measurement on the test project and on the application, and neither is
covered whole until late. With per-unit declining, a slice that adds a
construct family lowers the count of declined units and the instruction
count of both projects in the same pull request, with identical output by
construction (a declined unit takes the old road).

What per-unit mixing costs: a unit checked by one checker must be readable
by a dependent checked by the other. Two converters do that,
`tc::bridge::to_old` (a segment as the old checker's shared graph; the rows
as a typed tree for the backend) and `tc::bridge::from_old` (an old shared
graph as a segment). Both are lazy, one `OnceLock` per unit, so a build in
which no unit needs the other format pays nothing. Both are deleted:
`from_old` in R7, `to_old` in R9 and R10.

A coverage ratchet keeps the direction: `compiler-rust/tc_coverage.txt`
lists, per corpus (the test project, the runtime library, the application
by count only), the number of units declined for each reason. CI fails if
a count rises. It is the same instrument as the backend's ratchet file.

### 5.2 The end state

Run from `compiler-rust/`. "0" means no match.

**Exists.**

| Fact | Check |
|---|---|
| The checker is `src/tc/` | `ls src/tc` shows `graph.rs`, `template.rs`, `unify.rs`, `expand.rs`, `level.rs`, `scope.rs`, `names.rs`, `decl.rs`, `walk/`, `pattern.rs`, `exhaust.rs`, `module.rs`, `include.rs`, `segment.rs`, `publish.rs`, `rows.rs`, `facts.rs`, `explain.rs`, `print.rs` |
| A node is 16 bytes, a row 12, a value passed down the walk 16 | `rg -n 'size_of::<Node>\(\), 16' src/tc/graph.rs`, `rg -n 'size_of::<ExprRow>\(\), 12' src/tc/rows.rs`, `rg -n 'size_of::<Walk>\(\), 16' src/tc/walk/mod.rs` give 1 each |
| No shared ownership, cell or lock in the checker's data | `rg -n 'Rc<\|Arc<\|RefCell<\|Cell<\|Mutex<\|RwLock<' src/tc --glob '!world.rs'` gives 0 |
| No hash map keyed by a handle | `rg -n 'HashMap<(Ty\|u32\|NodeIdx\|Binder)' src/tc` gives 0 |
| A segment is shared between threads | `rg -n 'assert_send_sync::<Segment>' src/tc/segment.rs` gives 1 |
| Instantiation is one pass | `rg -n 'fn instance' -A30 src/tc/template.rs` shows no recursion and no map |
| The success path takes no snapshot | `rg -n 'fn unify' -A12 src/tc/unify.rs` shows the mode test before any trail use |
| One checker context per worker | `rg -n 'fn reset_for_unit' src/tc/context.rs` gives 1; its body destructures every field without `..` |

**Gone.**

| What | Check, expecting 0 or absence |
|---|---|
| The old checker's five files | `src/types/typecore.rs`, `src/types/ctype.rs`, `src/types/typemod.rs`, `src/types/env.rs`, `src/types/thread_store.rs` do not exist |
| Their satellites | `src/types/{context,type_expr,env_lazy,env_log,env_log_tests,shared_store,module_view,world,btype,includemod,includecore,parmatch,type_marks,printtyp}.rs` do not exist |
| The typed tree | `src/types/{typedtree,tast_arena,tast_iterator,sexp_typedtree}.rs` do not exist; `rg -n 'TypedArena' src` gives 0 |
| The old handles and context | `rg -n 'TypeExprRef\|TypeContext\|TypeCheckContext' src` gives 0 |
| The switch, declining, the bridge | `rg -n 'RESCRIPT_CHECKER\|Declined::\|tc::bridge' src ../scripts ../rewatch` gives 0; `tc_coverage.txt` does not exist |
| The mechanisms J listed as gone | every "Gone" row of CHECKER_REDESIGN J.2 gives 0, because the files they are in are gone |

### 5.3 The slices, in order

Gates of every slice, not repeated: `cargo build` and `cargo test` for
`compiler-rust` and `rewatch`; CI green with the four output parity suites
and the instruction count; `scripts/test_worker_determinism.py`. From R5
on: `scripts/compare_checker_builds.py` between an `old` and a `new` build
with no difference on the test project and the application, and a `both`
build of each with no mismatch.

"Model" says whether a less capable model can build the slice from its
prompt in section 6.

| # | Builds | Deletes | Lines | Extra gate | Measurement it must show | Depends on | Model |
|---|---|---|---:|---|---|---|---|
| R0 | The switch (`old` only does anything), `both` mode's comparison, the ratchet file with every unit declined, the canonical signature numbering shared structure nodes (CHECKER_REDESIGN I.3.5), a fixture for O11, the step-count test helper | Nothing: it replaces nothing | 900 | the new canonical form differs between `dup` and `two` of `checker_identity_07b_sharing.res` | instruction count unchanged (±0.1%) | - | yes |
| R1 | `tc/graph.rs`, `tc/level.rs`, `tc/template.rs`: nodes, pools, `repr`, links, the trail, levels, generalisation, templates with capture and instance, the general copy with a forwarding array. Not wired to the driver | Nothing yet | 2,500 | step counts at 10,000; a property test against the old `instance`, `generalize` and `update_level` through R2's converters is added by R3 | same-machine measured attribution table; instance7 generic bookkeeping at most 30 instructions above the kernel (see [R1 measurements](TC_KERNEL_R1.md)) | R0 | yes |
| R2 | `tc/segment.rs`, `tc/publish.rs`, `tc/bridge/{from_old,to_old}.rs` for signatures; the canonical signature printed from a segment | Nothing yet | 3,000 | for every unit of both corpora: `to_old(from_old(g))` and `g` print the same canonical signature, with shared-node numbers | publication of a segment from an old graph costs at most what `publish_signature` costs today (1.34% of the application) | R1 | yes |
| R3 | `tc/unify.rs`, `tc/expand.rs`: unification with every case of `ctype.rs`, expansion and its memo, `moregeneral`, `equal`, subtyping; the simple-abbreviation memo and the copy-time nullary `find_repr` lookup in general copies and template instances | Nothing yet | 6,000 | differential property test: random graphs converted both ways, the same operations on both, canonical forms and failures equal; the `checker_identity_*` shapes as unit tests on the new graph | kernel operations with abbreviations added, reported | R1, R2 | no |
| R4 | `tc/scope.rs`, `tc/names.rs`: binders, scopes, open layers over export tables, path resolution, usage bits, lookup-time warnings | `types/env_log.rs`, `types/env_log_tests.rs` (4,466 lines: the binding log P6 built and did not switch on) | 3,000 | step counts at 10,000 binders and 10,000 nested scopes; a differential test of lookups against `Env` on every identifier of both corpora in `both` mode | lookup by name at most 80 instructions, by binder at most 10, in the crate's bench | R2 | no |
| R5a | `tc/decl.rs`, `tc/walk/typetexp.rs`: type declarations (records, variants, abbreviations, abstract, externals), annotations | Nothing yet | 4,000 | `both` mode on declaration-only units | - | R3, R4 | no |
| R5b | `tc/walk/`: the core expression language on the success path, patterns, `tc/exhaust.rs`, `tc/rows.rs`; structures, aliases and opens in `tc/module.rs` | Nothing yet | 9,000 | step counts at 10,000 for sequences, applications, record fields, match cases | - | R5a | no |
| R5c | The driver takes the new road for units that are not declined; `to_old` for rows (typed tree for the backend); `RESCRIPT_CHECKER=new` works | The ratchet entries of every unit now covered | 2,500 | the oracle, first time on real units | type checking of the covered units of the test project at most 60% of the old checker's instructions for the same units, the bridge included | R5b | no |
| R6a..R6f | One family each, each with its `Declined` reasons: (a) labelled and optional arguments, JSX; (b) polymorphic variants, objects, rows; (c) GADTs, existentials, locally abstract types; (d) functors, module types, `include`, first-class and recursive modules; (e) exceptions, `async`, dicts, unboxed and untagged variants, coercions; (f) interface files and signature inclusion (`tc/include.rs`) | The `Declined` variants of the family and their ratchet rows | 2,000 to 5,000 each | the oracle; the family's `super_errors` fixtures still fail (through the old checker) | the declined count of the family goes to 0 on both corpora; instructions per line of type checking reported | R5c | first of each kind no, then yes |
| R6g | Derived items (3.9): `tc/derived.rs`, a port of `types/derived.rs::discharge` onto templates, member declarations and scopes, with the per-item fallback to the general form; the binding and obligation tables; `to_old` for them | `Declined::DerivedItem` and its ratchet rows | 1,200 | `RESCRIPT_DERIVED_PATH=check` builds `tests/ppx_spice` with no difference under `RESCRIPT_CHECKER=new`; the 14 fixtures of `tests/build_tests/super_errors_derived` give their expected files; the oracle | declined units with a plan go to 0 on every corpus; a discharge is at most 3 steps an obligation and 2 a skeleton node at 10,000 | R5c, and R6a for labelled arguments in skeletons | yes |
| R7 | `new` is the default. The old checker runs only for a unit with an error and for tooling | `Declined`, `tc_coverage.txt`, `tc/bridge/from_old.rs` | 600 | every project under `tests/` builds with zero declined units, `tests/ppx_spice` included | **type checking at most 24,000 instructions per line on the application** (surroundings included, bridge included), and the CI instruction count of the test project down by at least 12% | all R6, R6g included | yes |
| R8a..R8c | The explaining mode: `tc/explain.rs`, `tc/print.rs`. (a) type clashes and the type printer; (b) every other expression and pattern error; (c) declaration, module and inclusion errors. Tooling entry points check with the new checker and get their typed tree from `to_old` | (c) deletes `types/typecore.rs`, `types/typemod.rs`, `types/includemod.rs`, `types/includecore.rs`, `types/parmatch.rs`, `types/printtyp.rs`, and every function of `types/ctype.rs` the backend does not call | 3,000 each | `scripts/test_error_output_parity.sh`, the `super_errors` and `super_errors_multi` suites, with `RESCRIPT_CHECKER=old` no longer accepted after (c) | a failing unit costs at most 2.2 times a passing one | R7 | (a) no, (b) and (c) yes, one error at a time |
| R9a..R9c | Readers on rows and `TypeFacts`: (a) `raw_lambda/typeopt.rs` and `convert.rs`; (b) `matching.rs` and the pattern pool; (c) genType and unit reads (THREE_TREES T9, T10, T11, T3) | (c) deletes the batch build's use of `to_old`, the rest of `types/ctype.rs`, `types/context.rs`, `types/type_expr.rs`, `types/env.rs`, `types/env_lazy.rs`, `types/thread_store.rs`, `types/shared_store.rs`, `types/module_view.rs`, `types/world.rs`, `types/btype.rs`, `types/type_marks.rs` | 3,000 each | JavaScript, stdlib and genType parity | **type checking at most 20,000 instructions per line on the application** | R8 | (a) and (b) no, (c) yes |
| R10 | Editor analysis on rows (THREE_TREES T12) | `types/{typedtree,tast_arena,tast_iterator,sexp_typedtree}.rs`, `tc/bridge/`, the switch | 3,000 | analysis tests | - | R9 | yes, arm by arm |

**R1 measured price:** instance1/3/5/7 as built cost 140.06/220.31/305.34/327.27
instructions against the kernel's 89/169/221/250; the R5c gate (covered units
at most 60% of the old cost, bridge included) judges whether this matters.

About 55,000 lines built, 110,000 deleted (`src/types` is 123,242 lines
today, tests included).

**What a slice deletes, plainly.** R0 to R5b delete almost nothing, because
until R5c nothing of the old checker is replaced: they build a second
checker that no build uses. The first deletion of old code that matters is
R8c. That is a property of replacing a representation and not a choice:
the alternative, deleting piece by piece, needs the two representations in
one graph. What keeps the beside period honest is the ratchet (no slice
may land without lowering a count from R5c on), the two hard measurement
gates (R7, R9), and the rule that the bridge's converters are lazy and
therefore visible in a profile whenever something still needs them.

**The order is forced** except for two freedoms: R6a to R6g can be built in
parallel by different workers once R5c has landed, and R9a to R9c can
start after R7 on the old checker's side of `TypeFacts` if workers are
free (they then land before R8 and R8c deletes less).

**If a gate fails.** R7's gate is the test of the whole design. If the
application is above 24,000, the profile of section 1.1 is run on the new
checker and its top item is fixed before the default flips; the default
does not flip on a promise.

## 6. Worker prompts

Each prompt is given verbatim, with the common part in front of it. `rg` is
run from `compiler-rust/`. In a pattern, type `|` where a table of this
document wrote `\|`.

### 6.0 The common part

```text
You build one slice of the type checker rewrite. Read first, in this order:
AGENTS.md; compiler-rust/docs/CHECKER_REWRITE.md sections 2.1, 3 and 5; the
row of your slice in 5.3. The old checker (compiler-rust/src/types/) and the
OCaml sources (compiler/ml/) are the reference for behaviour. The new
checker lives in compiler-rust/src/tc/ and shares no type with the old one
except through tc/bridge.

The contract: the same programs accepted and rejected, the same warnings
and errors in text and location, byte-identical JavaScript, no dependence
on worker count. The list of what is observable is section 2.1; when your
code decides whether two types are one node, which way a link points,
whether a node is generic or which path a node carries, it does what OCaml
does, and you cite the OCaml location in a comment.

Engineering standard, checked by the reviewer:
1. Every function you add on a compile path states in its doc comment what
   one call costs. Wherever it has a loop or a recursion, a test builds an
   input of 10,000 elements, counts steps with tc::steps (R0), and asserts
   the bound (for example: at most 3 steps per element). A walk over a
   type 10,000 nodes deep must not overflow a 2 MB stack: use an explicit
   stack.
2. No hash map keyed by a handle, a binder, a unit or a node: use a dense
   table indexed by it. A hash map in new code needs one sentence in the
   pull request saying why no index exists.
3. No allocation per visited node: no Vec, String, Box, format!, Rc or Arc
   clone inside a walk. Use the context's pools and handles.
4. No lock, atomic write or thread-local access per node or per lookup.
5. No second pass over a tree for a fact the first pass could record.
6. A size_of test for every struct or enum stored per node or passed down
   a walk; a value passed down a walk is at most 16 bytes.
7. Instruction counts before and after, on tests/tests (CI) and on the
   application where you can reach it. Say plainly when nothing is saved.
8. One path: what your slice replaces is deleted in the same pull request.
   No second switch, no fallback other than Declined, no dead code.

Shortcuts that count as failure, in every slice:
- weakening, deleting or re-recording a test or an expected file to make a
  gate pass;
- sharing two type nodes because they are equal, interning a type, or
  skipping a level write for a type without variables (CHECKER_REDESIGN
  I.1 to I.3 say why);
- calling into compiler-rust/src/types/ from tc/ outside tc/bridge;
- a `Declined` reason that is not in the closed enum, or declining after
  anything was published or any warning was emitted;
- a number in the pull request that you did not measure.

Gates: cargo build and cargo test for compiler-rust and rewatch;
scripts/test_worker_determinism.py; CI green (JavaScript, diagnostics,
stdlib and genType parity; the instruction count). Paste real output.
One pull request against ocaml-to-rust-rewrite, commits in the order given,
each building and passing tests on its own.
```

### 6.1 R0: oracle, switch, ratchet

```text
Task R0: the instruments of the rewrite. No checker code.

End state:
- rg -n 'RESCRIPT_CHECKER' src/driver.rs gives the one read, into an enum
  CheckerChoice { Old, New, Both } carried in CompilerOptions.
- rg -n 'pub\(crate\) enum Declined' src/tc/mod.rs gives 1, with one
  variant, NotBuilt; rg -n 'fn check_unit' src/tc/mod.rs gives 1, a
  function that returns Err(Declined::NotBuilt).
- compiler-rust/tc_coverage.txt exists: one line per corpus and reason,
  "tests/tests NotBuilt <n>", written by scripts/tc_coverage.py, which
  also checks it (exit 1 when a count rose).
- rg -n 'fn write_shared' src/types/canonical_sig.rs gives 1: a structure
  node reached twice in one item is printed with a number, as variables
  are, so that `dup: int => (int, int)` with one shared node and with two
  nodes print differently.
- src/tc/steps.rs: a counter compiled only under cfg(test), `steps::tick()`
  and `steps::scope(|| ..) -> u64`.
- tests/build_tests/super_errors/fixtures/checker_identity_12_memo.res with
  its expected file, or a paragraph added to CHECKER_REWRITE.md 2.1 row O11
  saying which programs were tried and that none shows the rule.

Commits, in order:
1. CheckerChoice and its plumbing; Both behaves as Old.
2. tc/mod.rs with Declined and check_unit; in New and Both the driver calls
   it, gets NotBuilt and takes the old road. In Both it also compares the
   two results; with one checker that is a no-op you unit-test with a fake.
3. scripts/tc_coverage.py, the file, its CI wiring given as lines in the
   pull request body (do not edit .github/workflows).
4. Shared-node numbers in the canonical signature; expected dumps updated
   by scripts/update_expect_dumps.py only.
5. tc/steps.rs with its own test.
6. The O11 fixture or the paragraph.

Tests: a unit test that the canonical text of fixture 7b's `dup` and `two`
differ; scripts/compare_checker_builds.py with base and candidate the same
executable reports no difference under RESCRIPT_CHECKER=both.

Failure: changing any behaviour of the old checker; a canonical form that
depends on node indices.
```

### 6.2 R1: the graph

```text
Task R1: the type graph of the new checker, not wired to the driver.

End state:
- src/tc/graph.rs: Ty(u32), Node (16 bytes, layout of CHECKER_REWRITE 3.2),
  Graph { nodes, lists, params, trail, level, mode }, repr with path
  halving, link (Btype.link_type's naming rule for variables), write
  (logs only while a speculation is open), speculation open/keep/restore.
- src/tc/level.rs: begin_def, end_def, lower (OCaml update_level without
  the scope test, which R3 adds), generalize, generalize_structure.
- src/tc/template.rs: Template (16 bytes), capture(root) -> Template,
  instance(template) -> Ty in one pass, copy(root) for a scheme without a
  template using a forwarding array indexed by node (no map).
- rg -n 'size_of::<Node>\(\), 16|size_of::<Template>\(\), 16' src/tc gives 2.
- rg -n 'HashMap|RefCell|Rc<' src/tc/graph.rs src/tc/level.rs
  src/tc/template.rs gives 0.

Commits, in order: graph and repr; links and the trail; levels; the
general copy; templates; the bench (benches/tc_kernel.rs, the operations
of docs/prototypes/checker-kernel).

Tests, each with a step count at 10,000:
- repr of a chain of 10,000 links: at most 2 steps a link, and a second
  repr is 1 step;
- instance of a template of 10,000 nodes: exactly 10,000 node steps and
  one per list slot;
- copy of a scheme of 10,000 generic nodes, half of them reached twice:
  one step per node, the shared ones copied once;
- lower of a 10,000-node type whose root is already at the level: 1 step;
- generalize of 10,000 nodes: one step a node, and 0 on a second call;
- restore of a speculation with 10,000 writes: 10,000 steps, and a
  speculation that is kept costs 0;
- the shapes of fixtures 2, 3, 4 and 7b of CHECKER_REDESIGN I.2.3, built by
  hand: which uses are one node.
The bench must show a same-machine comparison with the kernel of 2.2 and
attribute the difference to required data and still generic bookkeeping;
instance7's still generic bookkeeping must be at most 30 instructions.
Put the measured table in the pull request. This replaces the original
blanket +25% gate because the reference lacks required section 3.2 data.

Failure: a copy session object, a map from node to copy, recursion in
instance, a level stored anywhere but in the node, a flags summary of a
subtree.
```

### 6.3 R2: segments and the two converters

```text
Task R2: what a unit publishes, and the converters between the old shared
graph and it.

End state:
- src/tc/segment.rs: Segment (boxed slices: nodes, lists, params,
  templates, type declarations, members, export items sorted by name,
  child tables, digest), ExportItem (12 bytes), lookup(name) by binary
  search, const assert_send_sync::<Segment>.
- src/tc/publish.rs: publish(graph, items) -> Segment in one walk: every
  generic node reachable from an item goes into that item's template, in
  the order tc::template::capture gives; a node that is not generic is
  stored once per segment and referenced absolutely; paths are absolute.
- src/tc/bridge/from_old.rs: an old published unit (the SharedGraph the
  world holds) as a Segment. src/tc/bridge/to_old.rs: a Segment as the old
  graph. Both lazy, one OnceLock per unit in the world's unit slot.
- src/tc/canonical.rs prints the canonical signature of a Segment; its
  text equals types/canonical_sig.rs's for the same unit.

Commits: Segment; publish; canonical; from_old; to_old; the world slot.

Tests:
- a property test over generated signatures: canonical(to_old(from_old(g)))
  equals canonical(g), shared-node numbers included;
- on tests/tests and the runtime library, a debug check run under
  RESCRIPT_CHECKER=both that does the same for every published unit;
- step counts at 10,000: publish of 10,000 items of one node each is at
  most 4 steps an item; lookup in 10,000 items is at most 15 probes;
  from_old of a 10,000-node graph is one step a node;
- fixture 8 (super_errors_multi/checker_identity_08) by hand: two
  positions that are one node in the exporter are one node in an instance
  made from the segment.

Measurement: instructions of from_old over the application's units,
against publish_signature's (1.34% of the build).

Failure: merging equal nodes of two items; a segment that holds a pointer,
a lock or a cell; a converter that runs for a unit nobody asked for.
```

### 6.4 R3: unification and expansion

**Replaced by section 8 ("R3 as designed"): ten build slices, a skeleton
and acceptance tests. The text below is kept for the record.**

```text
Task R3: unification on the new graph. The reference is
compiler-rust/src/types/ctype.rs function by function, and
compiler/ml/ctype.ml where the two differ in form.

End state:
- src/tc/unify.rs: unify (inline test for one node, then unify_distinct),
  every case of ctype.rs's unify_types and unify_after_expansion, rows,
  objects, universal variables, polymorphic types, packages, pattern mode
  and GADT equations; moregeneral, equal, matches; subtype.
- src/tc/expand.rs: is-abbreviation as one bit of TypeDecl; the memo as
  slot 0 of a constructor's list; expand_head and its modes; the simple
  abbreviation memo (O11).
- lower gains the scope test and the expanding retry of OCaml's
  update_level.
- In Mode::Success a top-level unify opens no speculation; in
  Mode::Explain it does (compiler/ml/ctype.ml, the outer unify).
- The pair set exists only on the paths that do not link:
  rg -n 'pairs' src/tc/unify.rs shows it in the abbreviation, row and
  object cases only.

Commits: variables and the binding walk; arrows, tuples, constructors;
expansion and the memo; rows and objects; universal variables and
polymorphic types; pattern mode and equations; moregeneral, equal,
matches; subtype.

Tests:
- differential property test: generate a graph and a declaration table in
  the old representation, convert with from_old, run the same sequence of
  instance, unify, generalize on both, compare canonical forms with
  shared-node numbers and compare which operations failed. 10,000 cases in
  CI, seeds printed on failure;
- step counts at 10,000: unify of two 10,000-node equal types is at most
  4 steps a pair; binding a variable to a 10,000-node type at the
  variable's level is at most 2 steps a node, and 1 step in total when the
  type's root is below the variable's level; a second unify of the same
  pair is 0 steps;
- fixtures 1, 6b, 7, 9, 10 and 11 of CHECKER_REDESIGN I.2.3 and the
  program of CHECKER_REWRITE 2.4 idea 1 as unit tests that read the path
  of the representative.

Failure: a link written after the children; a link in the other
direction "because the result is equal"; an occurrence check skipped at
equal levels; a snapshot in Mode::Success.
```

### 6.5 R4: scopes and names

Replaced by section 9 ("R4 as designed"); the text below is the task it was
cut from.

```text
Task R4: binders, scopes and lookups.

End state:
- src/tc/scope.rs: binder arrays (type, name, location, kind, used bit),
  Scope (12 bytes), the per-namespace head table indexed by interned name,
  the undo log, open layers that point at a Segment's export table or a
  local module's member range.
- src/tc/names.rs: lookup of a value, type, module, constructor, label by
  name and by path; the warnings a lookup raises (deprecation, unused
  open) and the usage bit; unit reads logged at the lookup.
- src/types/env_log.rs and src/types/env_log_tests.rs are deleted, with
  their `mod` line in types/env.rs.
- rg -n 'HashMap|Rc<|RefCell' src/tc/scope.rs src/tc/names.rs gives 0.

Commits: binders; scopes and the undo log; open layers; paths; warnings
and usage; unit reads; delete env_log.

Tests:
- step counts at 10,000: 10,000 bindings in one scope then leaving it is
  at most 3 steps a binding; a lookup under 10,000 nested scopes is 1
  step; a lookup under 10 opened modules probes at most 10 layers and
  stops at the first younger hit; marking 10,000 uses is 10,000 steps;
- shadowing, open shadowing a local and a local shadowing an open, the
  same name in two namespaces, a qualified path through two aliases;
- under RESCRIPT_CHECKER=both, a debug check that every identifier the old
  checker resolved in tests/tests resolves to the same item here (through
  bridge::from_old for dependencies).

Measurement: the crate bench, lookup by name at most 80 instructions and
by binder at most 10.

Failure: an environment value that is cloned; a lookup by name outside
the walk's current scope; a warning raised before the walk reaches the
use (CHECKER_REWRITE 2.4 idea 5).
```

### 6.6 R5a: declarations and annotations

```text
Task R5a: type declarations, externals and type annotations.

End state:
- src/tc/decl.rs: a recursive group is entered (binders for all), then
  translated to TypeDecl rows (32 bytes) and member rows with their
  templates, then checked as Typedecl does: well-foundedness, constraints,
  variance, immediacy, unboxed, the runtime representation tables the
  backend reads.
- src/tc/walk/typetexp.rs: annotations to nodes, the type-variable scope
  of an item, CoreTypeRow (8 bytes).
- A unit that holds only these items and anything R5b will add is still
  Declined; add Declined::Expression for that and one variant per
  declaration feature you do not build here (GADT constructors, private
  rows, extensible types).

Commits: abstract and abbreviation; records; variants; recursion checks;
variance; immediacy and representation; externals; annotations.

Tests: step counts at 10,000 (a variant with 10,000 constructors, a record
with 10,000 fields, a group of 10,000 declarations: linear, at most 6
steps a member); a debug check under both mode that the Segment published
for a declaration-only unit has the canonical text of the old one.

Failure: cloning a declaration to read it; looking a declaration up by
path where an index exists.
```

### 6.7 R5b: the walk

```text
Task R5b: expressions and patterns on the success path.

End state:
- src/tc/walk/: one function per construct family, each taking
  Walk (16 bytes: Expected, scope, flags) and returning Ty. Infer returns
  the node found; Check(t) unifies where OCaml's type_expect does, in the
  same order. Rows are written at the node's index (tc/rows.rs: ExprRow
  and PatRow 12 bytes).
- Constructs: constants, identifiers, application with OCaml's argument
  order and its generalisation rule, functions, let and let rec with
  begin_def/end_def/generalize and generalize_structure exactly where
  typecore.ml has them, sequences, if, tuples, arrays, records and field
  access with type-directed label resolution, constructors, switch,
  type-annotated expressions.
- src/tc/pattern.rs and src/tc/exhaust.rs: patterns into a pool of
  handles; Parmatch ported onto it, with its warnings.
- src/tc/module.rs: structures, aliases, opens.
- Anything else is a Declined variant, decided by a pre-scan of the unit's
  syntax tree before the walk starts.

Commits: one per construct family in the order above, then patterns,
exhaustiveness, modules, the pre-scan.

Tests: step counts at 10,000 (a sequence of 10,000 expressions, an
application with 10,000 arguments, a record with 10,000 fields, a switch
with 10,000 cases over a variant: linear; say the constant); for every
construct a unit test that reads the rows; the checker_identity fixtures
that use only these constructs, as tests that compare the printed type
with the fixture's expected file.

Failure: a Vec, String or Arc per expression; a fresh variable made only
to be unified with a result; begin_def/end_def moved "because it is
equivalent"; resolving a use before the walk reaches it.
```

### 6.8 R5c: the driver takes the new road

```text
Task R5c: units the new checker covers are compiled through it.

End state:
- RESCRIPT_CHECKER=new: the driver calls tc::check_unit; on Ok it
  publishes the Segment, converts rows to the typed tree and types the
  backend reads with tc::bridge::to_old, and continues as today; on
  Err(Declined) or a type error it runs the old checker on the unit,
  reading dependencies through to_old.
- RESCRIPT_CHECKER=both compares, per unit both checkers accept: the
  canonical signature, the warnings with locations, the unit reads.
- tc_coverage.txt has real counts.

Commits: to_old for rows; the driver; both mode; the coverage file.

Tests: scripts/compare_checker_builds.py between old and new on tests/tests
and the application: no difference; a both build of each: no mismatch;
scripts/test_worker_determinism.py under new.

Measurement, in the pull request: for the units of tests/tests that are
covered, instructions of type checking under old and under new (callgrind
toggled on the two entry functions), bridge included. The gate is at most
60%. Also the instruction count of the whole build under new against old.

Failure: declining after a warning was recorded or a segment published;
running both checkers on a unit in new mode when the first one succeeded.
```

### 6.9 R6a to R6f: one family each

```text
Task R6<x>: the construct family <family> in the new checker.

Families and their Declined reasons:
(a) labelled and optional arguments with defaults, partial application,
    JSX and props records;
(b) polymorphic variants, objects, rows, the coercions between them;
(c) GADT constructors, existentials, locally abstract types, local
    constraints and their scope;
(d) functors, module types, include, first-class modules, recursive
    modules, module type of: with tc/subst.rs for the substitution OCaml's
    Subst does;
(e) exceptions and extensible types, async and await, dicts and dict
    patterns, unboxed and untagged variants, :> on records and variants,
    the built-in rewrites that are typed where consumed;
(f) interface files, and the inferred signature against the interface
    (tc/include.rs, a port of includemod.rs and includecore.rs).

End state: the Declined variants of the family are deleted from the enum;
their rows are gone from tc_coverage.txt for every corpus; no new variant
is added.

Commits: one per construct, each lowering a count.

Tests: for each construct, a unit test on rows and a step-count test at
10,000 where the construct has a list (10,000 row fields, 10,000 items in
a signature for inclusion, 10,000 functor applications in sequence:
linear); the oracle; the family's super_errors fixtures still produce
their expected files (through the old checker).

Measurement: declined units before and after per corpus; instructions per
line of type checking of the application under new.

Failure: a construct accepted that the old checker rejects (run the
family's error fixtures under RESCRIPT_CHECKER=both: the new checker must
fail each of them, at any point).
```

### 6.10 R6g: derived items

```text
Task R6g: derived items in the new checker. Read
compiler-rust/docs/DERIVED_CODECS.md ("The cheapest sound path", "The
oracle"), CHECKER_REWRITE.md 3.9, and compiler-rust/src/types/derived.rs,
which is the reference function by function.

Until this slice a unit whose parse arena has a plan
(arena.plans().item_count() > 0) is declined with Declined::DerivedItem by
the pre-scan. If the derived work on trunk has added item kinds since
(records, variants), cover every kind trunk discharges; do not decline by
kind.

End state:
- src/tc/derived.rs: discharge(item) -> Result<(), Fallback>. Per value
  obligation: one lookup by name at the current scope (tc/names.rs, with
  its usage mark, deprecation warning and unit read), one instance of the
  value's template, one unify with the obligation's skeleton built in the
  unit's graph. Per type obligation: the path resolved to a TypeDecl row,
  its members read by index. Per binding: one function type, one binder.
- The whole item runs under one speculation, in Mode::Success and
  Mode::Explain alike. On Fallback the speculation is restored, the
  warnings and usage marks recorded since the item began are taken back,
  and the item's general form is typed by the walk; nothing of the failed
  discharge is observable.
- Two dense tables indexed by the plan's BindingIdx and ObligationIdx: the
  binder of each binding (4 bytes) and what each obligation resolved to
  (4 bytes, the reference an ExprRow carries). size_of tests for both. No
  ExprRow is written for a discharged item.
- tc/bridge/to_old.rs fills the old typed arena's derived tables from
  them, so raw_lambda/convert/derived.rs is untouched.
- rg -n 'DerivedItem' src gives 0; its rows are gone from tc_coverage.txt.
- rg -n 'HashMap|Vec<' src/tc/derived.rs shows only the two tables and the
  reused skeleton-variable buffer.

Commits: the tables; value obligations; type obligations; bindings and
generalisation (begin_def, end_def, generalize where typecore.ml's
type_let has them); the fallback; to_old; delete the Declined variant.

Tests:
- step counts at 10,000: an item with 10,000 value obligations is at most
  3 steps an obligation; a skeleton of 10,000 nodes is at most 2 steps a
  node; a failing last obligation restores in one step per write made;
- a unit test per fixture shape that the fallback leaves no warning, no
  usage mark and no link behind;
- RESCRIPT_DERIVED_PATH=check RESCRIPT_CHECKER=new rescript build
  tests/ppx_spice: no difference reported; the same under
  RESCRIPT_CHECKER=both: no mismatch;
- the 14 fixtures of tests/build_tests/super_errors_derived produce their
  expected files with RESCRIPT_CHECKER=new, with RESCRIPT_DERIVED_PATH
  unset and with general, byte for byte.

Measurement: declined units with a plan before and after on every corpus;
instructions of type checking of tests/ppx_spice under old and under new.

Failure: typing a derived body when its obligations discharge; reporting
a diagnostic from the discharge instead of from the general form;
treating a Fallback as a failure of the unit; knowing anything about
Spice in tc/.
```

### 6.11 R7: the default flips

```text
Task R7: RESCRIPT_CHECKER defaults to new.

End state:
- rg -n 'Declined' src gives 0; tc_coverage.txt and scripts/tc_coverage.py
  are deleted; src/tc/bridge/from_old.rs is deleted (no unit is published
  by the old checker any more: it runs only for a unit that has an error,
  and such a unit publishes nothing).
- The old checker is reached from two places:
  rg -n 'type_structure\(' src/driver.rs shows the failing-unit rerun and
  the tooling entry points only.

Commits: the default; delete Declined; delete from_old.

Gate, measured by you and pasted: on the application, instructions of type
checking with its surroundings (the functions of CHECKER_REWRITE 1.4) per
source line, at most 24,000; the CI instruction count of tests/tests down
by at least 12% against the base. If either fails, do not flip: profile
with docs/prototypes/checker-attribution, report the top three items, stop.

Failure: flipping with a unit still declined in any project under tests/.
```

### 6.12 R8a to R8c: the explaining mode

```text
Task R8<x>: diagnostics from the new checker.

(a) Mode::Explain: the speculation around a top-level unify, traces,
    clash sites passed down the walk as a Copy value of at most 16 bytes
    in total with Walk, tc/print.rs (a port of printtyp.rs: names of
    variables, weak variables, the loop marks), type clash messages
    through driver/type_clash.rs.
(b) Every other error of expressions and patterns, one TypeCoreError
    variant per commit, following tests/ERROR_VARIANTS.md.
(c) Declaration, module and inclusion errors. Tooling entry points
    (typecheck_structure_for_tooling, typecheck_signature_for_tooling)
    check with the new checker and take their typed tree from
    tc::bridge::to_old.

End state after (c): src/types/typecore.rs, typemod.rs, includemod.rs,
includecore.rs, parmatch.rs and printtyp.rs do not exist; types/ctype.rs
holds only what rg shows the backend and genType call; RESCRIPT_CHECKER
accepts new only.

Tests: scripts/test_error_output_parity.sh; the super_errors and
super_errors_multi suites; for (a) a step-count test that a unit of 10,000
items that fails in its last item is checked exactly twice; a test that
every fixture fails in Mode::Success too.

Measurement: a failing unit against the same unit made to pass: at most
2.2 times the instructions.

Failure: an error text assembled on the success path; a fixture's
expected file changed.
```

### 6.13 R9a to R9c: readers on rows

```text
Task R9<x>: a reader of the checker's results reads rows and TypeFacts.

(a) raw_lambda/typeopt.rs and raw_lambda/convert.rs (THREE_TREES T9);
(b) raw_lambda/matching.rs, switch.rs and the pattern pool (T10);
(c) genType and the unit reads (T11, T3).

End state: (a) rg -n 'typedtree::' src/raw_lambda/convert.rs
src/raw_lambda/typeopt.rs gives 0. (b) the same for matching.rs and
switch.rs. (c) rg -n 'to_old' src/driver.rs shows the tooling entry points
only, and the files listed in CHECKER_REWRITE 5.3 row R9 do not exist.

src/tc/facts.rs: the TypeFacts trait, about twenty methods, each with its
cost in the doc comment, each O(1) or one expansion.

Tests: JavaScript, stdlib and genType parity; a step-count test that
converting a function of 10,000 expressions reads each row once.

Gate for (c), measured and pasted: type checking with its surroundings at
most 20,000 instructions per source line on the application.

Failure: a TypeFacts method that walks a type; a reader that looks a name
up again.
```

### 6.14 R10: tooling, and the last deletions

```text
Task R10: editor analysis reads rows; the bridge and the switch go.

End state: src/types/typedtree.rs, tast_arena.rs, tast_iterator.rs and
sexp_typedtree.rs do not exist; src/tc/bridge does not exist;
rg -n 'RESCRIPT_CHECKER|TypedArena|TypeExprRef|TypeContext' src ../scripts
../rewatch gives 0; -dtypedtree prints rows.

Commits: one per analysis file (process_cmt.rs, process_extra.rs,
hover.rs, ...), arm by arm; then the dump; then the deletions.

Tests: make test-analysis; the watch-mode tests of rewatch.

Failure: a typed tree rebuilt under another name.
```

## 7. The ceiling

### 7.1 Instructions per source line, item by item

The application, one worker. "Today" is measured (1.2, 1.4). "Design" is
what section 2.3 derives. "Cautious" doubles every figure that rests on
the kernel and adds half to every estimate, which is what prototype 4.1
says an unconfirmed figure deserves. The label says what the design figure
rests on.

| Item | Today | Design | Cautious | The design figure is |
|---|---:|---:|---:|---|
| Unification and the journal | 8,297 | 1,930 | 3,860 | extrapolated from the kernel and counted shapes; sizes assumed. 865 of the reduction is **measured** in situ (4.2) |
| The walk | 5,411 | 4,200 | 4,900 | extrapolated from CHECKER_REDESIGN K.4 (a measured 54% of one family's allocation and copying) to 4,960, then estimated |
| Environment lookups | 5,279 | 570 | 1,150 | extrapolated from the kernel and H.2.11's operation counts; layers per lookup assumed |
| Loading dependencies | 2,996 | 600 | 1,200 | estimated |
| Substitution copies | 1,537 | 250 | 550 | estimated |
| Instantiation | 4,341 | 600 | 1,900 | extrapolated from the kernel. The cautious figure is what prototype 4.1 **measured** a templated node to cost in today's storage |
| The allocator | 3,463 | 500 | 1,000 | estimated |
| Expansion | 2,474 | 800 | 1,200 | estimated; expansions not counted |
| Levels and generalisation | 2,042 | 550 | 1,100 | extrapolated from the kernel and counted visits |
| Patterns and exhaustiveness | 1,478 | 1,000 | 1,250 | estimated |
| Warnings and usage | 1,382 | 400 | 700 | estimated |
| Declarations | 1,017 | 700 | 850 | estimated |
| Modules, disambiguation, annotations, error preparation | 943 | 750 | 850 | estimated at 80% |
| **`type_structure`** | **40,656** | **12,850** | **20,510** | |
| Interfaces, and the implementation against its interface | 1,367 | 600 | 900 | estimated: the same mechanisms |
| Publication | 1,380 | 500 | 700 | estimated: one export walk (CHECKER_REDESIGN J.6) |
| Per-unit setup | 396 | 60 | 100 | estimated: a reset of a dozen vectors |
| Per-unit teardown | 1,200 | 150 | 300 | estimated: no destructors in the pools |
| **The checker with its surroundings** | **45,022** | **14,160** | **22,510** | |
| Unit reads | 2,607 | 300 | 600 | estimated (THREE_TREES T3) |

The budget is 18,000 to 22,000. (The rows of today add up to 44,999; 1.4's
45,022 uses the inclusive count of `type_structure`, 0.06% above the
toggled one.)

- **The design reaches about 14,200 instructions per line**, 31% of
  today, if every figure holds.
- **The cautious reading is about 22,500**, just above the budget's upper
  edge.
- What is **measured in situ** of that reduction of 22,500 to 30,900 is
  865 (the journal) plus 345 a line that a template saves on today's
  storage (4.1): 4%. Everything else is a kernel measurement multiplied by
  a count, a quoted measurement extended, or an estimate.

So the plain answer: the design is under the budget on paper and at its
upper edge when the paper is distrusted, and this document has not proved either
in a checker. The proof is slice R5c (covered units at 60% or less, bridge
included) and slice R7 (24,000 with the bridge still there). R9 removes
the bridge: about 3% of a build, 3,000 a line, which is why R7's gate is
24,000 and R9's is 20,000.

### 7.2 What stands between the design and the budget

Nothing in the contract. Three things in the engineering:

1. **Names are 9,812 a line today and 1,420 in the design, and none of it
   is prototyped.** It is the largest single reduction (8,400) and the one
   earlier attempt at a different environment (CHECKER_REDESIGN H.2.11)
   came out 1.9 times worse than what it replaced. The design differs in
   kind (no versioned environments, binders as indices, results stored
   per syntax node), but R4's bench gate and R5c's measurement are the
   first evidence there will be.
2. **A mechanism measured alone does not deliver its number when the rest
   stays** (4.1: predicted 4% to 5% of the checker, measured 0.6% to
   0.9%). The design's figures are for all of it together. Until R5c
   nothing can be measured together.
3. **The beside period costs.** Two converters, a bridge to the typed tree
   for the backend, and a second check of failing units through the old
   checker until R8. None of it is on the default path before R7.

### 7.3 Items that cannot go lower, and the observation that holds them

| Item | Floor | Held by | Fixture |
|---|---|---|---|
| Instantiation | one copied node per generic node per use: 4.8 M nodes on the application, 27 instructions each on the kernel, about 200 a line | O4 and O5: every use of a generalised binding is its own copy, with the scheme's sharing | `checker_identity_03_generalized.res`, `checker_identity_07b_sharing.res` |
| Unification of two identical types without variables | 877,885 on the application cannot be answered by comparing handles: each links a pair of nodes and lowers levels; about 350 a line on the kernel | O2 and O10: the link decides the printed name, the level decides a later copy | `alias_name_follows_unification.res`, `checker_identity_02_annotated.res` |
| Level updates and generalisation of types without variables | 63% of level-update visits and 89% of generalisation visits are of such nodes; they must be written | O10 | `checker_identity_02_annotated.res` against `checker_identity_04_local.res` |
| Lookups in the order of the walk | a use is resolved when the walk reaches it, not in a pass before | O15 | `fun_return_poly1.res` |
| A second check of a failing unit | once per failing unit | O16: the message prints the types as they stood | any type clash fixture |

Together these floors are about 900 a line of the design's 14,200.

### 7.4 What could not be measured

- The profile-guided build (what ships), wall time, cycles, cache misses,
  memory, and more than one worker. Every number here is instructions with
  one worker on the fat-LTO build.
- How many pairs of nodes a unification visits and how many expansions
  run: the counters count top-level calls. The figures of 2.3 item 1
  assume two pairs for an identical variable-free unification.
- How many opened layers a lookup probes.
- The kernel with abbreviations, rows or two tiers of handles; 40% to 50%
  was added for them without a measurement.
- The invariant the pruned occurrence check relies on (a node's level is
  never below its children's) is argued from where `update_level`,
  `generalize` and `instance` write levels, not checked on a build. Slice
  R3's differential test is where a counterexample would show; if there
  is one, the occurrence check walks the whole type as today and item 1
  of 2.3 loses that part.
- The kernel's walks recurse: a type 10,000 nodes deep overflows a 2 MB
  stack in its tests, which run on a larger one. The checker's walks over
  types need an explicit stack; its cost is not in the kernel's figures.
- The OCaml compiler was not run for this document. The program of 2.4
  idea 1 was compiled with the Rust compiler of trunk only; the fixtures
  of 2.1 carry expected files written by the OCaml compiler.
- Whether O11 is observable: R0 tried the five program shapes in section 2.1
  against a reference build with the copy-time nullary memo lookup disabled;
  none isolated it. This does not prove that no program can.
- That the success mode fails every `super_errors` fixture (4.2).
- Whether storing templates per exported item loses anything: two items of
  one signature that share a generic node are stored as two nodes. No
  operation was found that relates the generic nodes of two items without
  copying each (every use instantiates; `include` and functor application
  copy item by item), but that is an argument, not a test. Slice R2's
  property test and fixture 8 are where it would show.
- The share assigned by the proportional rule in section 1 (34%) is an
  attribution, not a measurement of each call.

### 7.5 Questions for the owner

Each is an observation of the contract that the design keeps. Listed with
what dropping it would buy; the design does not assume any of them.

1. **Must the printed name of a type follow unification (O1, O2, O6), and
   must the comparison of O8 stay generic when a node was linked to an
   abbreviation?** This is the observation that forces one node per
   occurrence. Without it (names from the declaration or the annotation,
   immediacy read after expansion) variable-free types could be interned:
   69% of the nodes `instance` copies, the 877,885 identical unifications,
   63% of level-update visits and 89% of generalisation visits would
   become a handle compare or nothing. On the design's figures that is
   about 1,300 a line (9%); on today's it was the 4% to 6% of a build that
   CHECKER_REDESIGN F.10 claimed. It changes diagnostics text
   (`alias_name_follows_unification.res` would print `int => int`),
   signatures, genType output and, for O8, generated JavaScript
   (`checker_identity_comparison.res` would emit `a > "Green"`).
2. **Must the warnings printed before a type error be exactly those the
   OCaml checker had met when it failed (O15)?** If a failing unit could
   print all of its lookup-time warnings, or none, names could be resolved
   in a pass before typing. That buys no instruction on the success path;
   it would let the name pass of large units run apart from typing and
   simplifies R4 and R8.
3. **Must a type clash print the two types as they stood at the failed
   unification, with the partial links made before it failed (O16)?** If
   the state before the failing unification is acceptable, the explaining
   mode needs no exact replay of a partial unification. No instruction on
   the success path; it removes the riskiest part of R8a.
4. **Does the budget of 18,000 to 22,000 count the surroundings of 1.4
   (publication, interfaces, setup, teardown: 4,343 a line today) and the
   unit reads (2,607)?** This document counts the first and lists the
   second apart.
5. **Is a transition in which a failing unit is checked a second time by
   the old checker (R5c to R8), and the backend reads a converted typed
   tree (R5c to R9, about 3% of a build), acceptable?** The alternative is
   to port the readers and the diagnostics before the default flips, which
   moves the first measured saving on the default path from R7 to R9.
6. **May O11 be dropped if R0 finds no program that shows it?**

## 8. R3 as designed

Section 6.4 gave R3 as one slice of eight commits. It is replaced by this
section: ten build slices, a skeleton (`src/tc/{unify,expand,rows,relate}.rs`,
every body `todo!("R3x")`), a differential harness (`src/tc/differential.rs`)
and acceptance tests (`src/tc/r3_tests.rs`). A builder fills bodies in. It
does not change a signature, a stated cost or a test; when one cannot be met
it stops and reports a reproduction.

### 8.1 The slices

| Slice | Builds | File | Depends on | Can be built beside | Lines |
|---|---|---|---|---|---:|
| R3a | The unification entry, the two modes, the binding walk, the occurrence checks, arrows, tuples, constructors of one type, `undo_compress` | `unify.rs` | R1, R2 | R3b | 600 |
| R3b | Declaration facts by type index, expansion, both memos and their cleanup, the memo-aware `instance` and `copy`, `restore` | `expand.rs` | R1, R2 | R3a | 600 |
| R3d | The level walk with scopes and the expanding retry, `lower_args` | `expand.rs` | R3b | R3a | 300 |
| R3c | Abbreviations in unification: `unify2`, `unify3`, the relink to the original node, the recursion repair, `unify_var` | `unify.rs` | R3a, R3b, R3d | nothing | 450 |
| R3k | In the explaining mode a lowering whose retry clashes keeps its levels and adds the escaping pair to the trace (8.6, decision 14) | `expand.rs` | R3d | R3m | 60 |
| R3m | Inherited memo entries: a constructor with arguments copied by an expansion links to the expanding node of the same type, through a pool of rows found by slot 0 (8.6, decisions 16 and 26) | `expand.rs` | R3b | R3k | 150 |
| R3e | Objects and fields; mutability cells as nodes and their duplicate at an instance; two polymorphic types without variables (8.6, decision 27) | `rows.rs`, `unify.rs`, `expand.rs` | R3c, R3m | nothing | 600 |
| R3f | Polymorphic variant rows: the references of `Reither` fields as slots of the variant node, `unify_row`, `unify_row_field` (8.6, decision 34) | `rows.rs` | R3e | R3g | 600 |
| R3n | The references of a copied variant row: shared when the row variable is, new otherwise (8.6, decision 34) | `rows.rs`, `expand.rs` | R3e, R3f | R3g | 150 |
| R3g | Universal variables and polymorphic types with variables: the scopes, `unify_univar`, `enter_poly`, the escape test, `occur_univar`, PR#6744 in `unify_row_field` (8.6, decisions 49 to 51; 8.8) | `rows.rs` | R3e, R3f, R3n | R3p | 600 |
| R3p | Packages: the merge of two name lists, completed through `PackageDecls` (8.6, decision 52; 8.8) | `rows.rs` | R3e | R3g | 150 |
| R3h | Pattern mode: state, equations, `reify`, the binding walk of pattern mode, the arms without a backtrack, the fixed-row rule of `copy_refs` (8.9). Merged (pull request 356; `tc::` 298 passed, 7 ignored for R3r) | `rows.rs`, `unify.rs`, `expand.rs` | R3n, R3g | R3i, R3j, R3q | 700 |
| R3r | Pattern mode: `mcomp`, the two arms that try and fall back, the package fallback, a total `duplicate` (8.9). Merged (pull request 361; `tc::` 306 passed, none ignored) | `rows.rs`, `unify.rs` | R3h | R3i, R3j, R3q | 450 |
| R3q | `instance_poly` and `instance_label`: the copy that goes through free universal variables without sharing (`copy_sep`), and the fixed-row rule of `copy_row` only it reaches (8.6, decision 47; 8.10). Merged (pull request 370; `tc::` 324 passed, none ignored) | `rows.rs` | R3n, R3g | R3h, R3i, R3j | 500 |
| R3s | The ambiguity of GADT instances: tracing, the instance sets and the three places of the kernel that read them; a nullary constructor's own memo while tracing (8.6, decisions 72 and 97 to 112; 8.11). Merged (pull request 382; `tc::` 341 passed, none ignored) | `unify.rs`, `expand.rs`, three lines of `rows.rs` | R3r | R3i, R3j | 350 |
| R3i | `moregeneral`, `equal`, `matches`: one loop for `moregen` and `eqtype` on the frames of unification, `rigidify`, the renaming as a table (8.6, decisions 113 to 118; 8.12). Issued in the tenth skeleton turn: 23 bodies, 9 ignored tests, a prompt in 8.4 | `relate.rs` | R3s | nothing | 900 |
| R3j | Subtyping without the declaration-directed coercions: `subtype` and `force_subtype` as a loop of its own with a collection the caller owns, `enlarge_type` with the visited list as a dense table (8.6, decisions 119 to 126; 8.13). Issued in the eleventh skeleton turn: 27 bodies, 11 ignored tests, a prompt in 8.4; its harness operations are not made | `relate.rs` | R3s, R3i | nothing | 1,000 (the prototype: 908) |
| K2 | The hot paths of unification, no behaviour change (8.7) | `unify.rs` | R3c | every slice above | 150 |

State after the second skeleton turn (kept for the record; the third
turn's state follows it). Merged: R3a, R3b, R3d, R3c, and K1
(the kernel's hot paths, TC_KERNEL_R3.md). Designed in the second turn, with
acceptance tests that are ignored until the slice is built: R3k (with its
prompt in 8.4), R3m (its rule and test; its layout is still open, 8.6,
decision 16), and the generated-case acceptance tests of R3e and R3f (the harness prints
objects, fields, variants, polymorphic types and universal variables on
both sides; `Extras::from_segment` is built, because the harness needs the
pools to print). Designed as text with a build prompt: K2 (8.7). Not done
in the second turn: the hand-built acceptance tests, step relations, size
tests and build prompts of R3e and R3f, and all of R3g to R3j; 8.6 ends
with what the second turn learned that their designer needs. R3i and R3j
now depend on R3f: `matches` unifies, and a generated program for them has
variants. `differential::tests::ignored_tests_name_the_slices_they_reach`
checks, from the text of every ignored test, that it says which slices it
reaches and reaches none that is built after its own.

State after the third skeleton turn. Merged: R3a, R3b, R3d, R3c, K1.
Building beside this turn: R3k and K2. Designed in this turn, with
acceptance tests that are ignored until the slice is built and a prompt in
8.4:

| Slice | Decision | Tests | Run in this turn |
|---|---|---|---|
| R3m | 26 | five ignored (three hand-built, two against the old checker), two that run today | every ignored test passed with a prototype of the five bodies, which is not on trunk |
| R3e | 27 | eleven ignored (nine hand-built, two against the old checker), three that run today | the old checker's side of every fact it can show; the hand-built tests were not run |

R3m's line count is 150 and its file `expand.rs`. R3e grew to 600 lines:
it owns the duplicate of mutability cells at an instance and at a copy
(`rows.rs`, the pass of `expand.rs`), the three frames of `unify_fields`
and two edits of the binding walk in `unify.rs`, and the arm of two
polymorphic types without variables (decision 22). R3f is not designed
(decision 28): its row in the table stands, its generated-case test
exists, and it has no prompt. R3g to R3j are not started.

State after the fourth skeleton turn (trunk `c4e9326eba`). Merged: R3a,
R3b, R3d, R3c, K1, R3k, R3m, K2. Designed with tests and a prompt, not
built: R3e (third turn), and in this turn:

| Slice | Decision | Tests | Run in this turn |
|---|---|---|---|
| R3f | 34 | ten ignored (nine hand-built, one of fixed cases against the old checker), three that run today (`rows::tests`) | the old checker's side of every fact it can show (five tests that run today); the ignored tests were **not** run: no prototype of R3f was built |
| R3n | 34 | one ignored (fixed cases and 30,000 generated cases against the old checker) | the old checker's side; the new side was not run |

R3f was cut in two where the work divides: R3f is everything a
unification does to a row, R3n is what a copy does to the references of
one (a slice name has three characters, which the check of ignored tests
reads, so the second part is R3n and not "R3f-2"). The generated cases
are R3n's acceptance, not R3f's: every generated sequence copies, and a
copy of an opened row is wrong until R3n. R3f is accepted on its
hand-built tests and on fixed cases that make no copy. R3g to R3j are
not designed; R3g was not started in this turn.

State after the fifth skeleton turn (trunk `de646dffcb`). Merged: R3a,
R3b, R3d, R3c, K1, R3k, R3m, K2, R3e, R3f, R3n, K3, K4. `cargo test --lib
tc::` on that trunk: 236 passed, 0 ignored. The decisions of the reviews
between the two turns are 35 to 46 of 8.6. What the fifth turn designed
is listed after them, in 8.6 ("Decided in the fifth skeleton turn").
Designed in the fifth turn with tests and a prompt, not built:

| Slice | Decisions | Tests | Run in this turn |
|---|---|---|---|
| R3g | 49, 50, 51 | twelve ignored: nine hand-built and a step test in `r3_tests.rs`, the fixed cases and 20,000 generated cases against the old checker in `differential.rs`; thirteen that run today (the harness and the old checker's side, decision 49; `sizes_of_universal_variables`) | all twelve passed against a prototype of the five bodies (about 270 lines), which was removed before the commit; the tree as committed has `todo!("R3g")` in each |
| R3p | 52 | three ignored, hand-built with a supplier written in the test file | all three passed against a prototype of the two bodies (about 80 lines), removed before the commit |

Packages are R3p and not part of R3g: no generated case can judge them
(the differential program has no module types), their one caller is an
arm that is already wired, and they ask the declarations three questions
that R5a answers. R3h was not started in this turn.

State after the sixth skeleton turn (trunk `61f7f41292`). Merged: every
slice above R3h in the table, R3g and R3p included (built as designed;
what their reviews put on record is decisions 53 to 57 of 8.6), and K1 to
K4. `cargo test --lib tc::` on that trunk: 265 passed, 0 ignored. At the end
of the sixth turn: 281 passed, 15 ignored (ten for R3h, five for R3r). Without a design
before this turn: R3h, the `instance_poly` slice (R3q: a slice name has
three characters), R3i and R3j. What the sixth turn did is listed in 8.6
("Decided in the sixth skeleton turn").

| Slice | Decisions | Tests | Run in this turn |
|---|---|---|---|
| R3h | 61 to 67, 69, 71 | ten ignored in `r3_tests.rs`: nine hand-built and the step test `pattern_mode_at_ten_thousand` | none: no prototype was made; they compile against the skeleton and the check of the ignored tests passes. The harness and the old checker's side (decisions 61, 62) are nine tests that run today |
| R3r | 63, 68, 70 | five ignored: three hand-built and `mcomp_at_ten_thousand` in `r3_tests.rs`, the fixed cases and 12,000 generated cases in `differential.rs` (`pattern_plan_agrees_on_generated_cases`) | none, as above |

After the sixth turn: designed and not built, R3h and R3r (8.9); without
a design, R3q, R3i, R3j and the ambiguity levels of GADT instances
(decision 62).

State after the seventh skeleton turn (trunk `cfd8f200b4`). Nothing was
merged between the two turns. `cargo test --lib tc::` before: 281 passed,
15 ignored; after: 282 passed, 19 ignored (twelve for R3h, seven for
R3r). What the seventh turn did is listed in 8.6 ("Decided in the
seventh skeleton turn").

| Slice | Decisions | Tests | Run in this turn |
|---|---|---|---|
| R3h | 61 to 67, 69, 71 as rewritten; 76 | twelve ignored in `r3_tests.rs` | all twelve passed against a prototype of the bodies; what the run changed is in 8.9, "What the prototype corrected" |
| R3r | 63, 68, 70 as rewritten; 79 | seven ignored: six in `r3_tests.rs`, `pattern_plan_agrees_on_generated_cases` in `differential.rs` | all seven passed against the prototype; the generated cases with the seeds of decisions 77 to 79 listed |
| R3q | 8.10 | none | designed as text only |
| R3s | 72; 8.11 | none | designed as text only |

The prototype (about 1,090 lines: 700 in `rows.rs`, 380 in `unify.rs`,
12 in `expand.rs`) is not in the tree: it is over the size at which it
would have been committed as a patch. Built in the seventh turn, as a
correction of built code: the name of a row below its scope (decision
75).

State after the eighth skeleton turn (trunk `aad575e98d`). Merged
between the two turns: R3h (pull request 356) and R3r (pull request
361), so pattern mode of unification is built. `cargo test --lib tc::`
before: 306 passed, none ignored. The only `todo!` bodies under
`src/tc` before the turn are the six of `relate.rs` (R3i, R3j). What
the eighth turn did is listed in 8.6 ("Decided in the eighth skeleton
turn"); the state of R3q and R3s, and the count after, are at the end
of that list.

| Slice | Decisions | Tests | Run in this turn |
|---|---|---|---|
| R3q | 91 to 96; 8.10 | ten ignored in `r3_tests.rs`: nine hand-built and the step test `instance_poly_at_ten_thousand`; two that run today (`rows::tests::sizes_of_the_instance_of_a_polymorphic_type`, `template::tests::a_session_of_two_roots_shares_between_them`) | all ten passed against a prototype of the twelve bodies (429 lines), which is not in the tree; three of the four shapes of the step test were seen to fail with their structure broken. No generated case: the harness has no operation for it |
| R3s | 97 to 104; 8.11 | none | nothing: the section is corrected in place and its decisions are written; no skeleton, no test, no prototype, no prompt. NOT issued |

State after the ninth skeleton turn (trunk `b877a4814` at its start,
`8b9bf5a8e` merged during it). Merged between the two turns: nothing;
during the turn: R3q (pull request 370). `cargo test --lib tc::`
before, on `b877a4814`: 314 passed, 10 ignored (the ten of R3q, not
yet merged there); on trunk with R3q: 324 passed, none ignored. What
the ninth turn did is decisions 105 to 112 of 8.6 and section 8.11 as
rewritten; its count after is at the end of that list.

| Slice | Decisions | Tests | Run in this turn |
|---|---|---|---|
| R3s | 97 to 112; 8.11 | thirteen ignored: eleven hand-built and the step test `instance_sets_at_ten_thousand` in `r3_tests.rs`, `instance_plan_agrees_on_generated_cases` in `differential.rs`; one that runs today (`old_checker_refuses_a_member_below_its_scope`) and the size tests | all thirteen passed against a prototype of the 25 bodies (about 270 lines of code), which is not in the tree; each of the four shapes of the step test and three hand-built tests were seen to fail with their structure broken (decision 112) |

State after the tenth skeleton turn (trunk `f37ab8a73`). Merged between
the two turns: R3s (pull request 382). `cargo test --lib tc::` before:
341 passed, none ignored (seen: 1,166 seconds). After, on the skeleton:
342 passed, 1 failed, 8 ignored was seen (the check of the ignored
tests found one of the new ones without `Reaches:` in its doc comment;
corrected, and the check passes), so 343 passed and 8 ignored is what
the skeleton reads; with the prototype in place and the ignored tests
included, 351 passed, none failed, none ignored was seen (1,181
seconds). What
the tenth turn did is decisions 113 to 118 of 8.6 and section 8.12.

| Slice | Decisions | Tests | Run in this turn |
|---|---|---|---|
| R3i | 113 to 118; 8.12 | nine ignored: five hand-built and the two step tests `relations_at_ten_thousand` and `relations_over_ten_thousand_fields_and_tags` in `r3_tests.rs`; `relation_plan_agrees_on_generated_cases` (25,000 cases) and `a_wrong_answer_of_a_relation_is_reported` in `differential.rs`; two that run today (`the_rigid_expansion_is_public_and_adds_the_chain`, `old_side_of_the_relation_plans_is_not_vacuous`) and the size test | all nine passed against a prototype of the 23 bodies (803 added lines, comments included), which is not in the tree; the fifth shape of `relations_at_ten_thousand` was seen not to end without the table of pairs. The whole filter with the first prototype in place: 351 passed, none ignored; with the corrected one and the ninth test, the count is in the pull request |
| R3j | none | none | nothing: not designed |

State after the eleventh skeleton turn (trunk `265ff7e37`). Merged
between the two turns: pull request 396 (a listed seed must fit its
class); R3i is being built. `cargo test --lib tc::` before: 344 passed,
0 failed, 9 ignored (seen: 1,073 seconds). What the eleventh turn did
is decisions 119 to 126 of 8.6 and section 8.13; the counts after are
in the pull request (404).

| Slice | Decisions | Tests | Run in this turn |
|---|---|---|---|
| R3j | 119 to 126; 8.13 | eleven ignored in `r3_tests.rs`: nine hand-built and the two step tests `subtyping_at_ten_thousand` and `enlarging_at_ten_thousand`; two that run today (`the_table_keeps_both_upper_bits_of_a_variance` and the size test of `relate.rs`) | all eleven passed against a prototype of the 27 bodies (908 lines of code), which is not in the tree; one was changed first (`the_enlarged_type_of_a_coercion_without_a_source`, decision 125); shape 10 of the first step test, the shared type of the first and the hand-built test of `enlarge_type` were seen to fail with their structure broken. No generated case: the harness has no operation for it (decision 126) |

The ignored tests are checked mechanically
(`differential::tests::ignored_tests_name_the_slices_they_reach`): each
names the slices it reaches, reaches its own, and reaches none that is
built after its own; what a test reaches is read from its text (a plan
bit with a tier, a hand-built object, a type marked `INHERITS`, a call of
a method whose body is `todo!`). It counts the `#[ignore` lines and pins
no number.

Each slice is one pull request that removes the `ignore` of its own tests
and the `#[allow(...)]` of a module once the module has no `todo!` left.
R3a to R3d have their acceptance tests in full in this pull request. R3e to
R3j have signatures and prompts; their tests are the first commit of the
slice (an extension of the harness's program generator, proven not vacuous
on the old side as `old_side_of_the_full_tier_is_not_vacuous` does) and are
reviewed before the implementation commit is opened: question 5 of 8.5.

### 8.2 Decisions

Each is settled by a test that runs on the old checker today, by a probe
with a release build of trunk (`--dump sig`), or by the OCaml source.

**1. Instance sharing.** Publication identity (R2) certifies the exporter's
sharing in the canonical text. That an *instance* built from a segment
shares exactly what the old checker's instance shares is proven by
`r3_tests::instance_from_a_segment_shares_what_the_old_instance_shares`
(runs today) and by the kernel tier of the harness
(`differential::kernel_tier_agrees_on_generated_cases`, 2,400 generated
cases, runs today): the old checker instantiates a value of the
internalized unit, the new graph instantiates the same value's template of
the converted segment, and the two are compared in a form that numbers
every node at its first visit across all operands of the case. R3b owns
keeping it true for the memo-aware instance
(`memo_aware_instance_shares_what_the_old_instance_shares`, the `Expand`
tier).

**2. Two abbreviations (the abbreviation case of O5).** `unify2` expands
both heads; `unify3` then links the *expansion* of the chosen side to the
*original* node of the other (`link_type t1' t2`,
compiler/ml/ctype.ml:2299 and 2331). The abbreviation node of the chosen
side is not linked: two nodes, two names. Probe (old checker, canonical
signature, `same = (x, y) => if true { x } else { y }`):

```text
nullary     (x: a, y: b) => (same(x, y), x, y)   tuple(&4(a), @4, &5(b))
nullary_rev (x: a, y: b) => (same(y, x), x, y)   tuple(&4(b), &5(a), @4)
param       pa<string>, pb<string>               tuple(&6(pa<..>), &8(pa<..>), &10(pb<..>))
plain       (x: a, y: int), both orders          tuple(&4(a), @4, &5(int))
```

The fixture is `r3_tests::old_checker_abbreviation_pair_keeps_two_nodes`
(runs today); on the new graph it is
`fixture_10_two_abbreviations_stay_two_nodes` (R3c), which also covers
abbreviations with an argument, where the existing fixture had predefined
types only.

**3. O11 is observable.** R0 found no program; this is one. After one
application of `f`, a later instance of `f` in the same definition has both
its nullary nodes linked to the result node of the first instance:

```text
let f = (x: N.t) => x            (module N = M, or `type a = int` for N.t)
let twice = j => (f(j), f)       &0((&1(N.t)) => &2(tuple(&3(N.t), &4((@3) => @3))))
let noapp = (f, f)               nothing shared
let twoapps = (j, k) => ...      &0((&1(N.t), &2(N.t)) => &3(tuple(@2, @2)))
type p<'x> = ('x, int): twicep   nothing shared
```

The chain: the application runs `lower_args` on the callee's instance
(types/ctype.rs:11682), which expands the head of the result type; the
expansion of a nullary constructor is memorized in the memo all nullary
constructors share (`simple_abbrevs`, compiler/ml/ctype.ml:197-202) with
that node as the abbreviated type; a later copy of a nullary constructor of
the same type finds it (`find_repr`, ctype.ml:720) and becomes a link to it
(ctype.ml:782). The memo lives until the next `cleanup_abbrev`. It is not
specific to module aliases: a plain nullary abbreviation shows it. A
constructor with an argument never shows it, because its memo is the
node's own. Test on the old checker:
`old_checker_nullary_memo_shows_in_the_canonical_signature` (runs today).
Acceptance on the new graph:
`a_copy_of_a_nullary_constructor_links_to_the_memorized_node` (R3b) and
`an_application_memorizes_the_result_node` (R3d).

**4. What R1 left.** The copy-time lookup is R3b: `Checker::instance` and
`Checker::copy` in `expand.rs`. The memo of nullary constructors is one
16-byte row per type index, live by a generation number; `Memo::live`
counts live rows. With `live == 0` the instance is R1's and costs R1's
instructions plus one load and one untaken branch: the gate is
instance1/3/5/7 through `Checker::instance` at most 143/223/308/330
instructions (R1: 140/220/305/327), measured with the `tc_kernel` bench as
TC_KERNEL_R1.md describes, and in steps
`instance_with_an_empty_memo_costs_what_r1_costs` (equal to R1's count).
With a live memo it costs one row load and one compare more per nullary
constructor copied; that number is reported, not gated. The scope checks
are R3d: `Checker::lower`. `TypeTable::scoped` counts the types that have a
scope; with 0 the walk is R1's `lower` plus one compare
(`lower_without_scopes_costs_what_r1_costs`: the same step count).

**5. Modes.** `Mode::Success` and `Mode::Explain` of the graph are the old
checker's `CheckMode::Success` and `CheckMode::Explain`
(types/context.rs:783), with the same rule as `unify_takes_snapshot`
(types/context.rs:1609): a top-level unification opens a speculation in
`Explain`, and none in `Success` unless a speculation is already open. In
`Success` a failed top-level unification outside a speculation sets
`Checker::unexplained_failure` (the old `note_unexplained_unify_failure`)
and leaves no trail, no trace and no saved descriptor. What it wrote into
the graph stays written, and that is not observable: nothing is published
and no diagnostic is printed from that run; the unit is checked again from
its first item in `Explain` (3.4). Inside a speculation the trail is live
and the owner restores. In `Explain` a failure undoes path compression only
(`Btype.undo_compress`, compiler/ml/btype.ml:792), restores the descriptor
of each linked structure node (`t1'.desc <- d1`, ctype.ml:2437) and keeps
the trace. Tests: `success_mode_keeps_nothing_for_a_failure`,
`explain_mode_keeps_the_trace_and_undoes_compression` (R3a).

**6. Corrections to the task text of 6.4.**

- *One slice of 6,000 lines.* Ten slices of at most 600.
- *"Is-abbreviation as one bit of `TypeDecl`."* A constructor node's `a`
  is a `paths` row (bridge/from_old.rs), not a `TypeDecl` index, and
  `TypeDecl` rows exist only for the unit's own declarations. Unification
  reads `expand::TypeTable`, a dense table by type index (16 bytes a row).
  R3b fills it from a segment for the harness; R4 and R5a fill it for a
  unit being checked.
- *"The memo as slot 0 of a constructor's list."* True for a constructor
  with arguments. A nullary constructor's memo is shared by all nodes of
  its type (ctype.ml:200), which is what makes O11 observable, so it is a
  row of `Memo::simple` and slot 0 of a nullary node stays empty.
- *"The pair set exists only on the paths that do not link: abbreviation,
  row and object cases."* OCaml's `unify` has no pair set in expression
  mode at all: every case links before it recurses (ctype.ml:2227-2440),
  and `unify_eq_set` is read only in pattern mode (ctype.ml:2205-2214).
  The old Rust checker's `already_unified` set exists because it links
  after the children in one case (types/ctype.rs:8005-8022), which the
  failure list forbids. The criterion becomes: `rg -n 'pairs'
  src/tc/unify.rs src/tc/rows.rs` shows the pair set in `unify_gadt`,
  `mcomp` and the pattern-mode branch only. If the differential test then
  differs from the old checker, the builder stops with the seed.
- *"Unify of two 10,000-node equal types is at most 4 steps a pair."*
  OCaml runs `occur` on every structure pair before it links
  (ctype.ml:2330), a walk of the right-hand subtree with no level cut
  (ctype.ml:1384-1408, 1488), and the old checker does the same
  (types/ctype.rs:8210, 8242). The cost is therefore the pairs plus the sum
  of the right-hand subtree sizes: linear for a wide type, quadratic for a
  chain. The bounds are: at most 8 steps a pair on a wide type of 10,001
  pairs; on a 10,000-deep chain at most `n(n+1)/2 + 260n` steps and no
  stack overflow on 2 MB. This is derived from the two sources; it was not
  measured by running the old checker (question 1 of 8.5).
- *"Binding a variable ... 1 step in total when the type's root is below
  the variable's level."* Impossible: a node made after `end_def` around a
  variable of the definition is below the variable's level and holds it,
  and binding must fail (O13); `unify1_var` calls `occur` with no level
  test (ctype.ml:2216-2218). The bound is one walk, at most 2 steps a node,
  whatever the levels (`binding_finds_the_variable_under_a_lower_root`).
- *"A second unify of the same pair is 0 steps."* At most 1: the link the
  first one wrote.
- *"A snapshot in `Mode::Success`" is a failure.* Kept for the top-level
  unification. Two places need an undo by OCaml's own definition and open a
  speculation in either mode: the level walk when a clash triggers the
  expanding retry (ctype.ml:631-640), opened only when
  `TypeTable::scoped != 0`; and `matches`, `moregeneral` and the safe
  expansion of a type with constrained parameters.
- *Subtyping.* The coercions ReScript adds read a declaration's labels and
  constructors (types/ctype.rs:6648, `subtype_concrete_typedecls`; 5222,
  variant to primitive). Member tables do not exist before R5a. R3j builds
  `subtype_rec` without them; they move to R6e, whose row in 5.3 already
  lists coercions.
- *Node kinds.* R1's graph has five tags. Objects, fields, rows, universal
  variables, polymorphic types and packages keep the layout R2 publishes
  (`TUPLE | EXTENDED`, children in list slots, a descriptor row), with
  worker-local pools (`rows::Extras`), so R1's walks need no new case.
- *Variable names in an instance (found by the harness, not in the task
  text).* The old checker's `instance` gives every copied variable no name
  (`copy_type_desc`, compiler/ml/btype.ml:510); R1's `Graph::instance` and
  `Graph::copy` keep the scheme's name. That is O17. The kernel tier of the
  harness reported it on its first run; it prints no names until R3b, whose
  first commit makes the two R1 functions write no name
  (`instance_drops_variable_names`). A `keep_names` instance
  (ctype.ml:982) is added by the slice that first needs it (R5a).
- *A type written through a module alias.* OCaml expands it to a node of
  the target path and does not memorize that (ctype.ml:1211-1214). The old
  checker memorizes it: the probe of decision 3 shows `N.t` shared. The new
  checker follows the old checker (`expand::ALIAS`), because that is what
  `both` mode compares (question 2).

### 8.3 Per slice: functions, end state, commits, failure, gates

The gates of 5.3 apply to every slice. "Tests" are in
`src/tc/r3_tests.rs` unless a module is named; a slice is done when they
pass without `ignore`.

**R3a.** Functions: `Checker::{unify, unify_distinct, unify_pair, bind,
binding_walk, occur, deep_occur, unify_expanded, push_children,
undo_compress}`, with `unify_expanded` treating every head as its own
expansion. End state: `rg -n 'todo!\("R3a"\)' src/tc` is empty; tests
`unify_of_equal_wide_types_is_linear`,
`unify_of_equal_deep_types_fits_the_stack`,
`binding_a_variable_is_one_walk_of_the_type`,
`binding_finds_the_variable_under_a_lower_root`, `link_directions`,
`success_mode_keeps_nothing_for_a_failure`,
`explain_mode_keeps_the_trace_and_undoes_compression`,
`differential::structural_tier_agrees_on_generated_cases` (10,000 cases).
Commits: (1) variables and the binding walk; (2) arrows, tuples,
constructors and the explicit stack; (3) the two modes and
`undo_compress`. Failure: a recursive `unify`; a link after the children;
a level cut in an occurrence test; a trail entry in `Mode::Success`
outside a speculation. Numbers: the step bounds in the tests; unify of two
variables, of two ground 1-node types and of two 3-node types in
`tc_kernel`, reported beside the kernel's 2.2 figures.

**R3b.** Functions: `TypeTable::{from_segment, info}`,
`Checker::{set_env, cleanup_abbrev, find_expansion, find_repr, memorize,
forget_abbrev, expand_once, expand_head, instance, copy, restore}`,
`link_node`; in R1's code, `Graph::instance` and `Graph::copy` write no
variable name. End state: `rg -n 'todo!\("R3b"\)' src/tc` is empty; tests
`instance_drops_variable_names`,
`expansion_is_memorized_per_node_and_per_nullary_type`,
`a_copy_of_a_nullary_constructor_links_to_the_memorized_node`,
`instance_with_an_empty_memo_costs_what_r1_costs`,
`memo_aware_instance_shares_what_the_old_instance_shares`,
`differential::expand_tier_agrees_on_generated_cases`. Commits: (0)
instances drop variable names, and `Tier::names` returns true for every
tier; (1) the table from a segment; (2) expansion and the two memos; (3) the memo-aware
instance and copy; (4) `restore` with its cleanup. Failure: a memo lookup
per node when `live == 0`; a hash map by type index; clearing the nullary
memo by a pass; an expansion that links the abbreviation node. Numbers:
instance1/3/5/7 at most 143/223/308/330 with an empty memo.

**R3d.** Functions: `Checker::{lower, lower_args}`. End state:
`rg -n 'todo!\("R3d"\)' src/tc` is empty; tests
`lower_without_scopes_costs_what_r1_costs`,
`lower_checks_scopes_and_expands_to_escape`,
`an_application_memorizes_the_result_node`. Commits: (1) the scoped walk;
(2) the expanding retry; (3) `lower_args`. Failure: a `TypeInfo` load per
node when `scoped == 0`; a speculation opened when `scoped == 0`.

**R3c.** Functions: the expansion in `unify_expanded`, the expansion retry
of `binding_walk`, `FrameKind::Recursion`, `Checker::unify_var`. End state:
`rg -n 'todo!\("R3c"\)' src/tc` is empty; the six fixture tests,
`idea_1_the_label_copy_survives`, `occurrence_through_an_abbreviation`,
`differential::full_tier_agrees_on_generated_cases` (10,000 cases).
Commits: (1) `unify2`: expand, lower, choose the side; (2) `unify3`: link
the expansion to the original, the recursion repair; (3) `unify_var`.
Failure: linking the abbreviation node instead of its expansion; linking
after the children; a pair set.

**R3m.** Functions: `TypeTable::mark_manifests`, `Checker::{chain_entry,
inherit, inherited_expansion, cut_chain}`. End state:
`rg -n 'todo!\("R3m"\)' src/tc` is empty; tests
`the_table_marks_the_types_whose_expansions_inherit`,
`an_inherited_entry_is_found_past_a_forgotten_one`,
`expanding_the_heads_down_nested_recursive_nodes_is_linear`,
`an_abbreviation_that_inherits_nothing_reads_no_row` (runs before and
after), `differential::tests::{expand_tier_agrees_on_recursive_
abbreviations, a_chain_of_inherited_entries_agrees}`. Commits: (1) the
marks; (2) the entry and the copy's place in the chain; (3) the cleanup's
cut and the lookup through the chain. Failure: a row for a type without
`INHERITS`; a pool cleared by a cleanup; a second pass over an instance.

**R3e.** Functions: `rows::template_has_open_row`, `Checker::{flatten_
fields, unify_fields, make_rowvar, build_field, unify_field,
unify_mutability, field_trace_pair, instance_open, dup_cell,
end_cell_session}`, the arm of two polymorphic types without variables,
`OPEN_ROW` in `mark_manifests`, the two edits of `binding_occurrence` and
`binding_scan`, and `Checker::copy`'s pass. End state: no
`todo!("R3e")`; the nine tests of `r3_tests.rs` under "R3e",
`differential::tests::{cells_agree_on_fixed_cases, object_plan_agrees_on_
generated_cases}`. Commits: (1) flatten, row variable, built fields, the
frames; (2) a common field, mutability, the trace pair, the polymorphic
arm; (3) the route crosses rows; (4) the duplicate of an instance and of
a copy. Failure: recursion; a descriptor row written in place; a pass
over an instance nobody asked for.

**R3f.** Functions: `Checker::{open_row, flatten_row, merge_rows,
unify_row, row_is_fixed, set_more, resolve, settle, resolve_either,
unify_row_field, join_either, row_field_end, row_end, trace_row,
row_trace_pair}`. End state: no `todo!("R3f")`; the nine tests of
`r3_tests.rs` under "R3f"; `differential::tests::variant_rows_agree_on_
fixed_cases`. Commits: (1) opening, flattening, merging; (2) `unify_row`
with `set_more`, the resolution to absent, the static row, the trace
rows; (3) `unify_row_field` and what it needs. Failure: a `variants`,
`row_fields` or descriptor row written in place; a reference in a pool
of its own; a resolution that is not a `Graph::write` of a reference
node; recursion.

**R3n.** Functions: `Checker::copy_refs`, and two lines of
`Checker::copy`. End state: no `todo!("R3n")`;
`differential::tests::variant_plan_agrees_on_generated_cases`. One
commit. Failure: a pass over a copy when the graph has no descriptor
row; a hash map from a reference to its copy.

**R3g.** Functions: `Checker::{unify_univar, enter_poly, univars_escape,
free_univar, split_univars}` in `rows.rs`. Everything that calls them is
wired and built (8.8, "What is wired"). End state: no `todo!("R3g")`; the
twelve ignored tests pass with their `ignore` removed; no other test
changes. Commits: 8.8, "Commit order". Failure: a scope left open after a
failed unification; a pairing that outlives a restore; a walk that
allocates; a hash set of bound variables.

**R3p.** Functions: `Checker::{unify_package, package_end}` in `rows.rs`.
End state: no `todo!("R3p")`; the three ignored tests pass. One commit.
Failure: a frame or a saved descriptor left after a clash in the merge; a
supplier not put back; a `Vec` of pairs.

**R3h, R3r.** Functions, end state, commits and gates: section 8.9
("The parts") and the two prompts of 8.4.

**R3h to R3j.** Functions: every signature of `rows.rs` and `relate.rs`
carrying the slice's name. End state for each: no `todo!` with its name;
its generator extension and old-side vacuity test (first commit); the
`Full` tier at 10,000 cases with the extension on. R3e: fields in OCaml's
order, the mutability cells. R3f: the fresh row for the missing tags is
made once; closedness and the row name as ctype.ml:2560-2600. R3h: the pair set only
here; an equation writes one `TypeTable` row and cleans the memos. R3i:
`equal` and `matches` restore their speculation; `moregeneral` has none,
as in OCaml (8.6, decision 114, which corrects this sentence and the
last line of "A snapshot in `Mode::Success`" in decision 6 of 8.2). R3j:
the constraints are returned, not unified inside the walk.

### 8.4 The build prompts

The common part of 6.0 is prepended to each. Then, verbatim:

```text
You build slice R3x of the type checker rewrite. Read, in this order:
AGENTS.md; compiler-rust/docs/CHECKER_REWRITE.md sections 2.1, 3.3 and 8;
the files of your slice in compiler-rust/src/tc/. The skeleton is fixed:
you fill in every body that says todo!("R3x") with your slice's name, and
nothing else. You do not change a signature, a doc comment's stated cost,
a size test, or a test. You do not add `#[ignore]`, and you remove the
`#[ignore = "R3x build"]` of your slice only. If a signature, a cost or a
test cannot be met, stop: write the smallest reproduction (for a
differential failure: the seed and the report it prints) in the pull
request and end your turn. Do not work around it.

The behaviour is OCaml's, at the location each doc comment cites; read
that code before you write the body. Where compiler-rust/src/types/ctype.rs
does the same thing in another form, OCaml's order of work wins, and the
differential test (src/tc/differential.rs) is the judge: it runs the same
operations on the old checker and on your code and compares which
operation failed and every node's sharing, level and name.

The intent, not a layout: how you split a body into private helpers is
yours to decide; say what you did in the commit message. A private helper
has a doc comment that states its cost. No recursion over types: use
Checker::frames or Graph::work. No allocation per visited node. No hash
map keyed by a node, a type index or a pair, except unify::PairSet.

When a module has no todo! left, remove its #[allow(...)] line in
src/tc/mod.rs and fix what the compiler then reports.

Done means, all on your last commit:
  cargo test --manifest-path compiler-rust/Cargo.toml tc::   passes, and
    the tests named for your slice in section 8.3 are not ignored;
  rg -n 'todo!\("R3x"\)' compiler-rust/src/tc                prints nothing;
  cargo clippy --locked --manifest-path compiler-rust/Cargo.toml
    --all-targets --all-features -- -D warnings              passes;
  the gates of section 5.3.
Paste the output of each in the pull request.
```

Then one of these, in place of "R3x" and after the text above:

```text
R3a. First edit: Checker::unify in src/tc/unify.rs (two repr and a
compare, then unify_distinct). Then unify_distinct's loop over
Checker::frames, then bind and binding_walk. In this slice a head is its
own expansion: unify_expanded does not call expand_head. Commits: (1)
variables and the binding walk, with link_directions' first three blocks
passing; (2) arrows, tuples, constructors; (3) the two modes and
undo_compress. Relations to hold: unify of two equal types makes no node;
a second unify of the same pair costs at most 1 step; the step count of
unify_of_equal_wide_types_is_linear is at most 8 a pair. Report from the
tc_kernel bench: unification of two variables, of two 1-node ground types
and of two 3-node types, in instructions, beside the kernel's figures of
section 2.2. Say plainly if a figure is above the kernel's.
```

```text
R3b. Commit 0, before anything else: in src/tc/template.rs make
Graph::instance and Graph::copy give a copied variable no name (a = NONE;
compiler/ml/btype.ml:510), make differential::Tier::names return true for
every tier, and see the kernel tier still pass; this is the one change to
R1's code and the one change to the harness you make. Then: TypeTable::info
and TypeTable::from_segment in src/tc/expand.rs; run differential's Expand tier old side to see what a
generated declaration looks like. Then expand_once (a memo miss
instantiates the manifest's template at the node's level and memorizes
before the body is linked, as `subst` does), then the memos, then
Checker::instance and Checker::copy. Commits as in section 8.3. Relations
to hold: with Memo::live == 0, Checker::instance makes the nodes and takes
the steps Graph::instance takes for the same template, and instance1/3/5/7
in the tc_kernel bench cost at most 143/223/308/330 instructions (measure
as TC_KERNEL_R1.md does; paste the table). An expansion never links the
abbreviation node. cleanup_abbrev is one store for the nullary memo.
```

```text
R3d. First edit: Checker::lower in src/tc/expand.rs: when
self.types.scoped == 0 call Graph::lower and return. Then the scoped walk
(ctype.ml:584-630), then the retry (ctype.ml:631-640), then lower_args.
Relations to hold: with scoped == 0 the step count equals Graph::lower's
on the same graph and no speculation is opened; with a scoped type, a
clash leaves the graph as it was before the call.
```

```text
R3c. First edit: Checker::unify_expanded in src/tc/unify.rs: call
expand_head(ExpandMode::Unif) on both sides as unify2 does
(ctype.ml:2276-2303). The link of unify3 is from the expanded head of the
chosen side to the ORIGINAL node of the other side (ctype.ml:2331), written
before the children are pushed. Commits as in section 8.3. Relations to
hold: fixture_10's assertions; unifying two nodes of one NULLARY
abbreviation makes no node (two nodes of one parameterised abbreviation
are expanded: 8.6, decision 11); the Full tier of the differential test passes at 10,000
cases. If a seed fails and OCaml's source supports your code, stop and
report the seed: do not copy the old checker's order.
```

```text
R3k. Read section 8.6, decision 14, and compiler/ml/ctype.ml:584-640 and
2216-2225. First edit: Checker::lower in src/tc/expand.rs, the second
pass. In Mode::Explain, when no speculation whose owner restores is open
(the test Checker::occur_first makes in src/tc/unify.rs), the second pass
runs without a speculation and a clash keeps what it wrote; the escaping
node and a new variable at the target level are pushed on Checker::trace
so that they come after the pairs the enclosing unification adds. One
commit. Relations to hold: Mode::Success and a lowering inside an owner's
speculation make the writes and the steps they make today
(lower_checks_scopes_and_expands_to_escape and the scoped step tests of
expand.rs unchanged); the Full tier and scoped_plan_agrees_on_generated_
cases pass with the same pinned seeds. Shortcuts that count as failure:
keeping the levels in Mode::Success; a trace pair in Mode::Success; a
variable made when the lowering does not clash. Remove the ignore of
differential::tests::a_failed_retry_keeps_its_levels_in_the_explaining_
mode and of no other test.
```

```text
R3m. Read section 8.6, decisions 16, 19 and 26; compiler/ml/ctype.ml
720-724, 778-799, 1100-1130; compiler/ml/btype.ml 606-647; in
src/tc/expand.rs the types ChainRow and Chains and the five functions
whose body is todo!("R3m"). Everything else is wired: subst, expand_once,
link_memorized and cleanup_abbrev already call them, behind the INHERITS
bit or a non-empty pool.

First edit: the body of TypeTable::mark_manifests, then its call as the
last statement before `table` is returned in TypeTable::from_segment, and
in the same commit the count of expand::tests::table_from_ten_thousand_
declarations_is_one_pass from `2 * n + 1` to `5 * n + 1` (the pass reads
the three template nodes of each manifest; this is the one test line you
change, decision 26). Remove the `#[allow(dead_code, ...)]` above
mark_manifests. r3_tests::the_table_marks_the_types_whose_expansions_
inherit passes after this commit.

Commits, in order: (1) the marks; (2) chain_entry and inherit: the two
tests of r3_tests.rs and differential::tests::expand_tier_agrees_on_
recursive_abbreviations pass; (3) cut_chain and inherited_expansion:
differential::tests::a_chain_of_inherited_entries_agrees passes. Remove
each `#[allow(unused_variables)]` with its todo!, and the five
`#[ignore = "R3m build"]`.

Each body is what its doc comment says, step for step. One
`#[cfg(test)] super::steps::tick()` per row visited in a walk, one in
chain_entry, one per template node read in mark_manifests, one at the
top of inherited_expansion.

Relations to hold: r3_tests::an_abbreviation_that_inherits_nothing_reads_
no_row passes unchanged (it runs today); every other tc:: test passes
unchanged, with the same pinned seeds; the steps of expanding the heads
down 10,000 nested nodes are at most 11 times those of 1,000.
Shortcuts that count as failure: a row or a table entry for a node of a
type without INHERITS; a hash map; a row keyed by a node handle; clearing
or truncating the pool in cleanup_abbrev or in restore; a second pass
over an instance's nodes; reading a node's head to learn whether its
entry is private (the node may have been linked since: the bit is in the
row); a change in graph.rs, level.rs or template.rs. At most 150 lines.
```

```text
R3e. Read section 8.6, decisions 17, 18, 22 and 27; compiler/ml/ctype.ml
314-342, 1380-1408, 1725-1778, 2305-2332, 2400-2424, 2445-2539;
compiler/ml/btype.ml 404-412, 449-532, 745-747; src/tc/rows.rs whole; in
src/tc/unify.rs unify3, extended_children, run_frames, explain_failure,
binding_occurrence and binding_scan; in src/tc/expand.rs link_memorized,
Checker::copy and mark_manifests. R3m is merged before you start.

First edit: rows::flatten_fields, then Checker::unify_fields with
make_rowvar and build_field, then unify_field and unify_mutability: after
them r3_tests::fields_a_side_lacks_are_built_on_one_row_variable and
a_closed_row_takes_no_field pass. Each body is what its doc comment
says, step for step, in that order.

Commits, in order:
(1) flatten_fields, make_rowvar, build_field, unify_fields;
(2) unify_field, unify_mutability, field_trace_pair, and the arm of two
    polymorphic types without variables in extended_children;
(3) the route of a variable against a constructor crosses rows: in
    binding_occurrence the test with `occur_first` becomes
    `self.reaches(var, ty, routed)`, and binding_scan takes `deep: bool`
    (true when routed) and, for a node at which stops_occurrence holds,
    pushes its children as it does for any other node when `deep`
    (`LOWERS` when it lowered the node, no flag otherwise) in place of
    `LEVEL_ONLY`. Nothing else in the two functions changes;
(4) template_has_open_row, OPEN_ROW in mark_manifests, dup_cell,
    end_cell_session, instance_open; and Checker::copy: its fast path
    becomes `self.memo.live == 0 && self.extras.descriptors.is_empty()`
    and its pass `self.link_memorized(first, NONE,
    !self.extras.descriptors.is_empty())`.
Remove the `#[ignore = "R3e build"]` lines and no other.

Steps: one `#[cfg(test)] super::steps::tick()` per field flattened, per
step of the merge, per field built, per node a terminator walk passes or
marks in dup_cell. Name comparisons of the sort are not steps.

Relations to hold: every tc:: test that passed before passes unchanged,
with the same pinned seeds; r3_tests::objects_of_ten_thousand_fields_are_
linear; an instance of a template without an open row through
Checker::instance takes the steps of Graph::instance; no descriptor,
variant or row-field row that existed before an operation differs after
it (run_new asserts it on every generated case).

If a generated case of differential::tests::object_plan_agrees_on_
generated_cases differs, read the OCaml arm first. If your code does what
the arm says, stop and report the seed with the arm's lines: do not copy
the old checker, and do not pin the seed yourself.

Shortcuts that count as failure: a recursive call of unify, unify_fields
or flatten_fields; a descriptor row written in place, or a new one for a
built field; a cell in a pool of its own or as a child of a field; a hash
map from a class to its duplicate; walking a row to its end once per
field; a pass over an instance's nodes when the caller did not ask for
one; sorting by name index; an allocation per field (the scratch vectors
of Extras keep their capacity); a change in graph.rs, level.rs or
template.rs. At most 600 lines.
```

```text
R3f. Read section 8.6, decisions 17, 18, 28 and 34; compiler/ml/ctype.ml
366-397, 1704-1713, 2541-2730; compiler/ml/btype.ml 112-170, 229-241,
742-744; src/tc/rows.rs whole (the comment "The reference of a variant
field" is the layout; field_repr, field_types and published_slots are
built and tested: use them, do not write a second reader); in
src/tc/unify.rs unify3, extended_children, run_frames, explain_failure.
R3e is merged before you start.

First edit: Checker::open_row in src/tc/rows.rs; after it
r3_tests::opening_a_row_gives_each_reither_field_a_reference passes.
Each body is what its doc comment says, step for step, in that order.

Commits, in order; remove the `#[ignore = "R3f build"]` of a test in the
commit after which it passes, and no other ignore:
(1) open_row, flatten_row, merge_rows, row_is_fixed.
    Passes: opening_a_row_gives_each_reither_field_a_reference.
(2) unify_row, set_more, resolve, settle, row_end, trace_row.
    Passes: an_open_row_takes_the_tags_it_lacks,
    a_closed_row_refuses_a_tag_and_the_empty_type_is_a_clash (neither
    has a common tag, so neither reaches a body of commit 3).
(3) unify_row_field, resolve_either, join_either, row_field_end,
    row_trace_pair. Passes: the six other tests of r3_tests.rs under
    "R3f" and differential::tests::variant_rows_agree_on_fixed_cases.
Remove `#[allow(unused_imports)]` above `use super::unify::FrameKind` in
rows.rs when you first use it.

Steps: one `#[cfg(test)] super::steps::tick()` per field in open_row and
flatten_row, per step of the merge, per field of a rest in set_more, per
holder in settle and in resolve_either, per field in row_end. Name
comparisons of the sort are not steps.

Relations to hold: every tc:: test that passed before passes unchanged,
with the same pinned seeds; rows_of_ten_thousand_tags_are_linear; a
changed row that is not fixed makes exactly one node whatever it gains;
no descriptor, variant or row-field row that existed before an operation
differs after it (run_new asserts it on every generated case, the
hand-built tests with assert_rows_kept); unifying a pair of variant
nodes a second time makes no node.

Do NOT run or un-ignore differential::tests::variant_plan_agrees_on_
generated_cases: it is R3n's (a generated case copies a row). If a fixed
case of variant_rows_agree_on_fixed_cases or a hand-built test differs
from what your code does, read the OCaml arm the test quotes. If your
code does what the arm says, stop and report the test with the arm's
lines: do not bend the code to the test, and do not change the test.

Shortcuts that count as failure: a write to a `variants`, `row_fields`
or descriptor row that exists; a reference kept anywhere but in a slot
of the variant node; resolving by anything but Graph::write of the
reference node (the trail must undo it); a new list for a node that is
already opened; opening a node that has no Reither field; a recursive
call of unify, unify_row or unify_row_field (push frames); an
allocation per field (Extras::row_scratch keeps its capacity); a hash
map; sorting by name index; walking the holders of a reference when it
is resolved to Reither more than once; a change in graph.rs, level.rs
or template.rs. At most 600 lines.
```

```text
R3n. Read section 8.6, decision 34 ("What a copy does"); compiler/ml/
btype.ml 366-392; compiler/ml/ctype.ml 800-870; src/tc/rows.rs: the
comment "The reference of a variant field", open_row and copy_refs; in
src/tc/expand.rs Checker::copy and link_memorized; in src/tc/template.rs
Graph::copy (its queue `work` holds, in order, the node each new node
was copied from). R3e and R3f are merged before you start.

One commit. First edit: in Checker::copy (src/tc/expand.rs), around the
call of link_memorized that R3e left there, set `self.extras.copying =
true;` before it and `self.extras.copying = false;` after it. Then the
body of Checker::copy_refs, case by case as its doc comment lists them.
Remove the `#[ignore = "R3n build"]` of differential::tests::
variant_plan_agrees_on_generated_cases and no other.

Steps: one `#[cfg(test)] super::steps::tick()` per field of the node.

Relations to hold: every tc:: test that passed before passes unchanged,
with the same pinned seeds; a copy of a graph that has no descriptor row
takes the steps of Graph::copy; Checker::instance is not changed.

If a generated case differs, read btype.ml:366-392 and ctype.ml:800-870
first. If your code does what they say, stop and report the seed with
the lines: do not copy the old checker, and do not pin the seed
yourself.

Shortcuts that count as failure: a hash map from a reference to its
copy (the session's nodes are a dense range: use Checker::marks and
g.work); touching g.work inside the pass; a reference shared by two
fields of one copied row when `more` was generic; a new reference when
`more` was not generic; holder rows of the source reused for the copy;
a change in graph.rs, level.rs or template.rs. At most 150 lines.
```

```text
R3g. Read section 8.8 whole and section 8.6, decisions 49 to 51;
compiler/ml/ctype.ml 1544-1679 (unify_univar, occur_univar,
univars_escape, enter_poly), 2216-2247, 2299-2331, 2413-2415 and
2685-2704; compiler/ml/btype.ml 229-272 and 739-741; in src/tc/rows.rs
the doc comments of PolyScope, partner_node, unify_univar, enter_poly,
univars_escape, free_univar, occur_univar and split_univars, and
join_either and row_field_end, which call split_univars; in
src/tc/unify.rs unify_univars, free_of_univars, leave_scopes, the
LeavePoly arm of run_frames and the universal variable arm of unify3.
Those callers are built: do not change them. R3e, R3f and R3n are
merged.

You write five bodies in src/tc/rows.rs, each where its
`todo!("R3g")` is, and nothing else under src/tc except removing
`#[ignore = "R3g build"]` lines. The doc comment above each body lists
its steps; follow them in that order.

First edit: the body of Checker::free_univar. Then run
  cargo test --manifest-path compiler-rust/Cargo.toml --lib \
    tc::r3_tests::the_first_free -- --include-ignored
and go on only when it passes.

Commits, in this order (each one's tests are named; a test that calls a
body of a later commit stays ignored until that commit):
1. free_univar. Un-ignore the_first_free_universal_variable_is_found_
   in_order, a_free_universal_variable_is_refused and a_free_universal_
   variable_below_a_swapped_unify3_is_reversed.
2. unify_univar and enter_poly, whole: enter_poly calls univars_escape
   as step 2 of its comment says. That body is still todo! and the call
   is not reached: no test of this commit has a known binder.
   Un-ignore universal_variables_pair_by_position, a_variable_of_an_
   outer_scope_pairs_in_its_scope, a_failure_leaves_no_scope_and_a_
   restore_undoes_the_pairings and a_clash_in_the_bodies_below_a_
   swapped_unify3_is_reversed.
3. univars_escape. Un-ignore a_known_binder_escapes_before_the_bodies.
4. split_univars. Un-ignore the_types_that_hold_a_universal_variable_
   are_unified_not_gained, universal_variables_at_ten_thousand, and in
   differential.rs universal_variables_agree_on_fixed_cases and
   univar_plan_agrees_on_generated_cases.
End your turn after commit 4 is pushed and the whole of
  cargo test --manifest-path compiler-rust/Cargo.toml --lib tc::
has been seen to pass with no test ignored for "R3g build". The tests of
commit 4 are the ones no prototype of yours has seen: if one fails, fix
the body, not the test.

Steps: one `#[cfg(test)] super::steps::tick()` per list slot read in
unify_univar, enter_poly and univars_escape, and per node visited in
free_univar and in the walk of univars_escape. None in split_univars
(free_univar counts).

Relations to hold: every tc:: test that passed before passes unchanged;
universal_variables_at_ten_thousand as written (11 times for bound
variables and for the row, 110 times for nested scopes); no descriptor
row is written in place (assert_rows_kept in the tests); `scopes`,
`frames` and `saved` are empty after every unification, failed or not.

Report, before and after, the instructions of the tc_kernel bench
operations unify_vars, unify_ground1, unify_ground3, unify_datatype2
and unify_abbrev2 (compiler-rust/docs/TC_KERNEL_R3.md, "Machine and
method"), at three commits: de646dffcb (the trunk before this slice's
skeleton, which added reads to unify_pair and unify3 that nobody has
measured), the trunk you start from, and your head. No target is set
(section 8.6, decision 46): report the figures. Your bodies are reached
only through functions that are already out of line; if an operation
moves by more than 2 between your start and your head, mark the body
`#[inline(never)]`, measure once more, report both, and do not tune
anything else.

Another builder writes Checker::unify_package and Checker::package_end
(slice R3p) in src/tc/rows.rs at the same time. Do not edit those two
functions or the three tests ignored for "R3p build".

If a generated case differs, read the ctype.ml lines above first. If
your code does what they say, stop and report the seed with the lines:
do not copy the old checker, and do not pin the seed yourself.

Shortcuts that count as failure: a hash set or a `Vec` allocated per
call for the bound variables (use Checker::marks with a new generation,
and Extras::open_polys); a recursive walk (use g.work); partners kept
anywhere but in the partner nodes, or written without Graph::write;
pushing the scope before the escape test; cutting the scopes back
anywhere but in leave_scopes and the LeavePoly arm; a name compared; a
change in unify.rs, expand.rs, graph.rs, level.rs or template.rs; a
change under src/types. At most 600 lines; the prototype of the design
turn took about 270.
```

```text
R3p. Read section 8.8 ("Packages") and section 8.6, decision 52;
compiler/ml/ctype.ml 2135-2181 and 2416-2423; in src/tc/rows.rs the doc
comments of Completion, PackageDecls, unify_package and package_end; in
src/tc/unify.rs the Package arm of extended_children and the PackageEnd
arm of run_frames, which are built: do not change them. R3e is merged.

One commit: the bodies of Checker::unify_package and
Checker::package_end in src/tc/rows.rs, each where its `todo!("R3p")`
is, following the steps of its doc comment in order, and the three
`#[ignore = "R3p build"]` lines of src/tc/r3_tests.rs removed. First
edit: unify_package. End your turn after the commit is pushed and
  cargo test --manifest-path compiler-rust/Cargo.toml --lib tc::
has been seen to pass with no test ignored for "R3p build".

Steps: one `#[cfg(test)] super::steps::tick()` per turn of the merge.

Relations to hold: every tc:: test that passed before passes unchanged;
packages_of_ten_thousand_names_are_linear as written; after a clash
`frames` and `saved` are as long as before the call and
`Checker::packages` is `Some` again.

Report, before and after, the instructions of the tc_kernel bench
operations unify_vars, unify_ground1, unify_ground3, unify_datatype2
and unify_abbrev2 (compiler-rust/docs/TC_KERNEL_R3.md, "Machine and
method"). No target is set (section 8.6, decision 46).

Another builder writes the five `todo!("R3g")` bodies of
src/tc/rows.rs (free_univar, unify_univar, enter_poly, univars_escape,
split_univars) at the same time. Do not edit those functions or the
tests ignored for "R3g build".

Shortcuts that count as failure: a `Vec` of pairs (push the frames and
reverse that part of `frames` in place); comparing names in the kernel
(PackageDecls::compare is the only order); reading the pool the names
are positions of; calling `compatible` before the lists are unified, or
for two equal paths; a change in unify.rs or outside rows.rs and the
three ignore lines. At most 150 lines.
```

Reissued in the seventh skeleton turn. The searches of both prompts
were run on the head of that turn and print what the prompt says they
print there. The commits of a slice cannot fail alone: the tests of a
slice stay ignored until its last commit, and nothing that runs today
reaches a `todo!` of either slice (`cargo test --lib tc::` passes on
the skeleton: 282 passed, 19 ignored). The cut between the two slices
was run: with R3h's bodies present and R3r's `todo!`, the twelve tests
of R3h pass and the six R3r tests of `r3_tests.rs` fail.

```text
R3h. Read section 8.9 whole and section 8.6, decisions 47, 60, 61, 62
and 72 to 80; compiler/ml/ctype.ml 253-273, 1371-1408, 1467-1536,
1802-1881, 2084-2108, 2229-2440 and 2739-2750; compiler/ml/env.ml
1805-1810; in src/tc/unify.rs the doc comments of PairSet,
FrameKind::{Flags, Assumed, Try}, Checker::{unify_pattern,
cut_equations, unify_newtypes, occur_pattern, unify3_pattern,
assumed_equal, put_flags} and the bodies of unify_pair,
occur_expanding, unify_expanded, unify3 and run_frames; in
src/tc/rows.rs the doc comments of Equation, LocalDecls and
Checker::{match_unmatched, open_fresh, reify, fresh_abstract,
below_newtype_level, forget_name_children, add_gadt_equation,
non_recursive_abbrev, duplicate, find_newtype_level} and the bodies of
copy_refs and match_fixed_fields; in src/tc/expand.rs
TypeTable::{instantiable, non_aliasable, injective, contractive,
constrained}, LOCAL, PREDEF, and the doc comment and body of
Checker::subst.

A prototype of this slice was written in the design turn and every
test of the slice passed against it. It is not in the repository (it
was over the size set for committing it); it is the first comment of
pull request 354 and you may read it. It is a reference, not the
answer: you write the bodies from the doc comments and section 8.9.
Its occur_pattern recurses, which counts as failure below: the walk on
Checker::frames has never been run. Where the prototype and a doc
comment differ the doc comment stands, and you report the difference.

Before your first commit this prints rows.rs:8 and unify.rs:5, and the
second prints r3_tests.rs:12:
  grep -c 'todo!("R3h")' compiler-rust/src/tc/*.rs | grep -v ':0$'
  grep -c '#\[ignore = "R3h build"\]' compiler-rust/src/tc/*.rs | grep -v ':0$'
When you end, both print nothing.

Commits, in this order, each pushed with
  cargo test --manifest-path compiler-rust/Cargo.toml --lib tc::
seen to pass (the tests of this slice are ignored until commit 5; after
each commit run them with `-- --ignored` and say in the commit message
which pass):
1. Checker::match_unmatched in rows.rs (decision 47, last paragraph),
   with the hand-built row of that decision as a running test in
   src/tc/r3_tests.rs; a second running test whose row is not fixed by
   its flag and has a constructor as its `more` (ctype.ml:826-830:
   copy_refs sends it to match_fixed_fields too); and a step test of
   match_unmatched over a copy with n unmatched fields.
2. Checker::{find_newtype_level, non_recursive_abbrev, duplicate,
   add_gadt_equation} in rows.rs, Checker::cut_equations in unify.rs,
   and the equation arm at the top of Checker::subst in expand.rs
   (decision 67).
3. Checker::{fresh_abstract, below_newtype_level, reify} in rows.rs
   (section 8.9, "reify").
4. Checker::{unify_pattern, unify_newtypes, occur_pattern,
   unify3_pattern} in unify.rs and the call of unify_newtypes in
   unify_pair (decisions 64, 65, 69), with a step test of
   occur_pattern over a type nested n deep. In unify3_pattern the three arms
   marked 2 in the table of decision 64 are `todo!("R3r")`, and the
   call of mcomp in the arm "a constructor on either side" is the
   existing Checker::mcomp, whose body is R3r's.
5. The `#[ignore = "R3h build"]` lines of src/tc/r3_tests.rs removed
   and nothing else in those tests changed.
End your turn after the fifth commit is pushed.

Not yours: Checker::{mcomp, push_compatible, package_fallback,
try_frame, recover, recover_frames, resume_frames} are R3r's. Leave
their `todo!("R3r")` and the tests ignored for "R3r build" as they are.

Steps: one `#[cfg(test)] super::steps::tick()` per node `reify`,
`non_recursive_abbrev`, `occur_pattern` and `duplicate` visit, and per
entry `cut_equations` pops; one per field `match_unmatched` reads;
unify_pair's own tick counts the pairs.

The two step tests you add (commits 1 and 4) are relations: the steps
at 10,000 are at most eleven times the steps at 1,000. Each must be
seen to fail with its structure broken (a second pass over the fields;
a walk that revisits a node), and the commit message says how you
broke it. The occur_pattern test also runs at a depth of 100,000
without overflowing the stack; if that case fails for a reason outside
occur_pattern, leave it out and report the reason.

Relations to hold: every tc:: test that passed before passes
unchanged; pattern_mode_at_ten_thousand and
an_equation_over_ten_thousand_shared_nodes_is_linear as written; after
unify_pattern, on either result, what r3_tests::assert_pattern_left
asserts.

Report, before and after, the instructions of the tc_kernel bench
operations unify_vars, unify_ground1, unify_ground3, unify_datatype2
and unify_abbrev2 (compiler-rust/docs/TC_KERNEL_R3.md, "Machine and
method"). No target is set (decision 46).

Report what Graph::generalize writes when `duplicate` calls it under
its speculation (decision 76): every kind of write, and whether
Graph::restore puts it back. If it writes anything but levels through
the trail, stop and report it: do not add a second copy. Report also
whether a node of the destination at or below the graph's current
level stays as it is (Graph::generalize skips such a node) and is then
shared by the copy: if one can be, stop and report it with the node.

The hand-built tests are the judge. If a test of yours fails where
your code does what the ctype.ml lines say, stop and report the test
with the lines: do not change the test.

Shortcuts that count as failure: linking two structures in pattern
mode; an occurrence test for a structure pair in pattern mode; reading
`pairs` or `umode` in unify_pair or anywhere in expression mode beyond
the one load of unify_expanded and the one of occur_expanding; a
recursive walk (reify: g.work; non_recursive_abbrev and occur_pattern:
Checker::frames above its length; marks with a new generation); a hash
set or a `Vec` allocated per call; cutting equations in Graph::restore
or on a failed unification; a body of an equation that shares a node
with its destination; writing a TypeTable row of an equation anywhere
but add_gadt_equation and cut_equations; a logged write of a node the
copy of `duplicate` made; a change in graph.rs, level.rs or
template.rs, or under src/types. At most 700 lines (the prototype's
part of this slice was about 630).
```

```text
R3r. R3h is merged. Read section 8.9, decisions 63, 64 (the rows
marked 2), 68, 70 and "No supplier", and section 8.6, decisions 60 (its
last paragraph), 77 to 80; compiler/ml/ctype.ml 1886-2080, 2358-2375,
2402-2411 and 2416-2424; in src/tc/unify.rs the doc comments of Try,
TRY_ARGUMENT, TRY_ROWS, FrameKind::Try and Checker::{try_frame,
recover, recover_frames, resume_frames}, and the bodies of
unify_distinct and run_frames; in src/tc/rows.rs the doc comments of
LocalDecls, DeclMatch, Checker::{mcomp, push_compatible,
package_fallback, enter_poly, unify_univar, unify_row, unify_fields,
flatten_row, merge_rows, unify_package}.

A prototype of this slice was written in the design turn and every
test of the slice passed against it. It is not in the repository: you
write the bodies from the doc comments and section 8.9.

Before your first commit this prints rows.rs:3 and unify.rs:8 (in
unify.rs: four bodies, the three arms R3h left in Checker::pattern_arm
and one line of the doc comment of unify3_pattern). The second prints
differential.rs:1 and r3_tests.rs:6:
  grep -c 'todo!("R3r")' compiler-rust/src/tc/*.rs | grep -v ':0$'
  grep -c '#\[ignore = "R3r build"\]' compiler-rust/src/tc/*.rs | grep -v ':0$'
When you end, both print nothing (reword the doc comment of
unify3_pattern that names the marker).

Commits, in this order, each pushed with the tc:: tests seen to pass
(the tests of this slice are ignored until commit 4; after each commit
run them with `-- --ignored` and say which pass):
1. Checker::duplicate in rows.rs made total (section 8.9, "Corrections
   after the review of R3h", item 1): the pass that makes the nodes of
   the destination generic goes THROUGH a node that is generic already,
   where Graph::generalize stops at one. Write that pass in rows.rs: a
   walk on g.work with one new generation of marks
   (Checker::fresh_marks), each node visited once, its level written
   generic with Graph::write when it is not (so the restore puts it
   back), its children pushed with Graph::children as
   Graph::generalize pushes them; one tick a node visited. Then the
   copy and the restore as they are. Reword the doc comment of
   `duplicate` for it (this once you edit a doc comment of the
   skeleton: the sentences on Graph::generalize, and the cost, which
   stays three passes over the destination). With it a running test in
   src/tc/r3_tests.rs: a destination that is a tuple, not generic,
   over a tuple that IS generic, over a constructor without arguments
   that is not generic; after `duplicate` the graph has grown by
   exactly the three nodes, every node of the copy is generic, and the
   levels of the three nodes of the destination are what they were.
   See it fail on your base before you change the body, and say so in
   the commit message.
   an_equation_over_ten_thousand_shared_nodes_is_linear passes as
   written.
2. Checker::{mcomp, push_compatible, package_fallback} in rows.rs
   (decisions 70 and 63).
3. Checker::{try_frame, recover, recover_frames, resume_frames} in
   unify.rs and the three arms R3h left `todo!("R3r")` in
   Checker::pattern_arm (decision 68; decision 64, the rows marked 2):
   the arguments of one type by injectivity, two variants, and the
   package arm, which calls Checker::package_fallback where
   unify_package clashes (the doc comment of package_fallback names
   that caller). They are one commit: an arm that pushes a Try frame
   cannot run without try_frame, and try_frame has no caller without
   the arms.
4. The `#[ignore = "R3r build"]` lines of src/tc/r3_tests.rs and
   src/tc/differential.rs removed, nothing else in those tests changed.
End your turn after the fourth commit is pushed.

Not yours: everything else R3h built (Checker::{unify_pattern,
cut_equations, unify_newtypes, occur_pattern, reify,
add_gadt_equation, non_recursive_abbrev, find_newtype_level,
match_unmatched} and the arms of Checker::pattern_arm marked 1). If
one of them is wrong for a test of yours, stop and report it; do not
edit it.

Steps: one tick per pair `mcomp` takes off its stack, and one per
record `recover` takes off.

Relations to hold: every tc:: test that passed before passes
unchanged; mcomp_at_ten_thousand and
recovering_ten_thousand_attempts_is_linear as written;
`Checker::compatible` and `Checker::tries` are empty when unify_pattern
and mcomp return; `g.speculation_depth` is what it was.

The hand-built tests are the judge. If a test of yours fails where
your code does what the ctype.ml lines say, stop and report the test
with the lines: do not change the test.

pattern_plan_agrees_on_generated_cases lists the seeds that differ and
why (UNTIL_R3S, EXPLAINED_UNTIL_R3S, EXPLAINED_OLD_DIFFERS; decisions
77 to 79). If it reports a seed that is not listed, or a listed seed
agrees, read the ctype.ml lines of the arm first. If your code does
what they say, stop and report the seed with the lines: do not copy
the old checker, and do not edit a list yourself. The old checker is
not a judge of a pattern unification that succeeds on two structures
(decision 62), and `differential::old_judges` already ends a case
before one; a seed that differs there means old_judges missed a link:
report it.

Report the same five bench operations as R3h, before and after. No
target is set (decision 46).

Shortcuts that count as failure: a nested call of Checker::unify for
an attempt (the attempt is frames above a Try frame); taking the
snapshot when the Try frame is pushed and not when it is popped
pending; reading any record of `tries` but the last, or searching
`frames` for a frame; a test of `tries` in the loop of run_frames or on
the success path; cutting `equations` in recover; a second table of
pairs for unification (the table of mcomp is `compatible`, the table
of unification `pairs`); `g.work` as the stack of mcomp; comparing
declarations in the kernel (LocalDecls::compare is the only reader of
a declaration); answering compatible for two data types without a
supplier; calling leave_scopes from mcomp or recover; a second copy
of the destination in `duplicate`, or a hash set in its walk; a change
in graph.rs, level.rs, template.rs or expand.rs, or under src/types.
At most 500 lines.
```

The prompt of R3q, written in the eighth skeleton turn. Both searches
and the commit order were run on the head that holds the skeleton: the
searches print what the prompt says, and with the bodies of commit 1
present six of the ten tests pass, with those of commit 2 nine, with
all three ten.

```text
R3q. R3h and R3r are merged. Read section 8.10 whole and section 8.6,
decisions 47 and 91 to 96; compiler/ml/ctype.ml 676-713, 1016-1028
(diff_list, conflicts, delayed_copy) and 1030-1105;
compiler/ml/btype.ml 126-135, 366-392, 421-470 and 478-532; in
src/tc/rows.rs the doc comments of PolySlot, PolyEdge, PolyCopy and of
the twelve functions from Checker::instance_poly to Checker::poly_pass,
and the doc comments and bodies of field_repr, each_field_types,
Checker::{open_row, hold, dup_cell, copy_refs}; in src/tc/template.rs
Graph::{copy_begin, copy_ref, copy_drain}; in src/tc/expand.rs
Checker::{memorized_node, link_memorized, copy}; in src/tc/unify.rs
Frame, FrameKind and Checker::child.

A prototype of this slice was written in the design turn and every
test of the slice passed against it. It is not in the repository; it
is a comment on the pull request of the eighth skeleton turn (one
fenced diff, each body under a marker line). You MAY read it. It meets
the doc comments, and it is not the standard: it has no commit
structure and its step counts were chosen for the tests. Nothing it
does is forbidden by this prompt; where your code differs from it, the
doc comment decides.

Before your first commit the first search prints rows.rs:12 and the
second r3_tests.rs:10:
  grep -c 'todo!("R3q")' compiler-rust/src/tc/*.rs | grep -v ':0$'
  grep -c '#\[ignore = "R3q build"\]' compiler-rust/src/tc/*.rs | grep -v ':0$'
When you end, both print nothing.

Commits, in this order, each pushed with the tc:: tests seen to pass
(the tests of this slice are ignored until commit 4; after each commit
run them with `-- --ignored tc::r3_tests` and say which pass):
1. Checker::{instance_poly, poly_begin, poly_walk, mark_holders,
   copy_sep, sep_child, sep_conflicts, sep_fill, poly_session,
   poly_pass} in rows.rs. Six tests pass: the first five of the
   section of R3q in r3_tests.rs and
   a_field_that_holds_a_universal_variable_gets_its_cell_by_its_row.
   The two tests of rows, the step test and the test of a label reach
   a body of a later commit.
2. Checker::copy_sep_row. Nine pass: also the two tests of rows and
   instance_poly_at_ten_thousand.
3. Checker::instance_label. All ten pass.
4. The `#[ignore = "R3q build"]` lines of src/tc/r3_tests.rs removed
   and the `#[allow(unused_variables, dead_code)]` above the `impl`
   block of this slice in rows.rs with its comment; nothing else in
   the tests changed.
End your turn after the fourth commit is pushed.

Not yours, and not to be edited: Graph::{copy, copy_begin, copy_ref,
copy_drain}, Checker::{memorized_node, link_memorized, copy, instance,
copy_refs, match_fixed_fields, match_unmatched, open_row, dup_cell,
free_univar}, and everything of R3h and R3r. If one of them is wrong
for a test of yours, stop and report it. The relations (R3i, R3j) are
not started; the six bodies of relate.rs stay as they are.

Steps: one tick a node the first walk of mark_holders takes off its
stack and one a node a propagation takes off; one a node sep_fill
fills; one a field copy_sep_row reads; one a frame and one a node
sep_conflicts reads.

Relations to hold: every tc:: test that passed before passes
unchanged; instance_poly_at_ten_thousand as written; after either
function returns `Checker::frames` has the length it had, no
`PolySlot::copy` is set and `PolyCopy::depth` is 0 (the tests assert
it); no node that existed before the call is written, except a source
row that `copy_sep_row` opens for `keep` and the references and cells
the pass of a copy writes.

The hand-built tests are the judge. If a test fails where your code
does what the ctype.ml lines say, stop and report the test with the
lines: do not change the test. Witness 2 of
a_node_on_the_way_is_copied_again_when_a_new_binding_is_free_in_it was
followed through OCaml's lines by hand and has no source program: if
you read the lines differently, stop and say how.

Report, before and after, the five unification operations of tc_kernel
(unify_vars, unify_ground1, unify_ground3, unify_datatype2,
unify_abbrev2, each minus its build_ twin) and instance7, copy7 and
checker_instance7. No target is set (decision 46); the slice adds no
line to a function they run.

Before each push, from compiler-rust, both print no warning:
  cargo clippy --all-targets -- -D warnings
  RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
(a public doc comment must not link a private item; a list in a doc
comment is indented as clippy asks). Every loop a body of yours has
ticks as the list of steps above says. In your report, name each loop
with the shape of instance_poly_at_ten_thousand that runs it 10,000
times; a loop that no shape runs that often is named as such (the
reviewer adds its test: you do not add or change a test).

Shortcuts that count as failure: a recursion in copy_sep, sep_fill or
mark_holders (the stack is `frames` or `g.work`); a `Vec`, a hash map
or a hash set made in a call (the pools are PolyCopy's; the set OCaml
keeps a node is not kept); sharing the copy of a node that holds a
universal variable between two places, or a memo of such copies;
calling Graph::copy or Checker::copy once a delayed node (it is one
session: copy_begin, a copy_ref a root, copy_drain); running the
session before the walk has ended, or making a node between copy_begin
and copy_drain other than through copy_ref; a parameter added to
copy_refs or link_memorized; opening a source row when `keep` is
false; reading `is_Tvar` of the copy of `more` after the stub is
linked; a stub or a table of this slice touched by instance_label for
a label whose argument is not a polymorphic type; a new FrameKind
(the walk reads Pair, Linked and LeavePoly as its doc comments say);
a change in graph.rs, level.rs, template.rs, expand.rs, unify.rs or
under src/types. At most 500 lines added to rows.rs (the prototype's
bodies are 429).
```

The prompt of R3s, written in the ninth skeleton turn. The three
searches were run on the head that holds the skeleton and print what
the prompt says; the state after its first commit is the state the
prototype was run in (every test of the slice passed, and the whole
`tc::` filter with the three seed lists as the prompt gives them).

```text
R3s. R3h, R3r and R3q are merged. Read section 8.11 (the part "As
built in the ninth turn" first: it replaces the older table and
contract below it) and section 8.6, decisions 85 to 88 and 97 to 112;
compiler/ml/ctype.ml 176-203, 584-640, 744-800, 1113-1135, 1163-1167,
1187-1279, 1319-1336, 1503-1536, 1697-1701, 2227-2303, 2732-2785;
compiler/ml/btype.ml 606-650, 749-804; compiler/ml/env.ml 1045-1048,
1305-1345, 1802-1811; compiler/ml/typecore.ml 2824-2829; in src/tc/unify.rs the doc comments of GADT_LOCAL to
CaseMark, of FrameKind::Untrace and Try, and the doc comments AND
bodies of Checker::{unify_distinct, unify_distinct_from, unify_pair,
unify_expanded, unify_var, unify_pattern, try_frame, recover,
recover_frames, resume_frames, run_frames, fresh_marks}; in
src/tc/expand.rs Memo, OwnMemo, Chains and Checker::{cleanup_abbrev,
find_expansion, find_repr, memorize, forget_abbrev, expand_once,
subst, subst_plain, expand_head, expand_head_unif, copy,
link_memorized, inherit, inherited_expansion, lower, lower_scoped_loop,
lower_args}; in src/tc/template.rs Graph::{copy_begin, copy_ref,
copy_drain} and Forward; in src/tc/rows.rs Checker::{add_gadt_equation,
fresh_abstract, non_recursive_abbrev}.

A prototype of this slice was written in the design turn and every
test of the slice passed against it. It is not in the repository; it
is a comment on the pull request of the ninth skeleton turn (one
fenced diff against the skeleton as that pull request committed it,
each body under a line `// R3S-PROTOTYPE`). You MAY read it. Its 25
bodies meet the doc comments. Three things it does are NOT yours to
copy: it deletes four size assertions (`InstanceScope`,
`InstanceMember`, `CaseMark` in unify.rs, `OwnMemo` in expand.rs),
which stay; it keeps the test of resume_frames that (c) deletes; and
its three lists of seeds are not the ones (d) gives. It was written
before `expand_head` stopped adding the chain in `ExpandMode::Opt`:
that line is built code and not yours. Where your code differs from
it, the doc comment decides.

Yours: the 25 bodies that are `todo!("R3s")`: in unify.rs
Checker::{unify_distinct_gadt, trace_on, late_pair, has_own_expansion,
expanded_instances, join_instance_levels, enter_instance_scope,
leave_case, add_local_type, instance_level, instance_scope_at,
push_instance, add_instances, add_instance_chain, copy_in}; in
expand.rs Checker::{forget_own_memos, own_expansion,
find_own_expansion, memorize_own, own_ancestor, inherit_own,
subst_traced, instance_clash, expanded_instance, instance_escapes};
and five edits of built code, each named below. Everything else under
src/tc is not yours, the guards the skeleton put into built functions
included: if one is wrong for a test of yours, stop and report it.

Before your first commit, from the repository root:
  grep -c 'todo!("R3s")' compiler-rust/src/tc/*.rs | grep -v ':0$'
prints expand.rs:10 and unify.rs:15;
  grep -c '#\[ignore = "R3s build"\]' compiler-rust/src/tc/*.rs | grep -v ':0$'
prints differential.rs:1 and r3_tests.rs:12;
  grep -c '#\[allow(unused_variables, dead_code)\]' compiler-rust/src/tc/unify.rs compiler-rust/src/tc/expand.rs
prints unify.rs:15 and expand.rs:10. When you end, the first two print
nothing and the third prints unify.rs:0 and expand.rs:0.

Commits, in this order, each pushed:
1. The 25 bodies, and with them, because no body is reached before a
   bit is set and every test of the slice sets one:
   (a) `self.gadt |= GADT_LOCAL` in rows.rs, in add_gadt_equation
       beside the push of the equation and in fresh_abstract before
       the node is made;
   (b) in unify_pattern, `GADT_PATTERN` set beside `umode = Pattern`
       and put back to what it was beside the line that puts `umode`
       back;
   (c) in resume_frames, the test `if self.gadt & GADT_PATTERN == 0`
       with its `return` and its comment deleted: `late_pair` always
       (the prototype ran with the test in place; with (b) it is never
       true where resume_frames is reached; if a test fails once it is
       deleted, stop and report it);
   (d) in differential.rs, exactly these three constants and their
       types: `UNTIL_R3S` is `[u64; 0] = []`, `EXPLAINED_UNTIL_R3S` is
       `[u64; 0] = []`, `EXPLAINED_NEW_DIFFERS` is `[u64; 2] =
       [4_000_045, 20_000_132]`. `EXPLAINED_OLD_DIFFERS` and
       `EXPLAINED_INSTANCES_DIFFER` stay as they are (decision 110
       says why; the doc comments above them already do). Nothing
       else of the harness changes.
   Run `cargo test --manifest-path compiler-rust/Cargo.toml --lib
   tc:: -- --include-ignored` in the background with its output in a
   file (it takes up to twenty minutes; poll it): every test passes,
   the thirteen of this slice included, and the last line reads 338
   passed, 0 failed, 0 ignored (the 325 that pass before your first
   edit and the thirteen). Never report a count you did not see.
2. The thirteen `#[ignore = "R3s build"]` lines removed, the 25
   `#[allow(unused_variables, dead_code)]` lines, and the
   `#[allow(dead_code)]` of NO_OWN with the sentence about it;
   nothing else in the tests changed. The same command without
   `-- --include-ignored` then reads 338 passed, 0 failed, 0 ignored.
End your turn after the second commit is pushed.

Steps (`#[cfg(test)] super::steps::tick()`): one a scope and one a
member instance_level reads; one a scope instance_scope_at reads; one
a member add_instance_chain marks and one a node of the chain; one a
scope and one a member copy_in reads; one a row own_ancestor reads;
one a node inherit_own reads.

Relations to hold: every tc:: test that passed before passes
unchanged; `Checker::gadt & GADT_TRACING` is 0 and `frames` has the
length it had after every top-level call (the tests assert it); an
addition to a set is one pool row and one `Graph::write`; a unit that
never has a local constraint and never unifies in pattern mode reaches
none of your bodies.

The hand-built tests are the judge, each with the OCaml lines it
follows. If a test fails where your code does what the cited lines
say, stop and report the test with the lines: do not change the test.
A seed listed in EXPLAINED_INSTANCES_DIFFER, EXPLAINED_OLD_DIFFERS or
EXPLAINED_NEW_DIFFERS differs for the reason its doc comment gives,
and you act on none of them; a seed that
is not listed and differs is read against the lines of 8.11 and
reported: you pin none.

Report, before and after, the five unification operations of tc_kernel
(unify_vars, unify_ground1, unify_ground3, unify_datatype2,
unify_abbrev2, each minus its build_ twin) and instance7, copy7 and
checker_instance7, saying which commit each column was built from.
No target is set (decision 46); decision 111 has the figures of the
prototype, and the slice adds no line to a function they run beyond
the guards that are in the tree.

Before each push, from compiler-rust, both print no warning:
  cargo clippy --all-targets -- -D warnings
  RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
(a public doc comment must not link a private item; a list in a doc
comment is indented as clippy asks). In your report, name each loop of
your bodies with the shape of instance_sets_at_ten_thousand that runs
it 10,000 times; the loops no shape runs that often are the parents
of own_ancestor, the nodes of inherit_own, the scopes of
instance_scope_at and the additions of copy_in: name them as such
(the reviewer adds their tests: you do not add or change a test).

Shortcuts that count as failure: a test of `gadt` at a popped pair of
run_frames, or a second call site of unify_pair (late_pair calls
run_frames); tracing left on after a call returns, on either result;
a set kept anywhere but in the list headed by its scope's node (a
`Vec` a scope, a hash set, a bit of a node), or an addition that a
`Checker::restore` does not undo; the length of the pool in `Try` or
in a mark; instance_level asked for each node of a chain or for each
copied node (the marks; the forwarding rows); a member compared
without `repr`; an own memo read by find_expansion outside tracing,
or written in the memo all nodes of a type share while tracing; a
cleanup of the own memos by forget_simple_memo; a recursion in
add_instance_chain or own_ancestor; a `Vec`, a hash map or a `Box`
made in a call; the lowerings of unify_fields and set_more, a memo
chain through a parent with arguments, a copy with `partial`, an
expansion of the types of a failed trace (decision 112 and the
corrections after the review of the ninth turn: not in this slice); a change of `Checker::copy`, `instance`,
`Graph::lower` or `bind_leaf`; a new FrameKind; a change under
src/types. At most 350 lines of code added outside comments (the
prototype's part is about 270).
```

The prompt of R3i, written in the tenth skeleton turn. The two
searches were run on the head that holds the skeleton and print what
the prompt says. With the first prototype in place the whole filter
with the ignored tests included read 351 passed, 0 failed, 0 ignored;
the corrected prototype and the ninth test came after that run.

```text
R3i. Every slice above it in the table of 8.1 is merged. Read section
8.12 and section 8.6, decisions 113 to 118; compiler/ml/ctype.ml
314-397 (flatten_fields, associate_fields, merge_row_fields,
filter_row_fields), 496, 1544-1600 (unify_univar, occur_univar),
1656-1679, 2901-3124, 3126-3198, 3200-3380; compiler/ml/btype.ml 112-170, 229-265, 753-804;
compiler/ml/subst.ml 132-215; in src/tc/relate.rs everything; in
src/tc/unify.rs the doc comments of Frame, FrameKind, PairSet and of
the fields of Checker, and the doc comments AND bodies of
Checker::{unify, unify_distinct, push_children, occur, restore,
fresh_marks, push_pair, push_lists}; in src/tc/expand.rs
Checker::{expand_head, expand_head_rigid, copy, link_memorized,
memorized_node, lower, cleanup_abbrev}; in src/tc/level.rs
Graph::children; in src/tc/rows.rs the comment "The reference of a
variant field" and Checker::{flatten_fields, build_field, cell_of,
open_row, flatten_row, merge_rows, unify_row, row_is_fixed, set_more,
resolve, settle, resolve_either, unify_row_field, read_types,
field_now_at, build_variant, drop_name_children,
forget_name_children, reify_row, duplicate, copy_refs, dup_cell,
begin_cell_session, end_cell_session, enter_poly, unify_univar,
unify_package, package_end, occur_univar} and field_repr,
each_field_types, cell_repr, cell_mutable.

A prototype of this slice was written in the design turn and the
nine tests of the slice passed against it. It is not in the
repository; it is a comment on pull request 393 (one fenced diff
against the skeleton, each body under a line `// R3I-PROTOTYPE`; take
the LAST comment that holds one, issue comment 7164565630: the
earlier two have the fault of decision 117 in duplicate_type; the
review corrected line numbers of ctype.ml in the skeleton's doc
comments after it was posted, so where a line it cites differs from
the skeleton's, the skeleton is right). You MAY read it. Three things it does are NOT yours to copy:
relate_fields and moregen_row put their clash path in a closure that
is called at once (write the cut of the frames out); all_distinct_vars
turns a clash of a safe expansion into the unexpanded node with
unwrap_or (a safe expansion does not clash: say so with the
expression you choose, no panic); its bodies carry no doc comment of
their own beyond the skeleton's. Where your code differs from it, the
doc comment decides.

Yours: the 23 bodies of src/tc/relate.rs that are `todo!("R3i")`:
Checker::{moregeneral, duplicate_type, moregen, equal, matches,
relate_run, relate_frames, moregen_pair, eqtype_pair, relate_children,
moregen_occur, is_variant, row_children, rigidify, all_distinct_vars,
rename_pair, normalize_renaming, relate_fields, relate_field,
moregen_row, filter_fields, moregen_row_field, eqtype_row}. Not yours:
Checker::{subtype, force_subtype, enlarge_type} (R3j: they stay
`todo!("R3j")`), the functions may_instantiate and ordered, the
allowance on `mod relate` in mod.rs (R3j removes it), and everything
else under src/tc, the seed lists of differential.rs included. If a
function you must call is not visible from relate.rs, stop and report
it.

Before your first commit, from the repository root:
  grep -c 'todo!("R3i")' compiler-rust/src/tc/*.rs | grep -v ':0$'
prints compiler-rust/src/tc/relate.rs:23;
  grep -c '#\[ignore = "R3i build"\]' compiler-rust/src/tc/*.rs | grep -v ':0$'
prints compiler-rust/src/tc/differential.rs:2 and
compiler-rust/src/tc/r3_tests.rs:7. When you end, both print nothing.

Commits, in this order, each pushed:
1. The 23 bodies. Run `cargo test --manifest-path
   compiler-rust/Cargo.toml --lib tc:: -- --include-ignored` in the
   background with its output in a file (it takes about twenty
   minutes; poll it): every test passes, the nine of this slice
   included, and the last line reads 353 passed, 0 failed, 0 ignored
   (the 344 that pass before your first edit and the nine). Never
   report a count you did not see.
2. The nine `#[ignore = "R3i build"]` lines removed; nothing else in
   a test changed. The same command without `-- --include-ignored`
   then reads 353 passed, 0 failed, 0 ignored.
End your turn after the second commit is pushed.

Steps (`#[cfg(test)] super::steps::tick()`): one a frame
relate_frames pops; one a node moregen_occur, duplicate_type (also one
a node its pass after the copy reads) and rigidify mark; one a field
row_children reads; one a merge step of relate_fields; one a field
filter_fields reads and one a field of r1 and r2 eqtype_row reads;
one an entry of each pass of all_distinct_vars; one an entry of the
first loop of normalize_renaming (the scan for a link; its rewrite
counts none).

Relations to hold: every tc:: test that passed before passes
unchanged; after every call of a relation `frames`, `saved`, `scopes`
and `trace` have the lengths they had (the tests assert it);
`equal` and `matches` leave every node that existed before the call
as it was; a unit that calls no relation reaches none of your bodies.

The first statement of `moregen` and of `equal`:
  debug_assert!(self.scopes.is_empty(), "a relation entered with a scope of universal variables open");
OCaml empties its list of scopes there (ctype.ml:3093, 3363) and does
not put the old value back; cutting `scopes` back to its length at
the entry is the same only when that length is zero. The prototype
does not have the assertion. If it fails in a test, stop and report
the test: do not take it out and do not change the test.

The hand-built tests are the judge, each with the OCaml lines it
follows. If a test fails where your code does what the cited lines
say, stop and report the test with the lines: do not change the test.
A seed listed in ROWS_OLD_EQUAL_DIFFERS, ROWS_OLD_NIL_DIFFERS,
UNIVARS_OLD_EQUAL_DIFFERS, UNIVARS_OLD_NIL_DIFFERS or
UNIVARS_OLD_FREE_UNIVAR_DIFFERS differs for the reason its doc
comment gives. You act on none of them; a
seed that is not listed and differs is read against the lines of 8.12
and reported: you pin none.

Report, before and after, the five unification operations of tc_kernel
(unify_vars, unify_ground1, unify_ground3, unify_datatype2,
unify_abbrev2, each minus its build_ twin) and instance7, copy7 and
checker_instance7, saying which commit each column was built from.
No target is set (decision 46); the slice adds no line to a function
they run.

Before each push, from compiler-rust, both print no warning:
  cargo clippy --all-targets -- -D warnings
  RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
(a public doc comment must not link a private item; a list in a doc
comment is indented as clippy asks). In your report, name each loop of
your bodies with the shape of relations_at_ten_thousand or of
relations_over_ten_thousand_fields_and_tags that runs it 10,000
times; the loops no shape runs that often are the walk of
moregen_occur (every shape calls it at the generic level, which skips
it), the common tags of moregen_row with its static scan and
moregen_row_field, the chain of variant
nodes in row_children and duplicate_type, the types of one field in
moregen_row_field and eqtype_row, the expansions of eqtype_row and
relate_fields, and the entries of normalize_renaming: name them as
such (the reviewer adds their tests: you do not add or change a test).

If git push or gh answers HTTP 401: commit locally, end the turn, and
say exactly what is local and at which commit.

Shortcuts that count as failure: a speculation in moregeneral or
moregen; equal or matches returning on a path that does not restore;
a recursion in any body (the frames, Graph::work); a `Vec`, a hash
map or a `Box` made in a call (the scratch vectors of Checker and
Extras exist); a second pair table, or `pairs` or `compatible` used
for `related`; the renaming as a list that is searched; a generation
of `marks` held across expand_head, unify, occur, occur_univar, lower
or copy; a reference node or a partner node pushed as a child
(row_children reads the chain of references); Checker::duplicate or
Checker::copy in place of duplicate_type's own copy; the restore of
duplicate_type after its pass over the copied nodes (it runs between
the copy and the pass: decision 117); a field's
mutability cell written or linked; a trace built; a new FrameKind; a
change of a signature, of a doc comment's stated cost, of a test or
of a seed list; a change under src/types. At most 900 lines of code
added outside doc comments (the prototype's part is 803, comments
inside bodies included).
```

The prompt of R3j, written in the eleventh skeleton turn. The searches
were run on the head that holds the skeleton and print what the prompt
says.

```text
R3j. Precondition: R3i is merged. From the repository root,
  grep -c 'todo!("R3i")' compiler-rust/src/tc/*.rs | grep -v ':0$'
prints nothing (on the head of the eleventh turn it prints
compiler-rust/src/tc/relate.rs:23). If it prints a line, stop.

Read section 8.13 and section 8.6, decisions 119 to 126;
compiler/ml/ctype.ml 96, 314-397 (flatten_fields, associate_fields,
merge_row_fields, filter_row_fields), 346-361 (object_row and its two
tests), 1240-1247, 1353-1369, 1544-1559, 1656-1679, 2110-2181,
2769-2773, 3392-3425, 3427-3593, 3611-3641, 3643-3706, 4028-4231;
compiler/ml/btype.ml 112-170, 205-212; compiler/ml/typecore.ml
3566-3612; in src/tc/relate.rs everything from `Checker::subtype` to
the end of the file; in src/tc/unify.rs the doc comments of the fields
of Checker and the doc comments AND bodies of Checker::{unify,
unify_distinct, undo_compress, restore}; in src/tc/expand.rs
TypeTable::{upper, info} and Checker::{expand_once, expand_head}; in
src/tc/rows.rs the comment "The reference of a variant field" and
Checker::{flatten_fields, build_field, cell_of, open_row, flatten_row,
merge_rows, field_now_at, enter_poly, unify_univar, instance_poly,
unify_package, merge_packages}, PackageDecls, Completion, PolyScope,
cell_repr, cell_mutable, cell_node, field_repr, published_slots.

A prototype of this slice was written in the design turn and the
eleven tests of the slice passed against it. It is not in the
repository; it is a comment on pull request 404 (one fenced diff
against the skeleton, each body under a line `// R3J-PROTOTYPE`; take
the LAST comment that holds one). You MAY read it. Things it does that
are NOT yours to copy: its closures inside bodies (`closed`, `kind`,
`row` in subtype_row and subtype_package: write them as private
functions or in line); the `map` over an array that makes the two
tuples of subtype_close; `self.trace.remove(0)` in force_subtype is
O(trace): keep it only if you say so in the doc comment's cost, or
shift once; it has no doc comment of its own beyond the skeleton's.
Where your code differs from it, the doc comment decides.

Yours: the 27 bodies of src/tc/relate.rs that are `todo!("R3j")`:
Checker::{subtype, force_subtype, open_scopes, enlarge_type,
subtype_frames, subtype_link, push_subtype, constrain, subtype_close,
subtype_pair, expands, object_row, subtype_constr, subtype_fields,
fresh_var, subtype_row, subtype_poly, subtype_package,
read_subtype_trace, on_path, enter_path, enter_row, has_constr_row,
enlarge_visit, enlarge_leave, enlarge_expansion, enlarge_variant}; the
eleven `#[ignore = "R3j build"]` lines of r3_tests.rs; the allowance
on `mod relate` in mod.rs. Not yours: every body of R3i (they are
built: you change none), every type, constant and doc comment of
relate.rs, the tests, and everything else under src/tc. If a function
you must call is not visible from relate.rs, stop and report it.

Before your first commit:
  grep -c 'todo!("R3j")' compiler-rust/src/tc/*.rs | grep -v ':0$'
prints compiler-rust/src/tc/relate.rs:27;
  grep -c '#\[ignore = "R3j build"\]' compiler-rust/src/tc/*.rs | grep -v ':0$'
prints compiler-rust/src/tc/r3_tests.rs:11. When you end, both print
nothing, and
  grep -n 'allow' compiler-rust/src/tc/mod.rs
no longer prints a line above `pub mod relate;`.

Commits, in this order, each pushed:
1. The 18 bodies of subtype and force_subtype (from Checker::subtype
   to read_subtype_trace, with open_scopes). Run, each by name with
   `-- --include-ignored`: a_coercion_collects_its_constraints_and_forcing_unifies_them_in_order,
   a_tuple_of_another_length_and_a_forced_clash_are_the_two_errors,
   the_arguments_of_a_constructor_follow_its_variance,
   abbreviations_expand_and_what_is_left_out_is_refused,
   objects_are_related_field_by_field, variants_are_related_tag_by_tag,
   a_constraint_keeps_the_scopes_it_was_made_under,
   packages_are_completed_and_tried, subtyping_at_ten_thousand: all
   nine pass.
2. The 9 bodies of enlarge_type (enlarge_type, on_path, enter_path,
   enter_row, has_constr_row, enlarge_visit, enlarge_leave,
   enlarge_expansion, enlarge_variant). the_enlarged_type_of_a_coercion_without_a_source
   and enlarging_at_ten_thousand pass. Then the whole filter in the
   background with its output in a file (about twenty minutes; poll
   it): `cargo test --manifest-path compiler-rust/Cargo.toml --lib
   tc:: -- --include-ignored` reads N + 11 passed, 0 failed, 0
   ignored, where N is what the same command reads before your first
   edit. Never report a count you did not see.
3. The eleven `#[ignore = "R3j build"]` lines removed; nothing else in
   a test changed.
4. The `#[allow(...)]` line above `pub mod relate;` in mod.rs removed
   (and its comment brought up to date); what the compiler then
   reports as unused in relate.rs is removed or used. The same command
   without `-- --include-ignored` reads N + 11 passed, 0 failed, 0
   ignored.
End your turn after the fourth commit is pushed.

Steps (`#[cfg(test)] super::steps::tick()`): one a frame
subtype_frames pops; one a constraint force_subtype unifies; one a
scope open_scopes pops or counts; one a pair read_subtype_trace reads;
one a spelling expands follows; one a node object_row follows; one an
argument of subtype_constr; one a merge step of subtype_fields and of
subtype_package; one a common tag subtype_row classifies; one a frame
enlarge_type pops; one a result enlarge_leave reads; one a field the
variant arm of enlarge_visit reads and one a field of each pass of
enlarge_variant.

Relations to hold: every tc:: test that passed before passes
unchanged; after every call of the three functions `subtyping`,
`frames`, `saved`, `scopes`, `enlarging`, `enlarged`, `Extras::fields`
and `Extras::row_scratch` have the lengths they had, `related` is
empty, and `Coercion::{quiet, held, dirty}` are 0, NONE, false (the
tests assert it); a unit that never coerces reaches none of your
bodies.

The first statement of `subtype` and of `force_subtype`:
  debug_assert!(self.scopes.is_empty(), "... entered with a scope of universal variables open");
If it fails in a test, stop and report the test.

The hand-built tests are the judge, each with the OCaml lines it
follows. If a test fails where your code does what the cited lines
say, stop and report the test with the lines: never edit the test.

Report, before and after, the five unification operations of tc_kernel
(unify_vars, unify_ground1, unify_ground3, unify_datatype2,
unify_abbrev2, each minus its build_ twin) and instance7, copy7 and
checker_instance7, saying which commit each column was built from. No
target is set (decision 46); the slice adds no line to a function they
run.

Before each push, from compiler-rust, both print no warning:
  cargo clippy --all-targets -- -D warnings
  RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
In your report, name each loop of your bodies with the shape of
subtyping_at_ten_thousand or enlarging_at_ten_thousand that runs it
10,000 times; the loops no shape runs that often are the names of two
packages in subtype_package, the spellings of expands, and object_row
beyond a flat field list: name them as such (the reviewer adds their
tests: you do not add or change a test).

If git push or gh answers HTTP 401: commit locally, end the turn, and
say exactly what is local and at which commit.

Shortcuts that count as failure: a speculation in subtype,
force_subtype or enlarge_type outside the trial of two packages; a
recursion in any body; a `Vec`, a hash map or a `Box` made in a call
(the scratch vectors of Checker and Extras exist); `frames`, `pairs`
or `compatible` used for `subtyping` or `related`; a new FrameKind or
Relation; a constraint unified inside `subtype`; a node built inside a
quiet region; the scopes of every constraint made again from its chain
in force_subtype; the visited list as a list that is scanned, or as
marks that stay for the walk, or in `Checker::marks`; a field's cell
shared by an enlarged field, or copied by a built field of
subtype_fields (the first is new, the second shared); an arm of R6e
built (int to float, records, variants); a trace built in
`Mode::Success`; a change of a signature, of a doc comment's stated
cost, of a test, of a body of R3i, or under src/types. At most 1,000
lines of code added outside doc comments (the prototype's part is 908,
comments inside bodies not counted).
```

The prompt of K2 is in section 8.7. The last prompt below is superseded by
decision 5 of 8.6: no builder starts a slice from it. R3e, R3f, R3n, R3g
and R3p, R3h, R3r, R3q, R3s, R3i and R3j have their own prompts above it.

```text
R3e..R3j. First commit, before any body: extend
differential::program_source and differential::type_text with your
slice's types behind a new Tier (R3e: object types; R3f: polymorphic
variants; R3g: records with a polymorphic field, first-class module
types; R3h: a GADT and Op::UnifyPattern; R3i: Op::Moregeneral, Op::Equal,
Op::Matches; R3j: Op::Subtype), with old_form and node_form printing them,
and a test like old_side_of_the_full_tier_is_not_vacuous that runs today.
Push it and wait for review of that commit. Then the bodies, one function
family a commit, in the order of the signatures in the file.
```

### 8.5 Open questions

1. **The occurrence walk per structure pair makes unification of deep
   equal types quadratic, as in OCaml and the old checker.** A deferred
   check (one acyclicity walk at the end of a top-level unification in
   `Mode::Success`) would make it linear. Recommended: not in R3; decide at
   R5c, when the profile of real units shows what `Checker::occur` costs.
2. **The memo of a module-alias expansion follows the old checker, not
   OCaml's source.** Recommended: keep it, since `both` mode compares with
   the old checker; revisit when the old checker is deleted (R8c).
3. **Memo entries a constructor inherits from the node whose expansion made
   it (`ref !abbrevs`, `Mlink`; ctype.ml:788-797) are not modelled.** They
   matter for recursive abbreviations through objects and variants.
   Recommended: R3f's generator extension includes a recursive variant
   abbreviation; if the `Full` tier then differs, slot 0 becomes an index
   into a small memo-list pool, in R3f.
4. **`check_abbrev_env` cleans the memos whenever the environment of an
   expansion differs from the previous one (ctype.ml:1163).** The skeleton
   takes a scope index (`Checker::set_env`); which scope changes count is
   R4's and R5b's to match. Recommended: R5b's `both` mode decides; the
   harness uses one environment.
5. **R3e to R3j have no acceptance tests in this pull request.**
   Recommended: accept, with the first-commit rule of 8.4; or run a second
   skeleton turn for them once R3c's `Full` tier runs.

### 8.6 The open questions as decided

Decided in review, before this section was merged.

1. **The occurrence walk per structure pair stays in R3, as OCaml has
   it.** The candidate to measure at R5c is named now, so that it is not
   rediscovered: in `Mode::Success` a failure only has to be detected, not
   located, because the unit is checked again in `Mode::Explain`. One
   acyclicity walk at the end of a top-level unification could therefore
   replace the walks per pair in that mode. Before it is built it needs a
   proof that unification terminates on the graph an omitted check leaves
   behind, the same expansion rule as `occur_rec` (a constructor that holds
   the node is expanded before the check gives up, ctype.ml:1396-1402), and
   the share of `Checker::occur` in the profile of real units. Until then
   the bounds of decision 6 hold and `Mode::Explain` never changes.
2. **The memo of a module-alias expansion follows the current checker**
   until R8c deletes it, because `both` mode compares shared nodes with it.
   The `ALIAS` flag's doc comment cites both sources. Whether the
   difference from OCaml's source is visible in a diagnostic is not known:
   a search for a program that shows it is a task of its own, and if one is
   found the current checker is corrected first and this rule follows it.
3. **Inherited memo entries are decided by a test, in R3f**: its generator
   includes a recursive abbreviation through a variant and one through an
   object. If the `Full` tier differs, slot 0 becomes an index into a pool
   of memo lists in that slice.
4. **Which scope changes clean the memos is R5b's**, judged by `both`
   mode. The harness keeps one environment.
5. **R3e to R3j get a second skeleton turn**, not a generator written by
   their builder: the tests of a slice are written by the designer. It runs
   when R3c's `Full` tier passes, extends the generator and the two forms
   tier by tier, proves each extension not vacuous on the current checker's
   side, and writes one prompt per slice.

Two notes for that turn. The forms of the harness print a constructor by
the last component of its path, which is enough while a generated program
is one unit; a tier that generates a second module prints the whole path.
And the ignored acceptance tests of R3a to R3d have not run: where one
contradicts the OCaml lines its doc comment cites, the builder reports the
test with those lines and the test is corrected, as `link_directions` was
in review (the survivor of two nullary constructors ends at the left
node's level, ctype.ml:2256).

Corrections after the first builder (R3a) stopped at three gaps of the
skeleton; all three were the skeleton's, not the builder's.

- `Checker::undo_compress` reads the trail: `graph::Change` and
  `graph::Speculation` have their fields readable inside `tc`.
- The tiers of the harness call only what their slice's dependencies
  have built. Below `Expand` the new side uses R1's `Graph::instance`,
  `Graph::copy` and `Graph::lower` and an empty declaration table (a
  structural program has no abbreviation); only the full tier calls the
  scoped `Checker::lower`; no tier of R3a to R3d fills the descriptor
  pools. Names are compared from `Expand` up until R3b's first commit, which
  turns them on for every tier; the slice of R3a and R3b that merges second
  merges trunk first, so its structural tier runs with names.
- The old side of the harness starts where a compilation starts: stamps
  above the predefined types' and the first level at the current stamp
  (`Ctype.init_def (Ident.current_time ())`). It started at level 0, below
  the binding time of `int`, so the scope test of `update_level` refused a
  binding of `int` to a variable of the starting level, which no
  compilation refuses (found by R3a's structural tier, seed 1000064).
- `link_directions`: the test's checker is one definition deep, so the two
  nullary constructors are at levels 2 and 3 and the survivor ends at 2.
  The review's own correction above had the levels wrong.

6. **In `Mode::Explain` a binding checks occurrence before it writes a
   level**, as `unify1_var` does (`occur` first, then `link_type`, then
   `update_level`, ctype.ml:2216-2225): two walks. The combined walk of
   `Checker::binding_walk` is for `Mode::Success` and for a binding inside
   a speculation whose owner restores, where what a failed walk lowered is
   either never observed or undone. In `Explain` a failed top-level
   unification undoes path compression only, so a level lowered before the
   variable was found would stay and could reach a printed type or a later
   generalization. `Explain` runs on failing units only; its cost is not
   gated.
7. **For R3c**: a `Linked` frame records the expanded left head and the
   right node, which is the trace pair only while the left head is its own
   expansion. With expansion the frame records the original pair, and the
   swapped side of ctype.ml:2299.

8. **The combined binding walk lowers what `update_level` lowers, no
   more** (review of R3a). `update_level` does not look below a node that
   is not above the target (ctype.ml:586); the occurrence test looks
   everywhere. The first build lowered every node above the target that
   the occurrence walk met, also below a node `update_level` stops at, so
   `Mode::Success` and `Mode::Explain` left different levels on a type
   whose inner node is above a node that holds it (a node made after
   `end_def` around nodes of the definition). The walk carries, per stack
   entry, whether it came from a lowered node.
   `binding_lowers_only_what_update_level_reaches` pins it in both modes.
   The generator of the harness does not reach such a type today; the
   second skeleton turn adds an operation that does.
9. **The binding walk's stack entries carry their kind in bits 30 and 31
   of the handle.** Section 3.2 reserves bit 31 of `Ty` for a frozen node.
   No local graph holds a frozen handle yet (a segment's nodes are copied
   in), so the two do not meet today, and a debug assertion in
   `push_flagged` says so. The slice that first puts frozen handles into
   child lists keeps them off this stack (a frozen node holds no local
   variable and has no level to lower: it is skipped at the push, one
   compare a child) or widens the entry, with a test of a binding to a
   type that holds a frozen child.
10. **A generalization forgets the nullary memo** (review of R3b). OCaml
    empties `simple_abbrevs` as the first step of `generalize`,
    `generalize_structure` and `generalize_expansive`
    (ctype.ml:519, 543, 668), and the current checker does the same. The
    skeleton had no entry for it: the kernel's `Graph::generalize` cannot
    reach the memo. `Checker::generalize` and `Checker::generalize_structure`
    forget it (one load and one untaken branch while no row is live) and
    then run the kernel's walk; every generalization of the checker goes
    through them, and the harness's from the tier that has a memo. Test:
    `a_generalization_forgets_the_nullary_memo`. R5b's
    `generalize_expansive` forgets it the same way.
11. **What unify2 expands** (review of R3c; the builder stopped at the
    skeleton's test, correctly).
    - Only two nullary constructors of one path link node to node
      (ctype.ml:2248-2257). Two nodes of one parameterised abbreviation go
      to unify2 like any other pair and both heads are expanded
      (ctype.ml:1785-1790, 2278-2281); the left node's expansion is linked
      to the right node. The skeleton's last block of
      `fixture_10_two_abbreviations_stay_two_nodes` and the relation in the
      R3c prompt said otherwise and were wrong; both are corrected.
    - The cached-expansion test of the nullary shortcut reads the node's
      own memo (ctype.ml:2254), which a nullary constructor never gets
      outside GADT instance tracing: its expansions go to the nullary memo
      (`proper_abbrevs`, ctype.ml:200-202). R3a read the nullary memo
      there; the test is gone until R3h needs the node's own memo.
    - A variable against a constructor it occurs in goes to unify2 with the
      pair as it is (ctype.ml:2240-2241), not to a retry inside the binding
      walk: `v` against `id<v>` with `type id<'a> = 'a` succeeds and links
      nothing. The occurrence the binding walk finds stands for
      `deep_occur` while no node has a row; R3e makes it cross rows, with a
      test.
    - In `Mode::Success` that walk has lowered the constructor's nodes to
      the variable's level before unify2 expands, where OCaml expands
      first. Accepted: unify2 lowers the same nodes at least as far
      (ctype.ml:2284-2285), and an expansion read from a memo is lowered to
      its node's level at every read (ctype.ml:1196-1200). The Full tier is
      the judge; R5c's `both` mode is the second.
    - Not reached by the harness, resting on unit tests or on reading
      alone: the reversed trace below a swapped unify3 in `Mode::Explain`,
      and a clash of the recursion repair. The second R3 skeleton turn adds
      an Explain-mode tier.

Decided in the second skeleton turn, each with what was run. The harness
additions are `differential::Plan` bits; every number below is one run of
100 programs by 100 operation sequences on trunk `5bf0f4c121`.

12. **The explaining mode agrees with the old checker, traces included**
    (`Plan` bit `EXPLAIN`). Both sides run in the explaining mode, a failed
    operation does not end the case, and the harness compares the trace pair
    by pair (numbered with the operands) and the graph the failure leaves.
    9,999 of 10,000 cases agree: 2,223 failing cases, 317 traces of more
    than one pair. The graph after a failed unification does *not* always
    print as before it: 2,215 failures leave it as it was and 503 do not,
    on both sides alike, because a failure in this mode undoes path
    compression and the descriptors of linked structures only
    (btype.ml:792-800, ctype.ml:2437); a variable bound or two nullary
    constructors linked before the clash stay
    (`the_explained_trace_of_a_fixed_case`). The reversed trace below a
    swapped unify3 (ctype.ml:2299-2303) is reached with a trace of two
    pairs by seed 2000091
    (`explain_reaches_the_reversed_trace_below_a_swapped_unify3`). A clash
    while `create_recursion` holds (ctype.ml:2308) needs the node-building
    operations of `BUILD` and is reached by seeds 2000018 and 13000074
    (`explain_reaches_a_clash_with_the_recursion_repair_pending`); no case
    of 10,000 fails inside the repair itself or below such a pair, because
    the second expansion of a type that expanded a moment before can clash
    only through a constrained parameter, and the generator declares none.
    That path rests on reading (ctype.ml:2428-2436) and on
    `recursion_repair_over_ten_thousand_elements_is_linear`.
    Not classified: seed 35000137. After a failed unification of generic
    operands the new side links a later instance's nullary constructor to
    the node that unification memorized (a generic node); the old side
    makes a fresh node. Neither `undo_compress` cleans a memo. Which of the
    two OCaml does is not known; the seed is pinned in
    `explain_plan_agrees_on_generated_cases`.
    With `BUILD`, seven more seeds differ, all one cause: the old checker
    lowers a type before the occurrence check of a binding fails, where
    `unify1_var` checks first (ctype.ml:2216-2225); the new side follows
    OCaml (decision 6). Read by hand for seeds 7000101 and 15000055.
13. **Scoped types** (`Plan` bit `SCOPED`). A program declares three late
    types whose scopes are one, two and three levels above the level the
    case starts at; the old side binds them to local identifiers with the
    next three stamps, the new side sets `TypeInfo::scope`. In
    `Mode::Success` 9,996 of 10,000 cases agree (2,291 failing cases), and
    removing the scopes from the new side is seen by generated cases
    (`Fault::NoScopes`). The four seeds that differ:
    - 16000145: two nullary constructors of one late abbreviation. The old
      checker's shortcut lowers without the environment
      (types/ctype.rs, `update_level(ctx, ..)` in the nullary case), so
      the node keeps its name below its scope; OCaml's lowers with it
      (`update_level !env t1.level t2`, ctype.ml:2255) and the node becomes
      its expansion, as on the new side. A fault of the old checker.
    - 49000200, 49000205 (and 49000183 with `BUILD`): the retry of
      `update_level` runs `backtrack snap` (ctype.ml:638-639), which
      forgets every memo (btype.ml:773-781), so the second pass expands to
      new nodes and unify2's `t2` is no longer `t2'`: unify3 runs unswapped
      and links the left expansion. The new side does that; the old side
      links the other way. Derived from the source, not run on OCaml.
    - 81000306: not classified.
    These are reported, not fixed: the old checker is not changed in this
    turn. `run_cases_except` pins the list so that a change on either side
    is seen.
14. **The recorded difference of R3d is observable: slice R3k corrects
    it.** When the retry of a lowering clashes too, OCaml keeps the levels
    the second pass wrote (ctype.ml:599, "Levels should be restored") and
    raises `Unify [(ty, newvar2 level)]`; `unify1_var` then puts back the
    variable's descriptor only (ctype.ml:2223-2225). R3d restores the
    levels and has no pair. In `Mode::Success` nothing reads either. In the
    explaining mode both are read: the escaping pair is the last pair of
    the trace, which is where the "would escape its scope" text comes from,
    and the levels decide what a later operation lowers and generalizes.
    Generated evidence: with `EXPLAIN | SCOPED | BUILD`, 69 of 10,000 cases
    differ; in seed 1000039 the levels kept at operation 10 decide what
    operation 13 lowers. `old_checker_keeps_the_levels_of_a_failed_retry`
    pins the old side today; `a_failed_retry_keeps_its_levels_in_the_
    explaining_mode` is R3k's acceptance test (ignored, `R3k build`).
    R3k, 60 lines in `expand.rs`: in `Checker::lower`, when the graph is in
    `Mode::Explain` and no speculation whose owner restores is open, the
    second pass runs without a speculation of its own (its writes stay)
    and, on a clash, pushes `[escaping node, a new variable at the target
    level]` on `Checker::trace` after the pairs the enclosing unification
    adds. `Mode::Success` and a lowering inside an owner's speculation are
    unchanged (the owner restores). Cost: none in `Mode::Success` (one
    compare of the mode on the clash path only).
15. **Decision 8 is reached by the generator** (`Plan` bit `BUILD`:
    `Op::Var`, `Op::Tuple`, `Op::Child`, and after an `EndDef` a tuple of
    two operands, a variable and their unification). 10,000 cases agree in
    `Mode::Success`. A new side that lowers every node above the variable's
    level, with no cut (`Fault::UnprunedBinding`, what the first build of
    R3a did), is reported by 111 of them.

16. **Inherited memo entries are observable: slice R3m** (decision 3,
    decided by a test as it asked). The harness prints objects and
    variants (`Plan` bits `OBJECTS`, `VARIANTS`) and generates the four
    recursive abbreviations `ro`, `po<'a>`, `rv`, `pv<'a>`. Instance, copy,
    generalize and lower agree on 10,000 cases with such types
    (`kernel_tier_agrees_on_objects_and_variants`). Expansion does not: 89
    of 10,000 cases differ with objects and 159 with variants, all read so
    far one cause. Observed on the old checker
    (`old_checker_links_a_recursive_occurrence_to_the_node_being_expanded`):

    ```text
    ro          expand: obj{hd: poly(int;); tl: poly(@0;); nil}     both sides
    po<string>  expand: obj{hd: poly(@1;); tl: poly(@0;); nil}      old
                        obj{hd: poly(@1;); tl: poly(po<@1>;); nil}  new
    rv          expand: [closed #Nil #Cons((int, @0)) | nil]        both sides
    pv<string>  expand: [closed #Nil #Cons((@1, @0)) | nil]         old
                        [closed #Nil #Cons((@1, pv<@1>)) | nil]     new
    ```

    `@0` is the node being expanded. The nullary cases agree because the
    memo all nullary constructors share already does it (decision 3 of
    8.2). With a parameter, `subst` memorizes the expanding node in its own
    memo before the body is copied and sets `abbreviations` to that memo
    (ctype.ml:1113-1126); the copy of a constructor then asks `find_repr p
    !abbrevs` and becomes a link to the node found (ctype.ml:780-782); a
    constructor that is not found gets a memo that continues with the
    expanding node's (`Mlink !abbreviations`, ctype.ml:793-799). So the
    entries a node sees are its own and those of the chain of nodes whose
    expansions made it.
    R3m, in `expand.rs`. The rule is fixed: when `subst` copies a
    constructor with arguments, it walks the chain of the expanding node
    (the node, then the node whose expansion made it, and so on); the
    first chain entry that names the copied constructor's type and has a
    live expansion makes the copy a link to that entry's node
    (`link_node`); otherwise the copy's chain continues with the expanding
    node's. A node whose memo was cleaned ends the chain (`abbr := Mnil`
    cuts the list, btype.ml:623-627); a node whose entry was forgotten does
    not (`forget_abbrev` removes one entry and keeps the tail,
    btype.ml:636-647). Acceptance:
    `expand_tier_agrees_on_recursive_abbreviations` (ignored, `R3m build`).
    The layout is **not** fixed, and R3m is not handed to a builder before
    it is. Two facts found late in this turn rule out the first idea (a
    dense `Vec<Ty>` of parents by node handle): an entry outlives its node's
    descriptor (OCaml's entry holds the path and the node, and stays when
    the node is linked to another, so the type index and slot 0 cannot be
    read back from the parent node), and `Graph::generalize` visits slot 0
    as a child (`children(node, true)`, tc/level.rs), so slot 0 cannot
    hold anything but a node without a change in the kernel. The two
    layouts that remain:
    - a pool `Memo::chain` of 16-byte rows `{node, type index, parent row,
      slot-0 list index}`, one per constructor with arguments made by an
      expansion whose manifest has one, found from a constructor by a dense
      `Vec<u32>` indexed by its slot-0 list index (4 bytes per list slot up
      to the highest one written); slot 0 and the kernel stay as they are.
      Recommended.
    - slot 0 holds a flagged row index (what decision 3 foresaw), the row
      holds the expansion, and `Graph::children` learns to follow it: no
      dense table, one more compare on every generalization of a
      constructor, and a change in tc/level.rs.
    Either way a manifest whose body has no constructor with arguments
    pays nothing (a flag where the manifest is made), and the step relation
    is: expanding the heads down a chain of n nested `po` nodes at
    n = 10,000 takes at most 11 times the steps of n = 1,000.
17. **The forms of extended nodes.** An object prints `obj{fields}`, a
    field `name: type; rest` (`name!` when mutable), the end of a list
    `nil`, a variant `[closed fixed #tag(type) #tag?cm(types) #tag- |
    more as name<arguments>]` with the fields of a chain of rows outermost
    first and the innermost row's flags (`row_repr`, btype.ml:126-135), a
    polymorphic type `poly(body; variables)`, a universal variable
    `!name`. Every node is numbered as before, so sharing below a row is
    compared. Not printed: which mutability *cell* a field has. Two fields
    that share a cell and two that have equal cells print alike.
18. **What the designer of R3e to R3j needs from this turn** (their
    hand-built tests and prompts were not written; see 8.1).
    - *Descriptor rows are shared by every instance of a scheme* (a node's
      `a` is copied as stored). Unification must therefore never write a
      descriptor row in place. A field built for the fields one side lacks
      (`build_fields`, ctype.ml:325) has the name and the cell of the
      field it copies, so it reuses that field node's descriptor index and
      needs no new row. A row changed by `unify_row` is a new `variants`
      row and a new descriptor.
    - *Mutability cells are duplicated by an instance* when the row ends in
      a generic variable (`dup_mutability`, `row_terminator_generic`,
      btype.ml:457-530), one duplicate per class per copy. A template
      instance copies nodes as stored and so shares the scheme's cells.
      The kernel tier does not see this (decision 17). R3e has to decide
      where the duplicate is made (a pass over an instance's field nodes,
      run only for a template that has one, or cells as nodes of the
      graph), and its harness has to print cell classes before that
      decision can be tested. A promotion (`unify_mutability`,
      ctype.ml:2520-2539) needs a mutable field in a generated program;
      which surface syntax gives one was not established.
    - *An object's field is a `Tpoly` with no variables* in every generated
      type (`poly(int;)` above), so R3e's generator already reaches
      `Tpoly (t1, []), Tpoly (t2, [])` (ctype.ml:2413), which is R3g's
      arm. Either that arm moves to R3e or R3e depends on R3g.
    - *Decision 9* (bit 31 on the binding walk's stack): nothing built or
      designed in R3 puts a frozen handle in a child list; `Extras` rows
      name children by slot, and `from_segment` copies rows, not nodes. It
      stays with the slice that first shares a segment's nodes without
      copying them (R5a at the earliest).
    - *The old checker is not the judge everywhere.* Decisions 12 and 13
      list seeds where it departs from ctype.ml. A slice whose differential
      test differs must read the OCaml arm before it follows either side.

Decided in the review of the second skeleton turn (trunk `0b175b7d0d`).
They bind the builders and the third skeleton turn.

19. **R3m's layout is the pool** (the first of the two layouts of decision
    16). Rows of 16 bytes, found from a constructor through a dense table;
    slot 0 holds a node and nothing else, the kernel (`graph.rs`,
    `level.rs`, `template.rs`) is not changed, and a generalization pays
    nothing for it. Left to the third turn and fixed there (decision 26):
    the key of the dense table, the memory per unit as a formula, and the
    step relation of decision 16 as a test. A manifest whose body has no
    constructor with arguments pays nothing.
20. **The three places where the old checker departs from `ctype.ml` are a
    task of their own**, not part of a slice: the nullary shortcut lowers
    without the environment (decision 13, seed 16000145); a binding lowers
    before its occurrence check fails (decision 12, the seven `BUILD`
    seeds); the retry of a lowering does not forget the memos (decision 13,
    seeds 49000200, 49000205, 49000183). The old checker is changed for one
    of them only after a source program is found on which the OCaml
    compiler and this one differ in a diagnostic or in acceptance; a
    departure for which no such program is found is recorded and left as it
    is. When one is fixed its seeds leave the pinned lists of
    `run_cases_except`. A pinned list only ever shrinks.
21. **Seeds 35000137 and 81000306 stay pinned and unclassified.** Telling
    which side OCaml agrees with needs the harness's operations run on the
    OCaml compiler, which is a second harness; it is not built now. Both
    are read again when `both` mode runs on real programs (R5c) and shows
    whether either pattern occurs in one.
22. **Two polymorphic types without variables are R3e's**
    (`Tpoly (t1, []), Tpoly (t2, [])`, ctype.ml:2413): the type of every
    object field is one (decision 18), so R3e cannot pass its own tests
    without the arm. R3g keeps the arm with variables (`enter_poly`,
    ctype.ml:2414-2415).
23. **K2b is designed and not built** (8.7, "The deferred occurrence
    check"): one acyclicity check per top-level unification. It waits for a
    profile of real units at R5c that shows the occurrence walk above 2% of
    checking. This closes decision 1.
24. **Step counts under K2.** A step test whose pinned count goes *down*
    because item (a) or (d) of 8.7 removed work is lowered to the count
    observed, in the commit of that item; the pull request lists the test,
    the old count, the new count and the item. A count that goes up, a
    relation between two sizes that changes, or any other assertion that
    fails: the builder stops and reports.

Decided in the review of R3k.

25. **Whoever ignores a clash cuts the trace back to its length before
    the call.** OCaml carries the trace in the exception, so a `try ...
    with Unify _` drops it with the exception. Here the trace is a vector
    (`Checker::trace`), so every site that swallows a `Clash` in the
    explaining mode truncates the vector to the length it had before the
    call it swallowed. R3k does so where the lowering of a memorized
    expansion is ignored (ctype.ml:1196-1201). One site is known and not
    covered: in `Checker::subst`, the lowering of an argument to the
    node's level and the unification of a constrained parameter, when a
    safe expansion fails and the clash is turned into "does not expand"
    (`try_expand_safe`, ctype.ml:1251-1256; `expand_head_opt`,
    ctype.ml:1330-1335). It needs a type with a constrained parameter to
    reach, and no generated program declares one. The slice that first
    generates constrained parameters adds the truncation there with a
    test; the design of R3m (decision 26), which changes `subst`, changes
    nothing on that path and states the rule in `subst`'s doc comment.

Decided in the third skeleton turn (trunk `0b175b7d0d`), each with what
was run. "Prototype" means bodies written to try a design against its
tests and taken out again before the commit: no slice body is on trunk
from this turn.

26. **R3m as designed** (`expand::Chains`; decisions 16 and 19).
    - *What a row is.* One memo reference of a constructor with arguments
      (OCaml's `abbrev_memo ref`), reduced to what a copy reads: the one
      entry slot 0 holds (`node`, `type_index` with a bit for a private
      expansion) and the reference the list continues with (`parent`, the
      `Mlink` of ctype.ml:796-798), plus its own `slot`. 16 bytes
      (`expand::tests::sizes`).
    - *The key of the dense table is the list index of slot 0, not the
      node handle.* Slot 0 *is* the reference: two nodes that share a list
      share it. A node of a type written through a module alias and the
      node it expands to share one list (`expand_alias`; `newty2 level
      (Tconstr (path', args, abbrev))`, ctype.ml:1214). Keyed by node, the
      target node would have no row: expanding it would start a new chain,
      and a constructor of an outer type copied by that expansion would not
      link to the outer node, where OCaml, reading the shared `abbrev`,
      links it. `Memo::memorized` holds slot indices for the same reason.
    - *The flag.* `expand::INHERITS` in `TypeInfo::flags`: the manifest's
      template has a constructor with arguments whose type expands
      (`ABBREV`, `PRIVATE` or `ALIAS`). Only such a copy can be linked (an
      entry exists for an expanded node only) or be expanded later (and
      read its chain). It is narrower than "a constructor with arguments"
      of decision 19: `type t<'a> = array<'a>` pays nothing either. The
      test of the bit is on the row `expand_once` has already loaded. It
      is set by `TypeTable::mark_manifests` when every row exists (a
      manifest names later declarations of its recursive group), one pass
      over the manifests' template nodes.
    - *When a row is made.* By `subst` for the node of an `INHERITS` type
      that has none (`chain_entry`, which also writes the entry); and in
      the pass over the instance's nodes for each constructor with
      arguments of a type that expands and that no chain entry links
      (`inherit`), with `parent` the expanding node's row. Nowhere else:
      an instance or a copy outside an expansion starts no chain
      (`abbreviations = ref Mnil`, ctype.ml:1128).
    - *When the chain ends.* An entry is live while its slot 0 holds a
      node. `forget_abbrev` empties the slot and nothing else: the walk
      passes the row and goes on (`forget_abbrev_rec` returns the tail,
      btype.ml:636-644). A cleanup empties the slot *and* sets the row's
      `parent` to none (`abbr := Mnil`, btype.ml:626: the whole list of
      that reference is gone). The row itself stays, because a copy names
      the reference, not its content: when the node is expanded again, the
      copies of its first expansion see the new entry. Observed on the old
      checker with three abbreviations through objects
      (`old_checker_inherits_entries_along_the_chain`): with every entry
      in place the `m3` node's expansion links `m1<'a>` and `m2<'a>` to the
      two nodes above it; after a cleanup and a second expansion of the
      `m2` node it links `m2<'a>` and makes a new `m1` node.
    - *What a restore does.* Nothing of its own. `Graph::restore` puts
      descriptors back and truncates no pool, so every row still names a
      node and a slot that exist; `Checker::restore` then runs the cleanup
      above, as `backtrack` does (btype.ml:779). Rows are not logged in the
      trail.
    - *A lookup of an expansion reads the chain too* (`find_expans` goes
      through `Mlink`, btype.ml:618), which decision 16 did not say. It
      can only find something for a node whose own slot is empty and whose
      chain has a live entry of its own type: a private entry (which
      `find_repr` skips, so the copy was not linked), or an entry written
      after the copy was made (the revival above). `expand_once` asks
      `inherited_expansion` only on a miss, for an `INHERITS` type.
    - *Memory per unit*: `16 * rows + 4 * (S + 1)` bytes, `S` the highest
      slot-0 list index that has a row; `rows` = the expanded nodes of
      `INHERITS` types that had none + the constructors with arguments of
      expanding types that those expansions copied and did not link. Zero,
      with no allocation, for a unit that expands no `INHERITS` type. Rows
      are freed when the worker resets the checker, not by a cleanup.
    - *Cost.* A type without the flag: nothing beyond the bit test. With
      it, per expansion: one row write, one pass over the instance's nodes
      (the pass the nullary memo already makes when it is live; the two
      share one loop, `link_memorized`), one `TypeInfo` load per copied
      constructor with arguments, and for each of those that expands a
      walk of the chain. A chain is as long as the number of expansions
      above the copy that did not link it, which is at most the number of
      `INHERITS` types on that path while entries are live; OCaml's
      `find_repr` walks the same list. The regular recursive case is one
      row: `expanding_the_heads_down_nested_recursive_nodes_is_linear`.
    - *Changes to the skeleton, all in `expand.rs`.* `Memo::chains`;
      `subst` takes the `TypeInfo` row in place of the manifest index and
      calls `Graph::instance` and the pass itself; `link_memorized` takes
      the chain; `expand_once` loads the row before the memo-hit branch on
      a miss; `cleanup_abbrev` indexes its loop to call `cut_chain`. Every
      new call is behind `INHERITS` or a non-empty pool, neither of which
      exists until R3m is built: `an_abbreviation_that_inherits_nothing_
      reads_no_row` (runs today) pins the steps of an expansion at the
      count observed before the change.
    - *One test of the skeleton changes when R3m is built*:
      `expand::tests::table_from_ten_thousand_declarations_is_one_pass`
      pins `2n + 1` steps for `from_segment`; the marking pass reads the
      three template nodes of each of its n manifests, so the count becomes
      `5n + 1`. Its hand-built segment had no template nodes; it has them
      now.
    - *Run.* With a prototype of the five bodies: the two hand-written
      chain cases, `expand_tier_agrees_on_recursive_abbreviations` (10,000
      cases; 248 differed before), the three hand-built tests of
      `r3_tests.rs`, and every other `tc::` test unchanged (the full tier
      and the five plans with their pinned seeds).
27. **R3e as designed: objects, fields, mutability cells.**
    - *(a) A cell is a node of the graph that no node has as a child*
      (`rows::cell_node`: a variable with no name, `b` 1 when mutable; a
      link when its class was merged). A field's descriptor row holds the
      cell's handle. So a promotion is `Graph::write` and a merge is
      `Graph::link`: logged in the trail inside a speculation and undone
      by its restore, as `set_mutability` logs `Cmutability`
      (btype.ml:745-747), with no log of its own and no change in the
      kernel; and no walk of a type (lower, generalize, occur, instance)
      meets a cell or pays for one. The two layouts not taken: cells in a
      pool of their own need an undo log tied to `Graph::speculate`, which
      has no hook; cells as a list slot of the field make every walk load
      one more node per field, and tie "duplicate or share" to the cell's
      level, where OCaml ties it to the row's last node
      (`row_terminator_generic`, btype.ml:478-506).
    - *Where the duplicate is made.* In the pass over the nodes a copy
      session made (`Checker::link_memorized` with `cells`), per field
      node: `Checker::dup_cell`. A field whose row ends in a variable the
      session made (handle at or above the session's first node: the copy
      of a generic variable) gets a new descriptor row and the duplicate
      of its cell's class, one duplicate per class per session (the source
      class links to its duplicate until `end_cell_session`, as
      `dup_mutability` does, btype.ml:462-472). Any other field keeps its
      descriptor row and so its cell. The terminator of a row is found
      once per session (marks), not once per field.
    - *What a template without such a field pays: nothing.* The caller of
      an instance holds one bit per template: `Checker::instance_open`
      runs the pass, `Checker::instance` is unchanged (its test of
      `Memo::live` is the only one). The bit is `rows::template_has_open_
      row`: some field of the template has a variable of the template as
      its rest (the last field of an open row), one pass over the
      template's nodes, computed once by whoever makes the caller's row.
      R3 has two callers: an expansion (`TypeInfo` flag `OPEN_ROW`, set in
      the pass of `mark_manifests`) and the harness (per value). R5a's
      binders and imported values compute it where they are made. The
      general copy (`Checker::copy`) has no template: it runs the pass
      when the graph has any descriptor row.
    - *The harness prints cell classes* (`Plan` bit `CELLS`): `name^k`,
      `k` numbering classes at first visit across the operands, and
      generates `@set` fields. Observed on the old checker
      (`old_checker_duplicates_the_cells_of_an_open_row`): two instances
      of an open row have classes `0 1` and `2 3`, two of a closed row
      `4 5` and `4 5`; a copy of a generalized open row duplicates once
      per copy. With classes printed the kernel tier (no duplicate on the
      new side) differs on 2,877 of 10,000 cases: the classes are
      compared.
    - *(b) The surface syntax of a mutable field* is the attribute `@set`
      on a field of an object type (typetexp.ml:609-616). The parser takes
      it on a field that is not the first of an inline object type and on
      any field of a declared one; `{..@set "x": int}`, which is how the
      printer writes an open row whose first field is mutable, does not
      parse (observed: a syntax error; reported, not fixed). A promotion
      is reached by a write to a field of an open row (`o["x"] = 1`:
      fixture `object_open_write_readonly_caller.res`, whose parameter
      prints as `{..@set "x": int}`) and by unifying an open row with a
      row that has the field `@set`. R3e needs `unify_mutability`: the
      generated cases with `CELLS` reach both clashes and both promotions.
    - *(c) Unification never writes a descriptor row in place.* Rows are
      shared by every instance of a scheme. A built field
      (`build_field`) reuses the descriptor index of the field it copies;
      a duplicate is a new row; the trace pair of a failed field makes one
      `Nil` row, on the failure path. Tested by hand
      (`fields_a_side_lacks_are_built_on_one_row_variable`,
      `mutability_is_promoted_...`) and on every generated case: `run_new`
      compares the descriptor, variant and row-field rows the case started
      with after every operation.
    - *(d) Two polymorphic types without variables are R3e's* (decision
      22): `Checker::extended_children`.
    - *The order of work of `unify_fields` on the explicit stack*
      (ctype.ml:2467-2518). It links nothing and cannot fail itself: it
      flattens and sorts both lists, makes `va`, builds the two lists of
      missing fields in one backward merge, and pushes frames so that they
      are popped as OCaml recurses: the pair `(built1, rest2)`, the pair
      `(rest1, built2)`, then one `Field` frame per common field in name
      order. A `Field` frame runs `unify_mutability` with the openness
      read before the rests were unified, then the pair of the two types.
      In the explaining mode a `Fields` frame below them restores the two
      rests on a failure and a `FieldEnd` frame below a field's types puts
      the pair of two one-field lists into the trace.
    - *Names are ordered by text* in `flatten_fields` only; everywhere
      else a name is its index. `Extras::names` holds the text; for a
      graph made from a segment it is a copy of the segment's strings.
      R5a decides whether a unit being checked fills it from the worker's
      name table or `Extras` borrows that table; nothing in R3 depends on
      which.
    - *The occurrence tests.* `occur_rec` does not enter an object
      (ctype.ml:1403) and `deep_occur` does (ctype.ml:1735). R3c let the
      binding walk stand for `deep_occur` in the route of a variable
      against a constructor (decision 11); with objects the two differ,
      and R3e makes the route's test cross rows:
      `the_route_of_a_variable_crosses_an_object_and_the_occurrence_test_
      does_not` (the constructor ends at level 1, not 2).
    - *Changes to the skeleton.* `rows::Extras`: `mutabilities` is gone,
      `names`, `fields`, `session` are new, `from_segment` takes the graph
      and pushes the cell nodes; `flatten_fields` sorts; new signatures
      `make_rowvar`, `build_field`, `unify_field`, `unify_mutability`,
      `field_trace_pair`, `instance_open`, `dup_cell`, `end_cell_session`,
      `template_has_open_row`. `unify.rs`: `FrameKind::{Fields, Field,
      FieldEnd}` with their arms in `run_frames` and `explain_failure`;
      `unify3` takes two field nodes before the link and sends two other
      extended descriptors to `extended_children` (which replaces
      `extended_pair`). `expand.rs`: `OPEN_ROW`; `link_memorized` takes
      `cells` and no longer visits nodes the pass itself makes;
      `mark_inheriting` is `mark_manifests`.
    - *Not run.* The hand-built tests of R3e call bodies that are
      `todo!`: their expectations are read from the OCaml lines each one
      quotes, and where the old checker can show the same fact it does, in
      a test that runs today. No prototype of R3e was built.
28. **R3f is not designed in this turn.** The turn ended at R3e; R3f has
    its generated-case test and no hand-built tests, step relations or
    prompt, and no builder starts it. What its designer needs, read from
    the source and not run:
    - *The arms, in OCaml's order* (ctype.ml:2541-2641). `unify_row`:
      `row_repr` of both; nothing when the two `row_more` are one node;
      `merge_row_fields` (sorted by tag text unless one side has one tag
      the other lacks, ctype.ml:380-386); `more` is `rm1` when row 1 is
      fixed, else `rm2` when row 2 is, else a new variable at the lower of
      the two levels; `closed` is either row closed; the empty-type clash
      (ctype.ml:2565-2573); the name (ctype.ml:2574-2586); `set_more row2
      r1` then `set_more row1 r2`, each of which filters the other side's
      fields when `closed`, clashes when a closed or fixed row would gain
      a field, and links the row's `more` to a **new generic variant
      node** holding the fields it lacked (ctype.ml:2597-2619); then
      `unify_row_field` per common tag in merged order; then a static row
      1 gets `Tnil` as its `more`. On any failure `rm1` and `rm2` get
      their descriptors back.
    - *What a changed row allocates* (decision 18): one node at the
      generic level, one descriptor row (12 bytes), one `variants` row (28
      bytes), one `row_fields` row (20 bytes) and the list slots of its
      types for each field the other side had and this one lacked, plus
      the slot of `more` and of the name's arguments. Nothing when the
      other side had no such field and the row is fixed.
    - *The fact that blocks the layout.* A field `Reither (c, tl, m, e)`
      holds a reference `e` that is **shared**: by the two fields
      `unify_row_field` makes for one tag (`let e = ref None`,
      ctype.ml:2700-2704; the one `f` of PR#7496, ctype.ml:2659-2662), and
      by a copy of a row whose row variable is not generic (`let e = if
      keep then e else ref None`, btype.ml:374, with `keep = more.level <>
      generic_level`, ctype.ml:806), which is every instance of an
      annotation's type (`generalize_structure` leaves the variables at
      their level, O10). And `row_field_repr` reads through it: the
      children of a variant node are those of the *resolved* field, with
      the types met on the way (`row_field_repr_aux`, btype.ml:112-119).
      So: (1) a resolution cannot be a write to a `row_fields` row
      (`RowFieldRow::link`), because rows are shared by every instance of
      a scheme and a generic row's instance must have references of its
      own; (2) it cannot be a cell that no node has as a child, as a
      mutability cell is, because resolving `Reither (false, [], _, e)`
      with `Rpresent (Some t)` (ctype.ml:2710-2716) or with another
      `Reither` gives every variant node that shares `e` a child that is
      not among its list slots, and the level walk, generalization and
      `deep_occur` must reach it; (3) a field resolved to `Rabsent` stops
      being a parent of its types, which the slots of the node still
      name.
    - *The two layouts that remain*, neither tried. (a) The reference is
      a node the variant node has as a slot: unresolved, it has no child;
      a resolution writes it (a link to the reference it now equals, or a
      descriptor with the resolved types as its slots). Walks then reach
      what OCaml reaches, sharing is node identity, the trail undoes it,
      and an instance copies it when it is generic. What must be shown:
      that "generic" for such a node coincides with `keep` (the level of
      `more`), in particular under `generalize_structure`, which must
      treat it as a variable. (b) References in a side pool with the
      resolution's types, and the variant node rewritten (`Graph::write`:
      new slots, new descriptor) at every resolution, with the sharers of
      a reference found through a list kept in the pool. Recommended
      first step of the next turn: print reference classes in the
      harness's variant form (as `CELLS` does for cells), generate an
      annotation instantiated twice, and observe on the old checker
      whether two instances share a resolution; then choose.
    - *The duplicate at an instance* follows from it and uses R3e's pass
      (`link_memorized` with `cells`): a variant node with an `Reither`
      field whose `more` the session made needs references of its own
      (`copy_row`, btype.ml:366-392), exactly as a field of an open row
      needs a cell of its own. `template_has_open_row` grows that case.

Decided in the review of the third skeleton turn (trunk `2f5d0c3b8a`).
They bind the builders and the fourth skeleton turn.

29. **R3f gets a design turn of its own, and it starts in the harness.**
    The forms of both sides print the class of every `Reither` reference;
    the old checker is then asked whether two instances of an annotation's
    type share a resolution. Only after that is the layout chosen, in the
    direction decision 28 recommends: the reference is a slot of the
    variant node. No builder starts R3f before that turn is merged. The
    turn is decision 34.
30. **The hand-built tests of R3e were not run, and that is accepted**
    with the rule its prompt has: a test that contradicts the OCaml lines
    it quotes is reported with those lines, and the reviewer reads them.
    The R3e builder's first commit is reviewed against the tests before
    the second is opened.
31. **`{..@set "x": int}` is printed and not parsed.** It is not part of
    R3. It is a task of its own only where this compiler and the OCaml
    compiler differ on it, or as a syntax fix upstream; it is noted for a
    later check with both compilers.
32. **Where the text of a field name comes from while a unit is checked
    is R5a's decision** (the worker's name table, or a copy in
    `Extras::names`). Nothing in R3 depends on which.
33. **A chain through n distinct abbreviations costs a walk of up to n
    rows per copy**, as `find_repr` costs OCaml (ctype.ml:720-724). It is
    left as it is; chain lengths are read when `both` mode runs on real
    programs (R5c).

On record for R5 from the same review: mutability cells live in the
worker's graph, so the publication of a unit writes each field's cell as
the value of its class representative; the names replay of `both` mode
does not see cells, and R5c's comparison of signatures is where a wrong
class shows.

Decided in the fourth skeleton turn (trunk `2f5d0c3b8a`, merged with
`c4e9326eba`), each with what was run. No prototype of R3f or R3n was
built in this turn: the expectations of their ignored tests are read from
the OCaml lines each quotes, and wherever the old checker can show the
same fact it does, in a test that runs today.

34. **R3f and R3n as designed: variant rows and their references.**
    - *The harness prints reference classes* (`Plan` bit `REFS`): a field
      that is still `Reither` prints `#A?^k(types)`, `k` numbering the
      references at first visit across the operands, on both sides. The
      operations get `Op::GeneralizeStructure`
      (`generalize_structure`, ctype.ml:524-544), which is what makes an
      annotation's type: a generic row over a row variable that is not
      generic. Self-test: `rows::tests::a_field_is_read_through_its_
      references`. The deliberately wrong new side is the kernel tier,
      whose copy is R1's and knows no reference:
      `reference_classes_show_a_missing_share` (it agrees where
      references are new, differs on the fixed annotation case, and
      differs on 70 of 10,000 generated cases).
    - *Observed on the old checker*, each in a test of
      `differential::tests` that runs today:

      | Question | Observed | Test |
      |---|---|---|
      | Do two instances of a scheme share a reference? | No: `^0 ^1`, then `^2 ^3` | `old_checker_shares_the_references_of_an_annotation` |
      | Do two copies of a generalized value's type? | No: every copy has its own | same |
      | Do two copies of an annotation's type? | Yes: both print the source's `^0 ^1` and its row variable; each has its own copy of the argument types | same |
      | What does a resolution do to the sharers? | Every holder sees it: `#A` becomes present in the source and in the other copy too, each with its *own* argument (`Rpresent (Some (List.hd tl))`, btype.ml:117); with `[#B]`, `#A` is absent for all three and the shared row variable is `Tnil` | `old_checker_resolves_a_shared_reference_for_every_holder` |
      | What does a copy taken after a resolution have? | The resolved field, and it shares what is still `Reither` | same |
      | What does a failed unification leave resolved? | Everything it resolved before the clash: `set_row_field` logs `Crow` (btype.ml:742-744) and a failure undoes compression and the linked node's descriptor only | `old_checker_keeps_a_resolution_after_a_failed_unification` |
      | Is a field resolved to absent still a parent of its types? | No, for any holder: lowering the *other* copy's row leaves the variable `#A` named where it was | `old_checker_does_not_reach_the_types_of_an_absent_field` |

      This is `keep = more.level <> generic_level` (ctype.ml:806) with
      `let e = if keep then e else ref None` (btype.ml:374), and
      `iter_row` visiting what `row_field_repr` gives (btype.ml:229-236).
    - *The layout: the reference is a slot of the variant node, and what
      it names is a node* (`rows.rs`, "The reference of a variant
      field"). A published row has no references: a node of one is
      *unopened* and each `Reither` field stands for a reference nothing
      else holds. `RowFieldRow::link`, which was always `NONE`, is the
      slot the reference will have, after the published slots
      (`rows::published_slots`; `Extras::from_segment` fills it in its
      own copy of the rows). `Checker::open_row` gives a node those
      slots, in a new list (the node is written once; its descriptor
      index and its rows are untouched). From then on the field is a
      chain of *reference nodes* from that slot: an unresolved reference
      is a variable with no name (`rows::ref_node`); a resolved one is a
      `TUPLE` node that is not `EXTENDED` whose `a` says `Rabsent`,
      `Rpresent` (no slot, or the type) or `Reither` with `c` and `m`
      (the types, then the next reference). The field's own types are
      the first link of the chain: opening moves them into a `Reither`
      node of the node's own, and the node's published type slots for
      that field then name that node. `rows::field_repr` is
      `row_field_repr`: one loop, no write.
    - *Why that shape.* (1) Nothing shared is written: rows stay as
      published, and what differs between two instances is in their
      nodes. (2) A resolution is `Graph::write` of one reference node:
      the trail undoes it inside a speculation with no log of its own,
      and `graph.rs`, `level.rs` and `template.rs` are **not changed**.
      (3) The children of a variant node are those of the resolved
      field: every walk reaches the chain as ordinary children, so a
      type a resolution added is lowered, generalized and found by
      `deep_occur`. (4) A field resolved to absent stops being a parent
      of its types because the types hang under the field's own chain
      node, not under the variant node: `Checker::settle` rewrites that
      node (one write per holder of the reference, found through
      `Extras::holders`, 8 bytes each; a present field keeps its first
      type only). (5) Sharing is node identity: two fields share a
      reference when their chains end in one node.
    - *"Generic" coincides with `keep`.* A reference is a variable, so
      `generalize_structure` leaves it at the level it leaves the row
      variable at, and `Graph::copy` shares a node that is not generic:
      the copies of an annotation's type share its references with no
      code. The two cases where the levels of the reference and of
      `more` differ, and the unopened source, are `Checker::copy_refs`
      (R3n), whose rule is `keep` read from `more`, not from the
      reference.
    - *What each walk pays.* An unopened node: what it paid as
      published, one push per slot. An opened node with `k` `Reither`
      fields of which `t` have types: `k` more pushes, and `k + t` more
      nodes visited once each (lower, generalize, the occurrence tests,
      a copy). A row without a `Reither` field is never opened and pays
      nothing; that is every row of a closed variant type written in a
      declaration. An instance of a template pays nothing: a template
      made from a segment has unopened rows.
    - *Sizes* (`rows::tests::sizes`, `segment::schema_tests`): `Holder`
      8, `FieldRepr` 16, `FieldRef` 12, `VariantRow` 28, `RowFieldRow`
      20, `ExtraDescriptor` 12, a reference node 16.
    - *Memory per variant node.* Unopened: `16 + 4·S` bytes, `S` its
      published slots; its rows (`12 + 28 + 20·F` for `F` fields) exist
      once per scheme. Opened: `4·(S + k)` more for the new list (the
      old `4·S` are dead until the unit ends), `16` per `Reither` field
      without types, `32 + 4·(n + 1) + 8` per field with `n` types. A
      resolution: nothing (absent, constant), one slot (present with a
      type), or for two `Reither` that stay so one reference node, the
      slots of the types each side gains plus one, and 8 bytes per
      holder moved.
    - *What a changed row allocates* (decisions 18 and 28), in
      `set_more`: for a row that is not fixed, one node at the generic
      level (then lowered to the level of the variable it replaces), one
      descriptor row (12), one `VariantRow` (28), one `RowFieldRow` (20)
      per field gained, and one slot per present type, per `Reither`
      field (its reference slot, holding the chain the source field
      has), for `more` and per argument of the name. Nothing for a fixed
      row. One step a field gained. A gained `Reither` field shares the
      source's chain: the two rows then hold one field, as in OCaml.
    - *The arms of `unify_row` on the explicit stack.* `unify3` opens
      both nodes before the link (the left one is a link afterwards, and
      the descriptor a failure puts back must be the opened one).
      `unify_row` then links nothing by recursion: it flattens, merges,
      decides `more`, `closed` and the name, runs both `set_more`, and
      pushes a `RowEnd` frame (the static row) below one `RowField`
      frame per common tag. Two corrections of decision 28, read from
      the source: the pairs of `merge_rf` are unified in **descending**
      tag order (each pair is consed, ctype.ml:374), and the static-row
      test reads row 1 *again* (`static_row` calls `row_repr`,
      btype.ml:162-170), so it sees the merged row: it is closed exactly
      when either row was. `unify_row_field` runs as frames too: the
      `redo` of two `Reither` (ctype.ml:2663-2675) is a bit in the
      pair's record that `row_field_end` reads after the types were
      unified.
    - *Changes to the skeleton.* `rows.rs`: `unify_row` takes the pair
      and the two opened descriptors; `unify_row_field` takes a frame;
      thirteen new signatures and `copy_refs`; `Extras::{holders, row_scratch, copying,
      passive_variants, rigid_variants}`; `from_segment` fills `link`.
      `unify.rs`, three edits and no other: `FrameKind::{RowField,
      RowFieldEnd, RowEnd}` with their arms in `run_frames` and
      `explain_failure`; `unify3` opens two variant nodes
      (`both_variants`); the variant arm of `extended_children` passes
      the descriptors. `expand.rs`, one edit: the pass of
      `link_memorized` hands a variant node of a copy to `copy_refs`
      while `Extras::copying` is set (never, until R3n). `differential.rs`:
      `REFS`, `Op::GeneralizeStructure`, the variant form reads fields
      through `field_repr`.
    - *Not in R3f.* The split of the types that hold a universal
      variable (PR#6744, ctype.ml:2688-2702) is R3g's. `passive_variants`
      and `rigid_variants` are fields that nothing sets yet (R5b's
      `with_passive_variants`, R3i's `expand_head_rigid`). The GADT
      instance trace of `set_more` (ctype.ml:2607-2608) is R3h's.

Open after the fourth turn, each with the recommended answer.

1. *An instance of a template captured from an opened row.* A template
   made from a segment has unopened rows. A template R5a captures from a
   binder's type may hold an opened generic row: its instance would copy
   the chains as stored, so two fields that share a chain in the scheme
   would share one in the instance (OCaml gives each a `ref None`), and
   a copied reference would name the scheme's holder rows. Recommended:
   R5a keeps one bit per template ("has an opened row", as `OPEN_ROW`
   for cells) and runs the fourth case of `copy_refs` over such an
   instance; no kernel change.
2. *The order of `unify env rm more` for a fixed row whose `more` is not
   a variable.* OCaml runs it inside `set_more`, before the other row's
   `set_more`; the skeleton pushes it as a frame, popped before the
   common tags. They differ only in which of two clashes is reported
   first. Recommended: accept, and let the generated cases of R3n show
   whether the trace differs.
3. *R3f's tests were not run against a prototype.* Recommended: the
   rule of decision 30: a test that contradicts the lines it quotes is
   reported with those lines; R3f's commit 1 and 2 are reviewed against
   the tests before commit 3 is opened.
4. *`Op::GeneralizeStructure` is generated only under `REFS`.* The
   plans of R3a to R3e keep their seeds. Recommended: R3e's generated
   test stays as it is; a later turn may add the operation to the
   object plan, where a shared mutability cell under an annotation is
   the analogous case.
5. *R3g is not designed.* Recommended: a fifth skeleton turn, started
   from `enter_poly` and `unify_univar` and from the PR#6744 split that
   R3f leaves to it.

Decided in the review of the fourth skeleton turn (trunk `411724224f`)
and of the objects slice. They bind the builders and the fifth skeleton
turn.

35. **The cut of variant rows into R3f and R3n stands**, and R3h, R3i and
    R3j depend on R3n: a generated case of any of them copies a row.
36. **An instance of a template captured from an opened row is R5a's.**
    One bit per template ("has an opened row", as `OPEN_ROW` is for
    cells) and the fourth case of `copy_refs` over such an instance.
    Nothing in R3 meets it: a template made from a segment has unopened
    rows.
37. **`unify env rm more` of a fixed row runs as a frame**, popped after
    the other row's `set_more` where OCaml runs it before
    (ctype.ml:2599-2606). The generated cases of R3n judge whether a
    trace differs; a seed that differs is read against those lines before
    anything is pinned.
38. **R3f's hand-built tests were not run against a prototype**, so the
    rule of decision 30 applies to it: the builder ends its turn after
    commit (2) with a test-by-test report, the two commits are read
    against the OCaml lines, and a test that contradicts the lines it
    quotes is reported with those lines.
39. **A tag is one name when the two indices are equal; when they differ
    the two texts are compared once**, as field names are in R3e. Whether
    two indices can spell one name stays open (decision 32). R3f's merge
    does what R3e's does.
40. **`Op::GeneralizeStructure` goes into the object plan in the fifth
    turn**: a mutability cell shared under an annotation is the case
    R3e's generated test does not reach. Done in this turn: decision 48.
41. **unify3 links the expanded head it chose to the ORIGINAL other side
    before the children** (`occur !env t1' t2'; link_type t1' t2`,
    ctype.ml:2330-2331). The old checker unified the two expanded heads
    first and linked afterwards unless the head occurred in the other
    side, which is always so for an abbreviation that expands to its own
    argument (`type id<'a> = 'a`). The difference shows in a diagnostic:
    after two values of type `id<(int, int)>` are unified OCaml reports
    the second as `id<id<(int, int)>>` where the old checker reported
    `id<(int, int)>`, and a plain `(int, int)` unified with an
    `id<(int, int)>` is reported as `id<(int, int)>` where the old
    checker reported `(int, int)`. The four seeds of the object plan that
    showed it (31000122, 31000191, 77000306, and 77000265 with `BUILD`)
    were pinned with this cause, the new side was not changed, and the
    old checker was corrected in a pull request of its own with the
    witness programs as fixtures (decision 20); the pinned lists of
    `object_plan_agrees_on_generated_cases` are empty since. Accepted
    from the same review: `mark_manifests` takes a template's slots at
    the first extended node of a manifest; the restore of a row's two
    rests after a failure writes the saved descriptor at the node's
    *current* level (`rest1.desc <- d1` restores the descriptor only,
    ctype.ml:2513-2517).

On record from the reviews of R3e, R3f, R3n, K3 and K4, for the turns
that follow.

42. **Every trace entry made below a swapped unify3 is reversed, at two
    sites.** OCaml reverses the whole trace of a failure below
    `unify3 env t2 t2' t1 t1'` (`List.map (fun (x, y) -> (y, x)) trace`,
    ctype.ml:2301-2303). The checker reversed only the pairs
    `explain_failure` builds itself; seed 2000082 of the variant plan
    showed it. The two sites, each with a hand-built test that fails
    without it: (a) the error branch of `Checker::unify3` reverses the
    entries pushed since its start when the pair was swapped, because a
    clash that is synchronous in unify3 (`set_more`'s, for one) pops the
    frame that carries the swap before `explain_failure` runs
    (`a_set_more_clash_below_a_swapped_unify3_is_reversed`); (b)
    `explain_failure` reverses the entries already in the trace when the
    parity of the `Linked` frames above `base` is swapped: an escaping
    pair of a failed lowering in a child pair
    (`an_escape_below_a_swapped_unify3_is_reversed`). Cost: one load of
    the trace length per structure pair. **A slice that pushes a trace
    pair of its own, or adds a frame kind below which a trace is made,
    keeps both sites true and shows it with a test in the explaining
    mode.** R3g's is decision 51.
43. **The join of two `Reither` fields compares the two type lists
    pairwise** (`Checker::join_either`, O(|tl1| × |tl2|) comparisons of
    representatives, as `List.memq` in `remq`, ctype.ml:2678-2683), and
    counts no step for it. Whether the order in which a reference is
    settled can show between its resolution and the end of the field's
    unifications is what the generated cases of R3n judge; none of
    30,000 showed it.
44. **K3 kept two of its four items** (TC_KERNEL_R3.md, "K3"). Kept:
    the occurrence probe without marks (`unreached_within_budget`, the
    256 nodes of `walk_budget`, ctype.ml:1424; -18, -18 and -34
    instructions on `unify_ground3`, `unify_datatype2`,
    `unify_abbrev2`), and the test in front of the expansion call
    (`never_expands`: it answers only where the first `expand_once`
    returns "does not expand" without a side effect; the row is read at
    the time of the call). Reverted with their figures: items 3 and 4 (2
    and 0 instructions), and one attempt to take back the test's cost on
    a head that expands. On record from R3e's review, for R5c: a copy in
    a unit that has any descriptor row runs the pass over the copied
    nodes whether or not the copied type holds a field; and
    `sort_unstable_by` in `flatten_fields` rests on a row having no two
    fields of one name.
45. **K4 kept one loop and left three things for R5c**
    (TC_KERNEL_R3.md, "K4"). Kept: `expand_head_unif`, the loop of
    `expand_head` for the unification mode with a clash returned as the
    caller's. Left: (a) the target of 2822.27 instructions for
    `unify_abbrev2` is missed by 65.79 and is not chased; what remains
    is where the optimizer puts a function that every slice makes
    larger. (b) Attempt (c3) (158 fewer instructions on a pair that
    expands, 5 and 9 more on pairs that do not; commit `097f80d041`) is
    the candidate when R5c knows how many structure pairs have a head
    that expands: it pays above about one in eighteen. (c) The pass
    over the nodes a substitution copied (cells and references of rows)
    belongs out of line from `expand_once`, so that a unit without rows
    does not carry its code on the expanding path.
46. **The keep rule for a hot-path figure is a relation between
    operations, not a constant, and the kernel bench is tuned once, at
    R5c**, when the code under `tc/` is complete and a profile of real
    units exists. A figure that moves by 30 instructions each time a
    slice adds code is not a target for that slice. What a slice owes
    instead: it states what a unit that does not use its feature pays
    (as a number of reads), it reports the bench operations before and
    after, and where a figure moved it puts its rare arms out of line
    (`#[inline(never)]` on the functions of its frame kinds, the lesson
    of R3f) and says so. No slice adds a target for a `tc_kernel`
    figure.

Decided in the fifth skeleton turn (trunk `de646dffcb`), each with what
was run. Every test named here is in `differential::tests` and runs today
unless it says "ignored".

47. **The fixed-row rule of `copy_row` is not reachable through R3g, and
    is built by the slice that makes it reachable.** The rule
    (btype.ml:375, 389): a copy of a row whose `row_fixed` flag is set
    gives every `Reither` field `m = fixed` and keeps the flag only when
    `fixed`. The callers and what they pass:

    | Caller | `fixed` | What the rule does there |
    |---|---|---|
    | `Ctype.copy` (ctype.ml:868), which is `instance` and the copy of an expansion | `true` | a field that is not matched becomes matched; the flag stays |
    | `copy_sep` (ctype.ml:1067-1068), which is `instance_poly` | `fixed && is_Tvar (repr more')` | with `~fixed:false` every field becomes unmatched and the row is no longer fixed; with `~fixed:true` as `copy` |
    | `nondep_type_rec` (ctype.ml:4463), `Subst.typexp` (subst.ml:213) | `true` | as `copy`; neither is in R3 |

    Observed on the old checker with a row built by hand
    (`old_checker_matches_the_fields_of_a_fixed_row_it_copies`): the
    copy's fields print `?m` and `?cm` where the source's print `?` and
    `?c`, with references of its own when the row variable is generic and
    the source's when it is not.
    For `copy` the rule changes something only for a fixed row that has
    a `Reither` field with `m` false. Read from the source, such a row is
    made in three places: `make_fixed_univars` sets `m` when it sets the
    flag (typetexp.ml:684-696), so a row whose row variable is bound by a
    polymorphic type has matched fields (observed: `[closed fixed #A?m(int)
    #B?cm() | !a]`); `unify_row` gives a row that gains from a fixed one
    the flag (`row0`, ctype.ml:2590-2596), but then every common
    `Reither` pair is joined with `m1 || m2` (ctype.ml:2659, 2703-2704)
    and a tag only the unfixed row has is a clash or is made absent
    (ctype.ml:2597-2604, 388-397); and `reify` and `rigidify_rec` put a
    fixed empty row under a row that keeps its unmatched fields
    (ctype.ml:1841-1855, 3139-3147). Only the last is a source of such a
    row, and it is R3h's and R3i's. `instance_poly` reaches the rule from
    a program as soon as it exists (a field `'a. ([< #A | #B] as 'a) =>
    int` read from a record), and it is not a function of R3g (decision
    50, "Not in R3g").
    So: nothing is built now. `Checker::copy_refs` asserts in debug builds
    that the row it copies is not a fixed row with an unmatched field
    (`rows::Checker::fixed_with_unmatched`), and
    `no_generated_case_has_a_fixed_row_with_an_unmatched_field` scans the
    old side's form of 4,000 generated cases with variants and universal
    variables for one (546 print a fixed row, none with such a field).
    The slice that first makes such a row (R3h, `reify`) builds the rule
    in `copy_refs` as its first commit: for a row whose last variant
    node's `VariantRow::fixed` is set, each `Reither` field of the copy
    reads matched (a `RES_EITHER` chain node with `RES_MATCHED` in front
    of the field's chain, or that bit set in the chain node the session
    made), with the hand-built row above as its test. The slice that
    builds `instance_poly` owns the other two lines of the table.
    (Seventh turn) The generated cases of the pattern plan make such a
    row and copy it, so the debug assertion is gone: `copy_refs` tracks
    whether the chain it copies is fixed and calls
    `Checker::match_fixed_fields` (built: one pass over the copy's
    fields), which calls `Checker::match_unmatched` for a field that
    reads unmatched (R3h's first commit, as above; a `todo!` that no
    test running today reaches).
48. **`Op::GeneralizeStructure` is in the object plan, and it found
    nothing.** The operation is drawn under `CELLS` as it is under `REFS`
    (one operation in six, and after an `EndDef` the newest operand is
    made an annotation's type and copied twice). The plans with `CELLS`
    draw different sequences than before; no pinned list existed for
    them. `object_plan_agrees_on_generated_cases` passes with the new
    sequences, in both modes and with `BUILD`: 10,000 + 10,000 + 2,000
    cases, no seed differs. The case decision 40 asked for is
    `old_checker_shares_the_cells_of_an_annotation`: the two copies of an
    annotation's open row share its cells (`a^0 x^1` three times), a
    promotion through one copy is seen by the annotation and the other
    copy, and both sides agree; some generated case of the first 300
    sequences draws that pattern.
49. **The harness of R3g: `Plan` bit `UNIVARS`, and what the old checker
    shows.**
    - *The generator.* An object field is polymorphic one time in two:
      `'p. ('p, T)`, `'p 'q. ('p, 'q, T)`, `'q 'p. ('q, 'p, T)`, with `T`
      over the bound variables and the variables in scope, so a binder
      inside a binder names the outer variable and two fields bind the
      same names in the other order. With `VARIANTS` the body is one time
      in four an arrow from a row whose row variable is the first bound
      variable. The body names every bound variable because a variable
      the body does not name is not bound: `'a 'b. 'a => 'a` is `poly(fn(
      !a) => !a; !a)`, and in `'a. {"g": 'a. 'a => 'a}` the outer type
      has no variable (typetexp.ml:563-568; observed). So two binder
      lists of different lengths over bodies that unify do not come from
      a program.
    - *The operations.* `Op::Univar` (a universal variable at the current
      level), `Op::Poly(body, variable)` (a polymorphic type of any
      operand over any universal variable, also one an enclosing type
      binds already) and `Op::Inside` (the body of a polymorphic type as an
      operand, where its variables are outside their binder) are drawn
      one operation in four. `Extras::univar` makes the descriptor row of
      a universal variable and counts it.
    - *The forms* print `poly(body; variables)` with the binder list in
      order and a universal variable as a numbered node, on both sides
      (they did since the second turn). Self-test:
      `the_two_sides_agree_on_universal_variables` (the kernel tier agrees
      on instances, copies, generalizations and hand-made nodes of a
      fixed program, and on 10,000 generated cases:
      `kernel_tier_agrees_on_universal_variables`). The deliberately
      wrong new side is `Fault::SwappedBinders`, an instance whose
      polymorphic types have their first two variables in the other
      order: reported on the fixed case and by 819 of 1,000 generated
      cases (`a_swapped_binder_is_reported`). The old side of the full
      tier is not vacuous (`old_side_of_the_univar_plan_is_not_vacuous`:
      of 1,200 cases 222 have a failed unification, 821 print a universal
      variable, 299 a fixed row).
    - *Observed on the old checker.*

      | Question | Observed | Test |
      |---|---|---|
      | Are universal variables paired by name or by position? | By position: `'a. 'a => 'a` unifies with `'b. 'b => 'b`, `'a 'b. ('a, 'b) => 'a` with `'b 'a. ('b, 'a) => 'b`; `'a 'b. ('a, 'b) => 'a` against `'a 'b. ('a, 'b) => 'b` fails at the result, and the last pair of the trace is the two universal variables | `old_checker_pairs_universal_variables_by_position` |
      | What does `unify_univar` answer for a variable of an outer scope? | The scopes are searched innermost first. A pair neither list of a scope holds goes on to the next scope and pairs there. A variable of the outer scope against one the inner scope binds is refused at the inner scope (one found, one not: `| _ -> raise (Unify [])`, ctype.ml:1557) | `old_checker_searches_the_scopes_innermost_first` |
      | When does a universal variable escape, and what is the trace? | When an inner type binds again a variable an open scope has paired, and the other inner type names a variable of that family outside a binder of the family (ctype.ml:1612-1653). The trace is the pairs down to the two inner polymorphic types and nothing below them (`raise (Unify [])`, ctype.ml:1669), and the failure leaves the graph as it was | `old_checker_tests_escape_before_the_bodies` |
      | Is the escape test before or after the bodies? | Before the scopes are pushed and before the bodies (ctype.ml:1664-1674): with a left body that cannot unify with the right one the trace is still the escape's. See below | same |
      | What do an instance and a copy of a polymorphic type share? | Nothing generic: each has bound variables of its own, named by its body; a row whose row variable is bound ends in the copy of that variable. `generalize_structure` makes a universal variable generic. A type that is not generic is shared whole | `old_checker_copies_the_bound_variables_with_their_type` |
      | What does a failed unification of two polymorphic types leave? | The levels unify2 lowered and every pair of universal variables unified before the clash, linked. The same unification the other way round then succeeds: the two binder lists are one pair of nodes, and `!a` meets `!b` free in their scope | `old_checker_keeps_the_links_of_a_failed_polymorphic_unification` |
      | What happens to a universal variable outside its binder? | A variable against it, or against a type that holds it free, is refused by `occur_univar` with the pair of the universal variable and a new variable after the pair of the unification (ctype.ml:1586); two universal variables with no scope open are refused with one pair (ctype.ml:1559); a variable against the whole polymorphic type is bound | `old_checker_refuses_a_free_universal_variable` |

    - *The order question.* The skeleton's doc comment of `enter_poly`
      said "check afterwards". OCaml tests escape first
      (ctype.ml:1664-1669), then pushes the two directions of the scope,
      then runs the bodies. The two orders give the same answer
      (success or failure) on every case, by this argument: the escape
      walk reads the other polymorphic type for a universal variable of
      the family outside a binder of the family; unifying the bodies can
      only bind variables of that type, and a variable is never bound to
      a type that holds a universal variable outside its binder
      (`occur_univar` in `unify1_var` and in unify3, ctype.ml:2219, 2318,
      2322); so the walk finds the same after the bodies as before. They
      differ in what is left and in the trace: tested first, a failure
      leaves the graph as it was and the trace ends at the two
      polymorphic types; tested afterwards, the links and levels of the
      bodies stay (the row above) and, when the bodies clash too, the
      trace is the bodies'. The witness is the second case of
      `old_checker_tests_escape_before_the_bodies`: left `poly(poly((u,
      fn('x) => 'x); u); u)`, right `poly(poly((w', u'); w'); u')`; the
      trace is `outer ~ outer'`, `inner ~ inner'`, where a test after the
      bodies would add the pair of the arrow and `u'`. The design tests
      first (decision 50).
    - *A difference of the old checker, reported and not fixed.* The pair
      `occur_univar` raises is `(ty, newgenvar ())` (ctype.ml:1586): the
      new variable is generic. The old checker makes it at the current
      level (`ctx.new_var(None)` in `occur_univar`, types/ctype.rs), so
      its trace prints `[0]` where OCaml's would print `[G]`. Smallest
      case: a variable unified with a universal variable outside its
      binder (`old_checker_refuses_a_free_universal_variable`). The
      printed diagnostic is the same either way (a new variable with no
      name); the new side follows OCaml, and the generated cases of the
      explaining mode with `UNIVARS` are not part of R3g's acceptance
      until the old checker is corrected (decision 50, "Acceptance").
    - *A second difference of the old checker, reported and not fixed.*
      `Tpoly (t, [])` against a type that is not polymorphic is a clash
      in OCaml (`_, _ -> raise (Unify [])`, ctype.ml:2425). The old
      checker unifies the body with the other type ("Tpoly with empty
      vars: unwrap and retry", types/ctype.rs, the two arms after the
      package arm of its unify3). Smallest case: `newty (Tpoly (t, []))`
      unified with `t`, for `t` an arrow: OCaml refuses, the old checker
      accepts. The typer makes `Tpoly (t, [])` only where the other side
      is one too (a method or a field), which is why no program shows
      it. Found by the prototype of R3g on a generated case (seed
      1000058 of the plan as it then was); the generator no longer makes
      the pair: `Op::Poly` gives the body itself when its second operand
      is not a universal variable, and `Op::Inside` steps through a
      polymorphic type without variables. The new side follows OCaml.

50. **R3g as designed.** The design is section 8.8; this entry is what
    was decided.
    - *Storage.* A universal variable is one node with a descriptor row
      `ExtraDescriptor::Univar(name)`; a polymorphic type is one node
      whose slots are the body and then the bound variables. No new
      node kind and no new pool. The pairs of `univar_pairs` are a
      stack of 20-byte `PolyScope` records in `Checker::scopes`, and the
      partner references (`ref None` per bound variable) are graph
      nodes, so that `set_univar` is a logged `Graph::write` and a
      restore undoes a pairing with no log of its own.
    - *Order.* `enter_poly` tests escape before it pushes the scope, as
      OCaml does (decision 49).
    - *Who leaves a scope.* A `LeavePoly` frame below the bodies' pair on
      success; `unify_distinct`'s error path on failure (decision 51).
    - *What a unit without universal variables pays.* Nothing in
      `unify_pair` (one `and` of two heads already in registers and a
      branch not taken); one load of `Extras::univars` per binding of a
      variable to a type with children, per variable arm of unify3 and
      per joined `Reither` pair; one load of `scopes.len()` on a failed
      unification.
    - *Nested scopes are quadratic, as in OCaml* (`known_univars` is
      rebuilt at every entry, ctype.ml:1658-1662). The step test states
      it: at most 110 times the steps for ten times the depth.
    - *Not in R3g.* `instance_poly` (ctype.ml:1081-1095) and with it the
      lines of `copy_row` that only `instance_poly ~fixed` reaches
      (decision 47): they need an owner (8.8, open question 1).
      Packages: R3p (decision 52). Pattern mode: R3h.
    - *Acceptance.* The twelve tests ignored for "R3g build". The
      generated cases run in `Mode::Success` only; the fixed cases run
      the explaining mode too, except those whose trace has the pair
      `occur_univar` raises (decision 49).

51. **`LeavePoly` carries no pair and no swap, and a failure cuts the
    scopes back in one place.** OCaml's `enter_poly` restores
    `univar_pairs` in a handler and re-raises (ctype.ml:1677-1679), and
    unify3's handler reverses the whole trace of a swapped call
    (ctype.ml:2299-2303; decision 42). In the kernel:
    - A `LeavePoly` frame holds the number of scopes to cut back to in
      its `extra`, and `NONE` for both types. Popped, it truncates
      `Checker::scopes`. It adds nothing to a trace.
    - On a failure, `unify_distinct` calls `leave_scopes(base)` when
      `scopes` is not empty: it finds the lowest `LeavePoly` frame above
      `base` in `frames` and truncates `scopes` to its `extra`. One
      place, both modes; the partner nodes written since are undone by
      the caller's restore, as every other write.
    - The entries of a clash in the bodies below a swapped unify3 are
      reversed by the `Linked` frame of the two polymorphic types, which
      is below the `LeavePoly` frame: the `LeavePoly` frame needs no
      swap bit. Witness: `a_clash_in_the_bodies_below_a_swapped_unify3_
      is_reversed`.
    - The pair of `occur_univar` is pushed by the callee and reversed at
      its three call sites when unify3 ran swapped (`free_of_univars(ty,
      swapped)`): the two variable arms of unify3 and, through
      `bind_routed`, never swapped. Witness: `a_free_universal_variable_
      below_a_swapped_unify3_is_reversed`.

52. **Packages are their own slice, R3p, behind one trait.** The kernel
    has the two name lists and the arguments of a package; it does not
    have module types. `complete_type_list` needs `Env.lookup_type` in a
    module type and `nondep_instance`, and the last test needs
    `package_subtype`, which is `Includemod` (ctype.ml:2135-2181).
    - *The seam* is `rows::PackageDecls`, held in `Checker::packages`:
      `compare` (the order of two names, `Longident.cmp`), `complete`
      (the answer of one module type for one name, as `Completion`: a
      type, abstract, missing, other) and `compatible` (the last test
      for two different paths). R5a supplies it over its module types
      and installs it before the first unification of a unit; with none
      installed any two packages are a clash: without `compare` the
      kernel cannot put two name lists in one order.
    - *A name is a position* in the pool that `PackageRow::longidents`
      ranges over. The kernel passes positions and never reads the pool.
    - *The levels* `lv1` and `lv2` are both the lower of the two nodes'
      levels. OCaml passes `t1.level` and `t2.level` after `unify2`
      lowered both sides to the lower of the two expansions' levels
      (ctype.ml:2283-2285); the two readings differ only when one side
      is an abbreviation that sits above its memorized expansion, which
      `expand_head` does not produce (the expansion is made at the
      abbreviation's level, and a lowering of one reaches the other).
      Stated as an assumption; R5a's tests on real module types are
      where a difference would show.
    - *No differential judge.* The differential program has no module
      types and the old checker's `unify_package` is not reached by it.
      R3p is accepted on three hand-built tests with a supplier written
      in the test file, each quoting the OCaml lines it follows. R5a
      owns the comparison with the old checker on real packages.
    - `allow_absent` (subtyping) is R3j's: `Completion::Abstract` and
      `Completion::Missing` are separate answers so that R3j can skip
      them without a second trait.

On record from the reviews of the fifth skeleton turn, of R3g and of R3p
(trunk `61f7f41292`). They bind the sixth skeleton turn and R5c.

53. **`split_univars` puts the join off and runs it again.** OCaml
    unifies the gained types that hold a universal variable and then
    builds the two fields from the lists as they were before those
    unifications (`List.iter (unify env tu1) (tlu1 @ tlu2)`, then `tl1'`
    and `tl2'` as already computed, ctype.ml:2693-2706). The kernel
    returns `Ok(None)`, lets the frame stack unify the holders, and runs
    `join_either` from its start: the two type lists are read again and
    compared again. The field holds the same SET of nodes either way. The
    two differ in one corner: a gained type WITHOUT a universal variable
    that those unifications make the same node as a type the gaining side
    already has is not gained by the second run, and is kept, as a
    duplicate entry of the list, by OCaml. Accepted as built. It is
    reopened by a case in which a printed type or a later join shows the
    duplicate; the sixth turn built the corner by hand on the old side
    (decision 58).
54. **`join_either` lowers the two gained ranges each on its own.** With
    `passive_variants` set and holders on both sides, `split_univars`
    returns two ranges with a gap between them (what its compaction left
    behind: holders, which OCaml does not lower, ctype.ml:2699-2703). The
    caller lowered everything from the start of the first range to the end
    of the second; corrected in the review of R3g. Nothing in `tc` sets
    `passive_variants`, so no test reached the correction until the sixth
    turn wrote one by setting the field (decision 59).
55. **`package_end` reads the right node's descriptor without following
    a link.** For the right node to be linked away between the two frames
    it would have to be nested in an argument of one of the two packages,
    and every such shape ends in an occurrence clash before the
    `PackageEnd` frame is popped. Whether pattern mode changes that is
    answered by the design of R3h (decision 63: it does not, and why).
56. **A mark of `free_univar` is live while its context is open, and a
    polymorphic type WITHOUT bound variables opens a context.** A node
    first visited inside such a type is visited again after the type is
    left, where OCaml's `visited` map, which compares the sets of bound
    variables, does not visit it again (`bound' ⊆ bound` holds for two
    equal sets, ctype.ml:1572-1581). The answer is the same; the visits
    are more. The count is stated and asserted by the sixth turn's step
    tests (decision 59).
57. **The bench record of R3g, for R5c.** The five unification operations
    of `tc_kernel` at the builder's start and at the merged head:
    `unify_vars` 118 and 122, `unify_ground1` 120 and 120, `unify_ground3`
    807 and 807, `unify_datatype2` 815 and 815, `unify_abbrev2` 2885.06
    and 2886.06. Tried and reverted, each measured: `#[inline(never)]` on
    the five bodies (no figure moved) and `#[cold]` on the seven rare
    functions (every operation dearer than the merged head). What moved
    the figures between the two heads was a merge of trunk that changed
    none of these bodies: code placement under one codegen unit. For
    R3p, `#[cold] #[inline(never)]` on its two bodies put all five
    figures back at their base, and is kept. Consequence, binding every
    later prompt: no slice has a target for a `tc_kernel` figure
    (decision 46), and **no prompt prescribes a remedy for a figure that
    moves**; a build prompt asks for the five operations before and
    after, as a report.

Decided in the sixth skeleton turn (trunk `61f7f41292`), each with what
was run. Decisions 58 to 60 are corrections and tests of BUILT code that
the reviews above left owed; every test named runs today.

58. **`split_univars` keeps what OCaml keeps: decision 53 is reopened
    and closed.** The corner was built by hand on the old checker
    (`differential::tests::old_checker_gains_a_type_the_holders_made_a_
    duplicate`): `poly([< #A((u, x)) & x]; u)` against `poly([< #A((u',
    x')) & x']; u')`. The two tuples hold a universal variable and are
    unified, which makes `x'` and `x` one node; each field then holds
    THREE types, the last two one node (`#A?^0((!, ') @4 @4)`). The OCaml
    compiler was run on a source program that reaches the corner:

    ```rescript
    let f = (
      o: {"m": 'u. [< #A(('u, 'a)) & ('a)] => unit},
      p: {"m": 'u. [< #A(('u, 'b)) & ('b)] => unit},
    ) => (if true { o } else { p }, o, p)
    ```

    With a counter added to `unify_row_field` (a local build, not
    committed) the join runs once with two types a side, the split keeps
    one and holds one a side, and after `set_row_field` both fields read
    three types. So OCaml has the duplicate; the kernel, which compared
    the two lists again after the holders were unified, had two types.
    Can it show? A printed type lists every type of a `Reither` field
    (`tree_of_row_field`, printtyp.ml:730-737), and a later join reads
    the length of the list: the arm of PR#7496 needs `List.length tl1 =
    List.length tl2` (ctype.ml:2652-2655) and `rigid_variants` reads
    `List.length tl1 = 1` (ctype.ml:2667-2668), so a field of three
    types and a field of two can take different arms against the same
    third field. That is enough to correct it. (The diagnostic of the
    program above, with `let g: int = f` appended, prints two types for
    the tag in OCaml although the copies it is made from hold three; what
    drops the third between the copy and the printed text was not
    established, and is not needed for the decision.)
    The correction, in `rows.rs`: the arm of `split_univars` with holders
    on both sides writes the types each side KEEPS after the pair's
    record in `saved` (one entry with the two counts, one entry a type;
    16 bytes each, only in this arm), and the second run of
    `join_either` reads them back instead of comparing the two lists
    again. Test: `r3_tests::a_field_gains_what_it_lacked_before_the_
    holders_were_unified` (both modes; three types, the last two one
    node; it fails without the edit, observed: two types).
59. **`free_univar` opens no context for a polymorphic type without
    bound variables; the step tests of the two walks; the passive
    split.**
    - *A fault of built code, found by the step test decision 56 asked
      for.* Every object field is a `Tpoly (t, [])`. With a context per
      such type, a node first met below one was visited again after it
      was left, and the second visit met the types below it in closed
      contexts again: on `t(i + 1) = (poly(t(i);), t(i))` the walk took
      `2^(n + 1) - 1` visits (observed without the edit: 2,047, 4,095
      and 2,097,151 for n = 10, 11, 20). OCaml visits each node once:
      such a type adds nothing to `bound` (ctype.ml:1587-1589), and a
      node visited with a `bound` is not visited again with the same one
      (ctype.ml:1569-1581). A type of that shape is what a value used
      twice gives (`(x, {"m": x})`), and the walk runs at every binding
      of a variable to a type with children once the unit has ANY
      universal variable. Corrected: the `Poly` arm of
      `push_free_univar_children` pushes the body of a type of arity 1
      in the current context. The extra visits are now ZERO, stated and
      asserted: exactly `2n + 1` visits at n = 1,000 and n = 10,000
      (`r3_tests::the_walks_for_universal_variables_at_ten_thousand`,
      which also has the linear relations of `free_univar` over a wide
      type and of `univars_escape` with a known binder).
    - *Left as it is, and why.* A polymorphic type WITH bound variables
      still opens a context, and a node shared between the inside of two
      sibling types with binders, or between the inside and the outside
      of one, is visited once per context it is met in. OCaml visits
      such a node again too, once per strictly smaller `bound`
      (`Type_set.inter bound bound'`, ctype.ml:1574-1576: "that's way
      too expensive", ctype.ml:1562). On a chain of n nested types WITH
      binders that share their bodies with the outside the kernel's
      visits double per type where OCaml's grow with the number of
      distinct `bound` sets. No program has shown it: a polymorphic
      method whose type shares a node with a type outside it needs a
      value that is not generalized inside an annotated method type.
      Open question 3 of this turn.
    - *A row walked by `free_univar`*: `r3_tests::a_free_universal_
      variable_is_found_in_a_row_in_order` (fields, then the name's
      arguments, then the row variable; an opened `Reither` field through
      its chain; nothing below a reference resolved to absent).
    - *The passive split*: `r3_tests::passive_variants_keep_the_levels_
      of_the_types_that_hold_a_universal_variable` sets
      `Extras::passive_variants` by hand, with holders on both sides and
      the holder AFTER the kept type in each list: the holders stay two
      nodes at their level, the kept types are lowered to the merged row
      variable's level. With the caller's loop as it was before decision
      54 the test fails (observed: a holder at level 1).
60. **The arguments of a row's name are children only of the innermost
    row, in every walk.** OCaml's `iter_row` visits them only when
    `row_more` is not itself a variant (btype.ml:229-241), every walk of
    a type goes through `iter_type_expr` (btype.ml:263-265), and a copy
    takes the name of the innermost row (`row_repr`, btype.ml:126-135).
    The kernel's walks push every slot of a node. Before this turn:

    | Walk | Kernel | Visited them for a row whose `more` is a variant | OCaml |
    |---|---|---|---|
    | lowering | `Graph::lower`, `Checker::lower_scoped` | yes | no: `update_level`, ctype.ml:625-626 |
    | generalization | `Graph::generalize`, `generalize_structure` | yes | no: ctype.ml:509-516, 524-540 |
    | occurrence of a structure pair, of a binding | `Checker::reaches`, `occur_expanding`, the scan of `binding_scan` | not entered: a row stops the walk | not entered: `occur_rec`, ctype.ml:1403 |
    | deep occurrence | `Checker::reaches` with `deep`, the routed `binding_scan` | yes | no: `deep_occur`, ctype.ml:1735-1782 |
    | the lowering part of a binding | `binding_scan`, `LEVEL_ONLY` entries below a row | yes | no: `update_level` |
    | free universal variable | `Checker::free_univar` | yes | no: `occur_univar`, ctype.ml:1601 |
    | escape of a universal variable | `Checker::univars_escape` | yes | no: ctype.ml:1648 |
    | closedness of an expansion | `Checker::closed_over` | yes | no: `closed_parameterized_type`, ctype.ml:441-451 |
    | copy, instance | `Graph::copy`, `Graph::instance` | copied as slots of the copy | not copied: `copy_row` of `row_repr`, ctype.ml:800-868 |

    Observed on the old checker with `[> #B]` unified with `[> #A] as
    p<y>`, `y` in no field (`differential::tests::old_checker_does_not_
    reach_the_arguments_of_a_stale_row_name`): a lowering, a
    generalization, `deep_occur`, a copy and a binding all leave `y`
    alone. What can show it: the level of a type that is the argument of
    a phantom parameter of a named open row, after the row gained a tag.
    Corrected on the write side, so that no walk pays a descriptor load
    per variant node: when `unify_row` has run both `set_more`, each row
    that is not fixed has a variant node as its `more` (ctype.ml:2619),
    and when such a row has a name with arguments its home node is
    written with a new list in which the slots of those arguments hold
    what the `more` slot holds (`Checker::drop_name_children`; in the
    explaining mode a `Fields` frame puts the descriptor back on a
    failure, as it puts back the rest whose link made the name stale).
    Nothing reads the name of a row that is not the innermost. Cost: two
    compares per unified pair of rows; for a named row with arguments
    that gains a tail, one list of the node's slots. Test:
    `r3_tests::the_arguments_of_a_stale_row_name_are_not_children`, one
    block per walk of the table, in both modes (without the edit the
    lowering already reaches `y`, observed). Two other places link a row
    variable to a variant node, and each calls `drop_name_children` for
    the row when it is built: `reify` (ctype.ml:1848-1852, R3h; 8.9) and
    `rigidify_rec` (ctype.ml:3139-3147, R3i).
    *In pattern mode* (rewritten in the seventh turn; the review of pull
    request 347 did not accept this decision there). What changed: the
    decision said that row 1's home is known only when `last1` is a
    node, "because unify3 has linked the left node". Pattern mode links
    no structure node (decision 64), so there the left node is still
    the variant node it was and it is the home of row 1: `unify_row`
    takes the two heads as its first argument and uses the left one as
    row 1's home when `last1` is none and that node is not a link (one
    load of a head, made only for a row 1 that has a name with
    arguments and is not fixed). Its name's arguments stop being
    children exactly as in expression mode, for the same reason: its
    `more` is linked to a variant node by `set_more`. Test:
    `r3_tests::a_named_row_on_the_left_loses_its_arguments_in_pattern_mode`
    (R3r: a pattern unification of two rows is the `Try` arm): in
    pattern mode the left node is not a link, reads `A B`, and a
    lowering leaves `y`; in expression mode the same pair leaves the
    left node a link. Seen to fail without the home: `y` is lowered.
    The cost paragraph of `unify_row` names the two compares (`fixed`
    and "has a name with arguments", on the `VariantRow` already
    loaded, per row that is not fixed) and the one head load.
    The name of a row whose path would escape is decision 75.

61. **The harness of pattern mode: the plan bit `PATTERN`.**
    `differential::PATTERN` (bit 9 of a plan) makes a case a case of
    pattern mode. What the bit adds:
    - *the program*: `type n0`, `type n1`, `type k<'a>` and
      `type d<'a> = D('a)`, and after the generated values four values
      whose parameters are the pairs R3h is about
      (`differential::PATTERN_VALUES`): a locally abstract type against a
      structure and against the other one; constructors of one path with
      arguments, abstract (`k`) and a data type (`d`), over a locally
      abstract type, over `int` and over a variable; arrows over them.
      With `VARIANTS` two more (`PATTERN_ROWS`): rows that clash and are
      not compatible (a tag the other closed row lacks, a constant tag
      against one with an argument) and rows that unify under an
      equation; a row that clashes and is compatible comes from `reify`
      (a fixed row against an open row with one more tag). There is one
      data type, so two different data types are never compared and the
      supplier of declarations answers `Clash` (8.9);
    - *both sides*: `n0` and `n1` are locally abstract types of two
      newtype levels, the level the case starts at and one above it. The
      old side binds them again as local identifiers whose declarations
      have `type_newtype_level`; the new side sets `NEWTYPE` and a
      `Newtype` row on their `TypeTable` rows. The old side sees the unit
      from outside, as `Case`: its types are paths through a module and
      only the predefined types are bare identifiers
      (`in_current_module`). The new side says the same with the `LOCAL`
      flag, set on the predefined types only;
    - *the operation* `Op::Gadt(left, right, flags)`: one top-level
      unification in pattern mode with the current level as the newtype
      level; bit 0 of `flags` is `generate_equations`, bit 1
      `assume_injective`. `unify_gadt` itself is 3; 1, 0 and 2 are the
      modes unify3 installs below it (ctype.ml:2352, 2368) and that no
      top-level call of OCaml asks for: `Checker::unify_pattern` takes
      the two flags so that a case reaches each. Half of the pattern
      unifications of a generated case are over two parameters of a new
      instance of a pattern value, the rest over any two operands;
    - *the form*: both sides end it with the equations in force, one
      line a type that has one, sorted by the type's name: `= name :=
      body`, the bodies numbered together. The old side prints the
      manifests of the local constraints of the environment the last
      successful pattern unification left; the new side instantiates the
      manifest of every entry of `Checker::equations` at the generic
      level. A type `reify` made prints by its name (`$0`, `$1`), which
      the new side takes from the supplier of the harness
      (`differential::FreshNames`, the rule of `get_new_abstract_name`,
      ctype.ml:908-922).
    - *the deliberately wrong side* `Fault::ExpressionMode`: a pattern
      unification runs as `Checker::unify`.

    Running today: `the_two_sides_agree_on_pattern_programs_without_a_
    pattern_unification` (the self-test: the fixed program and 300
    generated cases with the pattern unifications taken out agree),
    `old_side_of_the_pattern_plan_is_not_vacuous` (observed, 1,200
    cases: 950 pattern unifications that succeed and 493 that fail
    among the judged operations; 130 cases end with an equation, 3 with
    two, 183 with a reified type) and
    `generated_cases_find_a_pattern_unification_in_expression_mode` (the
    wrong side needs nothing of R3h: of 228 cases with a pattern
    unification it is reported in 21 that have an equation on the old
    side and in 58 where only it fails).

62. **What the old checker does in pattern mode, and where it is a
    judge.** Observed on `differential::tests::PATTERN_PROGRAM`; each
    item names its test in tc/differential.rs.
    - *Which pairs get an equation, and its direction* (a judge):
      `old_checker_gives_the_equation_to_the_newer_locally_abstract_type`.
      A locally abstract type against a type that is not one gets the
      equation on either side (ctype.ml:2385-2392) and the two nodes
      stay two nodes. Of two locally abstract types the one of the
      higher newtype level gets it (ctype.ml:2373-2384). Without
      `generate_equations`: none, and a success (`reify`, no `mcomp`).
      `int` against a tuple with equations: a clash (`mcomp`). After
      `n0 := int`, `n1` against `n0` gives `n1 := int`: the body is the
      expanded head.
    - *The arguments of one path* (a judge):
      `old_checker_refines_the_arguments_of_a_constructor_by_its_
      injectivity`. With `assume_injective` the arguments are unified
      with equations; below that an abstract type that is not of the
      unit gets none and what does not unify is reified, and a data type
      gets them. A later expression unification of two `k` nodes that
      pattern mode assumed equal fails: nothing of the assumption is
      left after the top-level call.
    - *What `reify` makes* (a judge, also of the names of variables
      without one): `old_checker_reifies_a_variable_and_a_row_variable`.
      A variable at the newtype level is a link to a new abstract type
      `$0` at the variable's level; a row variable is a link to a fixed
      row without tags over `$0`; the second is `$1`. A variable with a
      name (`$'a`) is not reachable from an operation: tested by hand.
    - *What a failure leaves* (a judge of the graph):
      `old_checker_keeps_what_reify_linked_when_a_pattern_unification_
      fails`. `reify` links before it refuses a variable below the
      newtype level, and the row a clash reified stays fixed when
      `mcomp` refuses the pair: unify3's handler puts back only the left
      node's description (ctype.ml:2437-2439). A failure after an
      equation was added leaves the graph as it was. The caller that
      goes on restores a snapshot, the levels and the environment it
      kept (`set_state`, compiler/ml/typecore.ml:1299-1305); the kernel's
      caller restores a mark and cuts the equations
      (`Checker::cut_equations`, 8.9). The harness drops the old side's
      environment of a failed pattern unification, so it does not judge
      the equations a failed one added.
    - *Rows* (a judge):
      `old_checker_accepts_rows_that_clash_and_are_compatible`.
    - *Two structures unified in pattern mode are ONE node on the old
      side* (NOT a judge):
      `old_checker_links_the_structures_a_pattern_unification_unifies`.
      OCaml records the pair as assumed equal and links neither
      (`Pattern -> add_type_equality t1' t2'`, ctype.ml:2327-2331). The
      old checker links them: two tuples of two instances are one node
      afterwards, and of `[#A(n0) | #B]` against `[#A(int) | #B]` the
      left row prints `int`: a type equal only under the equations of
      one case has become the other for good. Three source programs
      were tried (a constructor whose result names a tuple, the same
      through a tuple pattern, the same through an abbreviation) and
      both compilers accept all three: no source program is known that
      shows it. `differential::old_judges` gives the number of
      operations of a case before the first pattern unification that
      succeeds and leaves a structure reachable from an operand a link;
      `compare` runs both sides on that prefix under `PATTERN` (observed:
      64 of 1,200 cases are cut). So the generated cases judge failures
      of structure pairs in pattern mode and never their success; the
      hand-built tests of 8.9 do, from the OCaml lines.
    - *Ambiguity is not checked on the old side* (NOT a judge, and not
      in R3h): OCaml refuses
      `type rec t<_> = Int: t<int>` /
      `let f = (type a, x: t<a>, y: a) => switch x { | Int => if true { y } else { 0 } }`
      with "This instance of int is ambiguous: it would escape the scope
      of its equation" (`trace_gadt_instances`, `Env.gadt_instance_level`,
      `add_gadt_instance_chain`, ctype.ml:176-201, 1220-1227, 2289-2298;
      the report is typecore's). The Rust compiler accepts it (observed
      with `compile_source_in_process`): the old checker has the tracing
      flag and no instance levels. The kernel has neither after R3h; it
      is a slice of its own after R3h (open question 1 of this turn).
    - Not observed to differ, and not judged: the arm of `unify` for two
      locally abstract types under local constraints, which expands the
      newer one once (ctype.ml:2258-2270), is missing on the old side;
      it expands both heads, and the equations that result were the
      same on every case tried.

63 to 71. **The design of R3h** is section 8.9, where each is written
    with its reasons: 63 `package_end` in pattern mode; 64 what replaces
    the link, per arm of unify3; 65 the arm of `unify` for two locally
    abstract types; 66 the declaration facts; 67 an equation, its
    storage and its cut; 68 the two arms that try, as frames; 69 `occur`
    in pattern mode; 70 `mcomp` and the answer without a supplier; 71
    what a unit that never types a pattern pays.

**Decided in the seventh skeleton turn.**

*The review of pull request 347, as decided.* Accepted as written:
decisions 53 to 59, 60 in expression mode, 61, 62, 63, 65, 66, 68, 70,
and the cut into R3h then R3r. Not accepted, and rewritten in place in
this turn, each saying what changed: decision 67 step 1 (what
`non_recursive_abbrev` refuses), "as in expression mode" of decisions
64 and 69 for the two variable arms, decision 60 in pattern mode,
decision 71 (what it left out). Decisions 63, 68 and 70 were accepted
and their mechanics changed where the prototype or a correction of the
review needed it (the package fallback has a body, `Try` has two
phases, `mcomp` runs on `frames`); 8.9 says so at each. The five open
questions of the sixth turn are decisions 72 to 76.

72. **The ambiguity of GADT instances is its own slice, R3s, after
    R3r** (question 1). The design is 8.11. Since the sixth turn the
    old checker has the instance sets (pull requests 350 and 352:
    `gadt_instance_level`, `add_gadt_instance_chain` and
    `wrap_trace_gadt_instances` in types/ctype.rs and types/context.rs),
    so the last bullet of decision 62 ("the Rust compiler accepts it")
    no longer holds for the program it names: the old checker is a
    judge of ambiguity where it traces. R3s also owns one thing that is
    not ambiguity: the memo of a nullary constructor while tracing
    (decision 79).
73. **`old_judges` stays** (question 2). The old checker links two
    structures in pattern mode and no source program shows it; the
    hand-built tests judge a structure pair that succeeds in pattern
    mode (`two_structures_are_assumed_equal_and_not_linked`,
    `pattern_mode_at_ten_thousand`).
74. **`free_univar` visits a node again for each context of a
    polymorphic type WITH bound variables, as OCaml does** (question 3;
    decision 59). Accepted; nothing changes.
75. **A row loses a name that is below its scope when it is lowered**
    (question 4; built in this turn, a correction of built code).
    OCaml, compiler/ml/ctype.ml:615-621 (the sixth turn cited 618-623):

    ```text
    | Tvariant row ->
      let row = row_repr row in
      (match row.row_name with
      | Some (p, _tl) when level < get_level env p ->
        log_type ty;
        ty.desc <- Tvariant {row with row_name = None}
      | _ -> ());
    ```

    `Checker::lower_scoped` has the arm: a variant node above the level
    goes to `Checker::lower_row_name`, which reads the name of the last
    row of the node's chain (`row_repr`, btype.ml:126-135) and compares
    the scope of the name's type with the level; when the name
    escapes, `Checker::unname_row` writes the VISITED node (logged) as
    one row of every field of its chain with no name. Only that node:
    `ty.desc <-` writes one node, and another node whose chain ends in
    the same row still reads the name. The walk then goes on over the
    slots of the new descriptor, which has no name arguments, so they
    are not lowered through it (`iter_row` reads the new descriptor).
    Cost, checked against the code: a node above the level that is not
    a constructor costs one test of the extended bit of the head it has
    loaded; an extended node (an object, a field, a polymorphic type, a
    variant, a package) one descriptor load; a variant one `VariantRow`
    load and one node load a chain node, and, when its row has a name,
    one `TypeInfo` load and one compare. Nothing is written and no step
    counted unless the name escapes; then one node, one descriptor row,
    one `VariantRow` and one `RowFieldRow` a field. A unit without a
    scoped type does not reach `lower_scoped` at all (`types.scoped ==
    0`). Test:
    `r3_tests::lowering_a_row_below_the_scope_of_its_name_drops_the_name`
    (four blocks: the name dropped and `y` left at its level; a scope
    not above the level changes nothing; of two nodes over one row
    variable only the lowered one loses the name; a restore puts the
    name back). Seen to fail without the arm (the row still reads its
    name). Generated cases: no plan makes a row whose name is a type
    with a scope (the late types of `SCOPED` and the locally abstract
    types of `PATTERN` are abstract, never the name of a row), so the
    generated cases of the plans with variant rows and scopes were run
    and agree as before (`scoped_plan_agrees_on_generated_cases`, the
    pattern plan), and the hand-built test is the judge.
76. **The builder of R3h reports what `generalize` writes under a
    speculation** (question 5): `duplicate` is `generalize` and `copy`
    under one, and that holds only if `generalize` writes nothing but
    levels through the trail. Observed on the prototype: after
    `duplicate` every level of the destination is what it was and the
    speculation depth is 0
    (`an_equation_over_ten_thousand_shared_nodes_is_linear`). The
    prompt of R3h says: report what it writes, and stop if it is more
    than levels through the trail. Two things the prototype met there:
    a copy under `duplicate`'s speculation that opens a row must not
    log the write (`Checker::open_fresh`: the restore would close the
    copy again), and a free universal variable of the destination is
    COPIED by `Checker::copy` where OCaml's `Subst.type_expr` keeps a
    variable and a universal variable shared (compiler/ml/subst.ml:
    132-143). A destination has no variable after `reify`; a free
    universal variable in a destination is a recorded difference with
    no known program.
77. **The body of an equation keeps the `Tnil` of its destination on
    the old side.** `duplicate_type` is `Subst.type_expr Subst.identity`
    (ctype.ml:2095), which copies every node that is not a variable or
    a universal variable, `Tnil` included (compiler/ml/subst.ml:132-158:
    `Tvar _ | Tunivar _` are kept, `| _ ->` makes a stub and copies).
    The old checker keeps a `Tnil` as the node it is
    (`subst_identity_copy_rec`, types/ctype.rs: `TypeDesc::Tvar(..) |
    TypeDesc::Tunivar(..) | TypeDesc::Tnil => ty`). Smallest case: an
    equation whose destination is a closed object or a closed row
    (`n1 := {"x": int}`): the body's `nil` is the destination's, at its
    level, where OCaml's is a new generic node. Nothing reads the level
    or the identity of a `nil` in OCaml's unification; no source
    program is known to show it. The harness prints a `nil` of a body
    without number and level on both sides (`OldSeen::bare_nil`); one
    explained seed where an instance of such a body shares the `nil`
    with the destination is listed
    (`EXPLAINED_OLD_DIFFERS`, 11,000,046).
78. **In the explaining mode the old checker does not keep what the
    second pass of a failed lowering expanded.** Seed 8,000,098 of the
    explained pattern plan: `fn(..)` against an object whose field is
    `po<int>` (a recursive abbreviation with an argument) and which
    names `n1` above its scope. The first pass clashes at `n1`; the
    second expands every constructor with arguments in place
    (`| Tconstr (_, _ :: _, _) when expand -> (try link_type ty
    (!forward_try_expand_once env ty)`, ctype.ml:602-604), reaches
    `po<int>` before `n1` (`iter_type_expr` takes a field's type before
    the rest of the row) and clashes; nothing restores (decision 14),
    so `po<int>` is its expansion afterwards. The new side has that;
    the old side prints `po<int>`. Read from the two forms and the
    OCaml arm; why the old side differs was not traced, and no source
    program was tried (the difference is the text of a type in a
    message after a failed lowering). Listed in
    `EXPLAINED_OLD_DIFFERS`.
79. **Until R3s the new side links the copy of a nullary constructor
    where OCaml, tracing, makes a node.** While an equation is in the
    environment `unify` traces GADT instances (`check_trace_gadt_
    instances`, ctype.ml:178-184) and `proper_abbrevs` gives every
    constructor its own memo (ctype.ml:200-202, pasted in the doc of
    `differential::tests::UNTIL_R3S`), so the expansion of `n0` is not
    in `simple_abbrevs` and `find_repr` of a later copy finds nothing.
    The kernel after R3r has no tracing: the expansion goes to the
    `simple` memo and a later copy of `n0` links to the node that was
    expanded. Seven seeds of the 10,000 of the pattern plan and five of
    the 2,000 explained ones differ in this and nothing else; they are
    listed (`UNTIL_R3S`, `EXPLAINED_UNTIL_R3S`) and R3s empties both
    lists. A prototype of the own memo was tried in this turn and
    abandoned: a nullary node has no slot 0 (its `b` is 0), so the
    memo needs a home, which is 8.11's to decide.
80. **The harness of pattern mode, as corrected by the run.** (a) A
    failed `Op::Gadt` cuts the equations it added on the new side, as
    the old side drops its environment (decision 62). (b) `Op::Lower`
    under `PATTERN` without `SCOPED` lowers without scopes on the new
    side (`Graph::lower`): the old side lowers without an environment
    there, and the locally abstract types and the types `reify` makes
    have scopes on the new side. (Eighth turn: this holds for every
    plan without `SCOPED`, not only under `PATTERN`: for a plan
    without scoped types `Checker::lower` is `Graph::lower`, so nothing
    changed for those plans.) (c) The equations are printed from
    `manifest.body`, which is a node of the graph. (d) The predefined
    types of the program are marked (`TypeTable::set_predefined`).

**Decided in the eighth skeleton turn.**

*What the reviews of pull requests 354, 356 and 361 decided* (81 to
85), *what today's checker learned about GADT instances* (86 to 88),
then what the turn itself decided, each with what was run.

81. **R3h and R3r are accepted as built**, with their builders' own
    decisions, each read in the final review of its pull request:
    `unify_newtypes` reads `umode` once (the table of assumed pairs,
    which its doc comment asks for; behind two nullary constructors of
    different types, an equation, and both types locally abstract);
    `match_unmatched` copies a shared chain from its first shared node,
    so that no slot of the source's chain is written; `reify` reads a
    row over a constructor as fixed, as `copy_refs` reads it; in
    `mcomp` the checks of one pair run before its child pairs are
    compared; two variables after expansion are `unreachable!`
    (OCaml's `assert false`); `mcomp_row` opens both rows
    (`open_row`: a write of the node's list that changes no type);
    `recover` puts the flags back before it reifies (`reify` reads no
    flag); `mcomp_fields` has no assertion for OCaml's
    `concrete_object` (OCaml reifies both sides before every `mcomp`,
    so the assertion cannot fail there; here a variable rest is
    compatible).
82. **`duplicate` is total** (R3r's first commit): the walk that makes
    the destination generic goes through generic nodes, and makes a
    node of level 0 generic. Test:
    `r3_tests::duplicate_copies_below_a_generic_node`.
83. **Decisions 64 and 70 were read against OCaml arm by arm**: the
    pattern arm of unify3 against ctype.ml 2333-2425 in the final
    review of pull request 356, and `mcomp`, `mcomp_type_decl`,
    `mcomp_fields` and `mcomp_row` against 1905-2039 in the final
    review of pull request 361. That pays item 9 of "Corrections after
    the review of the seventh turn".
84. **The `type_changed` loop of `occur_full` is not built; what it
    could show is recorded.** The loop (ctype.ml:1470-1476, pasted in
    decision 69) runs the walk again while `type_changed` was set
    during it. The flag is set in one place, the top of `unify`
    (`type_changed () := true`, ctype.ml:2238). The review of R3h
    wrote that the walk does not call `unify`. Read in this turn: it
    does, through an expansion. `occur_rec` calls `try_expand_head
    try_expand_once` in its handler (1400), an expansion that is not
    memorized is `subst` (1210), and `subst` unifies the stub with the
    body and the parameters with the arguments:

    ```text
    (* compiler/ml/ctype.ml:1129-1130 *)
        !unify' env body0 body';
        List.iter2 (!unify' env) params' args;
    ```

    So OCaml's loop runs a SECOND pass exactly when the first pass
    made a new expansion and did not raise. The second pass finds
    that expansion memorized (`find_expans`, 1194: no `subst`, no
    flag) and ends the loop. It can answer differently from the first
    only if the expansion changed a part the first pass had walked
    already, and that needs arguments that do not satisfy the
    declaration's constraint yet. (Corrected in the review of this
    turn. The turn wrote that a constrained parameter is bound "to a
    new instance of the constraint, which holds new variables and no
    node of the walked type". A constraint that makes two parameters
    one variable, `type t<'a, 'b> = int constraint 'a = 'b`, binds
    one ARGUMENT to the other: on `c<x, t<x, k<v>>>` with `c` and `k`
    abstract and `x` not bound, OCaml's first pass expands `t`, which
    binds `x` to `k<v>`, and finds nothing; its second pass finds `v`
    below `x`.) No type made from a source program is in that state:
    a type expression is unified with an instance of the declared
    parameters when it is made (`unify_param`,
    compiler/ml/typetexp.ml:374-382), so the annotation
    `c<'x, t<'x, k<'v>>>` is `c<k<'v>, t<k<'v>, k<'v>>>` from the
    start (run through OCaml in the review: that is the type its
    error message prints), and a copy keeps it. The kernel walks once
    and RESTS ON THAT INVARIANT: every constructor node satisfies the
    constraint of its declaration when it is made. The walk that
    lowers type expressions (R6) owes it; a hand-built graph that
    breaks it is outside the contract. What the next turn owes for it
    is in "Corrections after the review of the eighth turn" at the
    end of 8.11. The sentence of the review of R3h is corrected here
    and in decision 69.
85. **The types `reify` makes and the existential types of a
    constructor pattern ARE local constraints.** Both design turns
    before this one had it wrong. `Env.add_local_type` fills the map
    that `has_local_constraints` tests:

    ```text
    (* compiler/ml/env.ml:1047 *)
    let has_local_constraints env = not (Path_map.is_empty env.local_constraints)
    (* compiler/ml/env.ml:1802-1803 *)
    let add_local_type path info env =
      {env with local_constraints = Path_map.add path info env.local_constraints}
    (* compiler/ml/ctype.ml:970, an existential type of a constructor *)
          let new_env = Env.add_local_type path decl !env in
    (* compiler/ml/ctype.ml:1823, a type reify makes *)
        let new_env = Env.add_local_type path decl !env in
    ```

    So "the environment has a local constraint" is wider than "an
    equation exists": it holds from the first existential type or the
    first reified type on, until the environment of the case is
    dropped. Every sentence of 8.11 that turned on the difference is
    rewritten there against these lines (8.11, "When tracing is on").
86. **The mechanism of GADT instances, as today's checker had to
    build it** (pull requests 350 and 352; 71 and 48 programs through
    both compilers; CHECKER_DEPARTURES.md, place A1 and its "Second
    part"). It binds 8.11:
    (a) *the sets*: one per scope (`Env.add_gadt_instance_level`,
    env.ml:1307-1308); a member is compared by its representative
    (1314-1323); an addition is LOGGED and undone by a backtrack
    (`set_typeset`, btype.ml:749; unlike an equation, decision 68);
    (b) *the first member* of a set comes only from the expansion of
    an abbreviation under tracing (`expand_abbrev_gen`, ctype.ml:
    1215-1227); tracing is on inside `unify` under local constraints
    (176-191) and inside the wrappers `wrap_trace_gadt_instances`
    (typecore's `lower_args`; `unify_var`; `expand_head_trace`;
    `local_non_recursive_abbrev`); turning it on forgets the memorized
    expansions (`cleanup_abbrev`), and while tracing `proper_abbrevs`
    keeps a constructor's own memo (200-202);
    (c) *the readers*: `update_level` (587-589), the copy WITH the
    environment (770-774), `try_expand_head` (1270-1276), unify2
    (2289-2298), and the arm of `unify` for two locally abstract types
    (2258-2270: decision 65, built as `unify_newtypes`).
    In the Rust port of today's checker a unit that never adds a
    member pays one load and one branch at each of these sites, on a
    flag set where the first member is pushed: 7 of 788 units of the
    test suite ever set it, while 434 open an instance scope. The new
    checker pays no more (8.11, "The one read").
87. **A guard for a ported mechanism is chosen from where its STATE
    first becomes non-empty**, not from where its scope is created
    (lesson of pull request 350; the figures of 86).
88. **Where today's checker is still open without a program** (the
    list at the end of A1 in CHECKER_DEPARTURES.md) the new checker
    follows OCaml and the old side is not a judge. 8.11 names each.

*What the eighth turn decided itself*, each with what was run.

89. **A scoped lowering walks a chain of variant nodes in line**
    (G1 (c); a correction of built code). OCaml's `update_level` hands
    a variant to `iter_type_expr`, and `iter_row` goes on in a `more`
    that is a variant without handing that node back
    (compiler/ml/btype.ml:229-241):

    ```text
    let rec iter_row f row =
      List.iter
        (fun (_, fi) ->
          match row_field_repr fi with
          | Rpresent (Some ty) -> f ty
          | Reither (_, tl, _, _) -> List.iter f tl
          | _ -> ())
        row.row_fields;
      match (repr row.row_more).desc with
      | Tvariant row -> iter_row f row
      | Tvar _ | Tunivar _ | Tsubst _ | Tconstr _ | Tnil ->
        Misc.may (fun (_, l) -> List.iter f l) row.row_name
      | _ -> assert false
    ```

    As built, `lower_scoped` pushed every slot of a variant node, the
    `more` slot included, so each inner node of a chain was visited as
    a node of its own, and `lower_row_name` read the chain to its end
    from each: for a chain of n nodes whose name does not escape,
    1,002,000 steps at n = 1,000 and 100,020,000 at 10,000 (counted
    once the chain loop had a step; before, the loop was not counted
    at all). Now `Checker::push_row_children` pushes a `more` slot
    whose representative is a variant with the mark `IN_LINE`, and the
    walk pushes that node's children without a level test, a write or a
    name test. What changes besides the cost: an inner node of a chain
    KEEPS its level when the first node is lowered, as in OCaml (the
    fields and the row variable at the end are lowered through the
    first node). `Graph::lower`, the walk of a unit without a scoped
    type, still lowers the inner nodes (it pushes every slot); no walk
    of the kernel reads the level of an inner node except through a
    handle to it, and no generated case differs
    (`scoped_plan_agrees_on_generated_cases` and the pattern plans ran
    unchanged). Not chosen: bounding the walk of `lower_row_name` with
    marks (it keeps the visit of the inner nodes, which OCaml does not
    make). Cost for a unit that never lowers a variant with scopes:
    nothing (the arm is behind `types.scoped != 0` and the variant
    test that was there). Cost of the arm: `lower_row_name` reads the
    chain once for the name and the walk reads it once in line, 2n
    loads for n chain nodes; the first read cannot push children,
    because the name decides whether the node is rewritten as one row
    before its children are known. Step tests (rows.rs): the chain
    without a name, with a name that does not escape and with one that
    does (`unname_row`: one row of n fields), each linear between 1,000
    and 10,000; `match_fixed_fields` over a fixed row of n matched
    `Reither` fields (one step a field, which the loop did not count
    before). Lines added to a function expression mode runs:
    `lower_scoped_loop` gets one compare of `frame.extra`, a field of
    the frame it has popped (no load), per entry.

90. **The step tests the review of R3r asked for** (G1 (e)).
    `mcomp_fields` counted its merge steps; `mcomp_row` had two loops
    without a step (the tags only one row has, read when the other row
    is closed; the common tags) and now counts both (test-only code).
    Tests, relations between 1,000 and 10,000, each seen to fail with
    its structure broken:
    `r3_tests::mcomp_on_ten_thousand_fields_and_tags_is_linear` (two
    closed objects of n fields and two closed rows of n present tags
    whose types are one n-deep chain a side; with the table's test
    taken out: 4,007,006 against 400,070,006 steps for the objects and
    4,005,003 against 400,050,003 for the rows) and
    `r3_tests::recovering_inside_ten_thousand_nested_attempts_is_
    linear` (with a `recover` that reads every open record: 520,501
    against 50,205,001). The witness of the second is made of rows
    and not of arguments: the attempt of an argument cannot be nested
    in another, because inside one `generate_equations` is off and the
    arguments of a constructor go to `unify_list` (ctype.ml:2349-2350);
    the attempt of two variants is taken in pattern mode whatever the
    flags (2402-2411).

91. **`instance_poly` takes the polymorphic type node, and its copy is
    a tree walk on `frames` with the way in a dense table** (R3q;
    8.10). Signatures: `instance_poly(fixed, keep_names, poly, vars)`,
    `instance_label(fixed, argument, result, vars)`; the new variables
    are pushed on the caller's `Vec`. The way (`visited`) is
    `PolySlot::copy`, one load a child, set when a node is filled and
    put back by a `Linked` frame below its children. Not chosen:
    `Graph::copy`'s walk with a second memo (8.10 as written in the
    seventh turn): `copy_sep` has no memo across places, so a queue
    that fills each node once cannot be its walk; a recursion (the
    prototype of R3h recursed and its prompt forbade it: this
    prototype runs on `frames`, so the walk the prompt asks for was
    run).
92. **Whether a universal variable is free below a node is computed
    as OCaml computes it, one class at a time.** `mark_holders`: the
    inverse graph as a pool of 8-byte edges, then one propagation a
    class (the bound variables of the type; then each polymorphic type
    below the body), stopped at the class's binder, with one
    generation of `marks` a class. A node another class marked is not
    a place to stop: seen on `instance_poly_at_ten_thousand`, third
    shape, and on `a_polymorphic_type_inside_gets_new_universal_
    variables` (`r`, whose own variable must not make it a holder).
    Not chosen: a bottom-up pass with one bit (wrong on a type that
    reaches itself, and on two binders); OCaml's set of variables a
    node (a hash set a node).
93. **`conflicts` is asked by a walk, when it arises.** A node on the
    way met again after a binder was entered is copied again when a
    variable bound since is free in it (ctype.ml:1046). The kernel has
    no set a node, so `sep_conflicts` walks up from the binder's
    variables. It arises only for a type that reaches itself through a
    polymorphic type. Both answers have a hand-built witness; the
    second witness (`p = 'u. ('u, k2<p, 'a>)`) cannot be written as a
    source program and was followed through OCaml's lines by hand: a
    review should read it. Where a node is its own way back to the
    binder with nothing between, OCaml does not end; the kernel does
    not either, and no check is made for it.
94. **The delayed copies are one session after the walk, from a
    list.** `Graph::copy` is cut into `copy_begin`, `copy_ref`,
    `copy_drain` (built in the eighth turn; `copy` is the three in a
    row), and the loop body of `Checker::link_memorized` is
    `Checker::memorized_node`, so that `poly_pass` runs the same pass
    inside a cell session that also covers the fields the walk made.
    For a label the walk comes before the copy of the record type
    where OCaml's comes after; the two meet only through the session.
    One difference that follows is recorded and not built around:
    OCaml reads whether a row ends in a generic variable on the
    SOURCE, where a variable the record type's copy already reached is
    a `Tsubst` to a copy that is not generic (btype.ml:496-500), so a
    field of the argument whose row ends in a variable shared with the
    record type keeps its cell; the kernel, which has not copied the
    record type yet, duplicates it. No program is known (an object
    type whose row variable is a parameter of the record).
95. **A row with a universal variable below it is copied flat by
    `copy_sep_row`, and `copy_refs` does not change.** The row is read
    through its chain without opening it. Without `keep` the copy is
    an unopened node whose `RowFieldRow`s hold what each field reads
    now, with `m` and the flag by `fixed'`; with `keep` the homes are
    opened and the copy is built opened onto their references.
    `fixed'` reads whether the copy of `more` is a variable node at
    that moment, a stub included, as OCaml's `is_Tvar (repr more')`
    runs before the delayed copy is linked.
96. **`instance_label` of a label without a polymorphic type is a
    session of two roots and no stub.** It is the label of every
    record field access; it must not pay for the walk.

97. **Tracing is turned on by OCaml's test: the environment has a
    local constraint** (R3s; 8.11, (i)). Not chosen: "an equation
    exists" (the seventh turn): it cannot add a member either way, but
    it would keep memorized expansions that OCaml forgets and send the
    expansion of a constructor without arguments to the shared memo in
    a case that has an existential type and no equation. The bit is
    `LOCAL` of `Checker::gadt`.
98. **A set of instances is a list headed in a node of the graph, so
    that a restore undoes an addition** (8.11). An addition is one
    pool row and one `Graph::write` of the scope's head node. `Try`,
    `recover` and `Checker::restore` do not change. Not chosen: the
    pool's length in `Try` and in a mark of the walk.
99. **One byte, three bits, and one read a site** (8.11, the table):
    `LOCAL` decides tracing at the four entries, `TRACING` the
    expansion, unify2 and the two lowerings, `MEMBER` every read of a
    set. `MEMBER` is set where a pool row is pushed (decision 87), not
    where a scope is entered.
100. **While tracing, the memo of a constructor without arguments is
    a row of a dense table indexed by the node**, not a head bit
    (8.11). `has_cached_expansion` reads it behind `own_live != 0`.
101. **What the walk owes** (8.11, the contract): the scope and
    `leave_case`, a call for each existential type, `traced` around the
    four uses of `expand_head_trace`, `instance_in` and `copy_in` at
    the sites of `instance env`. `lower_args`, `unify_var` and
    `non_recursive_abbrev` trace themselves.
102. **The refusal is the escape pair** (8.11): no new kind of clash,
    no text in the kernel.
103. **The harness gets `Op::Scope` and environment-taking instance
    and lowering; R3s empties `UNTIL_R3S` and `EXPLAINED_UNTIL_R3S`
    and nothing else** (8.11).
104. **R3s is not issued in the eighth turn**, and three things are
    left to the turn that makes its skeleton (8.11, the last
    paragraph).

State at the end of the eighth turn: R3q is issued (8.10; its prompt is
in 8.4), R3s is not (8.11). `cargo test --lib tc::` after, with trunk
`b8b78d7d5` merged: 314 passed, none failed, 10 ignored, the ten tests
of R3q.

**Decided in the ninth skeleton turn.** R3s was written as a prototype
of the whole slice from 8.11, run against the generated cases and
against hand-built tests, and then taken out again: the tree holds the
skeleton. Each decision says what was run. Decisions 97 to 103 as the
prototype changed them: 99 (the first row of its table, by 105; the
rows of `instance`, `copy` and `expand_head`, by 107 and 111), 100
(the row is 16 bytes, by 109), 101 (`instance_in` is gone, by 107),
103 (the lists, by 110). 97, 98 and 102 stand as written.

105. **In pattern mode tracing is decided pair by pair, with a frame
     that turns it off.** 8.11 turned tracing on "at depth 0" of
     `unify_distinct`. OCaml makes the test at EVERY `unify`
     (`let reset_tracing = check_trace_gadt_instances !env in`,
     compiler/ml/ctype.ml:2235, pasted in 8.11), and `!env` changes
     inside one pattern unification: after the pair that adds the
     first equation, the next pair finds a local constraint, turns
     tracing on (with a cleanup of the memos) and turns it off when it
     returns; its parent's own work after it is not traced. On an
     explicit stack "when it returns" is a frame:
     `FrameKind::Untrace`, pushed below the pair by
     `Checker::late_pair`, which then runs the pair and everything it
     pushes with the loop of `run_frames` bounded above that frame.
     A unification that starts WITH a local constraint traces from
     its first pair to its end and needs none of this. So
     `unify_distinct` reads one byte: `gadt & (LOCAL | PATTERN)`, and
     only pattern mode without a local constraint runs its frames one
     pair at a time (`late_pair`, `resume_frames`); the loop of
     `run_frames` is not changed and keeps its one call of
     `unify_pair` (`run_frames` with a base no stack reaches returns
     after one pair). An attempt of pattern mode records whether
     tracing was on (bit 3 of `Try::flags`; the record keeps its 40
     bytes) and `recover` puts it back. Not chosen: a test at every
     popped pair (one load a pair of every unification); tracing from
     the first equation to the end of the top-level call (one cleanup
     where OCaml makes one a sibling, and the parent's work traced).
     Run: `r3_tests::a_pair_after_the_first_equation_of_a_pattern_is_
     traced`, which fails when `late_pair` never traces, and the
     10,000 cases of the pattern plan, where the seven seeds of
     `UNTIL_R3S` agree.
106. **A set is a list per scope; a lookup is linear in the members
     it reads, as OCaml's is** (decision 104, second point).
     `instance_level` answers the INNERMOST scope that holds the node
     (`find_instance`, env.ml:1314-1323), and an addition must be
     undone by a restore: one pool scanned once gives neither (a row
     an undone addition pushed is still in the pool, and a member can
     join an outer scope after an inner one). OCaml's lookup is
     linear a scope too (`Type_set.exists is_Tlink !r` runs over the
     set at every call). Measured on shape 0 of
     `instance_sets_at_ten_thousand` (n nested scopes of one member, a
     node in none): 2n steps; with the pool scanned for every scope
     1,002,000 steps at 1,000 and 100,020,000 at 10,000.
     `add_instance_chain` does NOT ask the list for each node of a
     chain: it marks the members of the target set once (one mark
     generation) and tests a mark a node; with a lookup a node, shape
     1 takes 1,504,503 and 150,045,003 steps. Corrected in the review
     of R3s: the generation is of `Checker::instance_marks`, an array
     of the sets' own, not of `marks`, which walks hold across the
     expansion that adds the chain ("Corrections after the review of
     R3s" at the end of 8.11).
107. **The copy with an environment reads the members once, and only
     `copy_in` exists** (decision 101 changed). OCaml asks
     `gadt_instance_level env ty` for every node it copies
     (ctype.ml:770-774). The kernel's copy leaves a forwarding row a
     copied source (`Graph::forward`), so `copy_in` runs
     `Checker::copy` and then reads the members of the visible scopes
     once, innermost first: a member whose representative was copied
     in this session gets its copy added to that scope (a mark keeps
     an outer scope from adding it again). Shape 2 of the step test:
     with a lookup a copied node, 1,004,003 and 100,040,003 steps.
     `instance_in(template)` of 8.11 is dropped: a template is made
     by `Graph::capture` from nodes and keeps no handle of them, so
     an instance of a template has no source that can be a member.
     What R5b owes for it is in the contract (8.11): a scheme that is
     generalized while `gadt & MEMBER` is set is kept as nodes and
     instantiated with `copy_in`. Not built: `copy ?env ~partial`
     (the pattern's instance; no caller in the kernel yet).
108. **The refusal of an expansion keeps what OCaml keeps.** OCaml
     tests `level < lv` AFTER `subst` (ctype.ml:1215-1226): the memo
     is written when the clash is raised. In `ExpandMode::Unif`
     `subst_traced` runs the plain expansion and then clashes, so a
     second expansion of that node finds the memo and is not refused,
     as in OCaml. In `Safe` and `Opt` OCaml's handler backtracks to
     before the expansion (`try_expand_safe`, 1251-1256;
     `expand_head_opt`, 1330-1335), which leaves a cleanup of the
     memos and nothing else, so the kernel makes no node: a cleanup,
     and `Ok(NONE)` or the clash. Run: `a_node_below_its_equation_is_
     not_expanded_under_tracing`, which fails without the level test.
     Not exact (review of this turn): `Btype.backtrack` cleans the
     memos only when a change was logged since the snapshot
     (btype.ml:773-784), and `subst` writes its memo without a log
     entry (ctype.ml:1122-1124, btype.ml:629-632). Where the
     expansion touched no older node OCaml keeps the memo, and a
     second `Safe` expansion of that node finds it and expands,
     where the kernel refuses again (item 8 of the corrections).
109. **The own memo of a nullary constructor is a row of 16 bytes
     with the node it continues with** (decision 100 changed: it said
     8). The first prototype had the expansion only, and the pattern
     plan ran out of memory on a type that reaches itself through a
     nullary abbreviation (`type rec rv = [#Nil | #Cons(int, rv)]`):
     outside tracing the copy of `rv` in the body links to the
     expanding node through the memo all `rv` nodes share; under
     tracing that memo is not used (`proper_abbrevs`, ctype.ml:
     200-202), and OCaml closes the type through the reference the
     copy inherits (`Mlink !abbreviations`, 793-799; `find_repr p
     !abbrevs`, 778-782). So a row has `parent` (the node whose traced
     expansion copied this one) and `type_index`, `inherit_own` gives
     each nullary constructor an expansion made its link or its
     parent, and `own_ancestor` walks the parents. A row whose entry
     a cleanup emptied ends a chain; a row that was never memorized
     is passed. NOT built, and recorded: the chain does not pass
     through a parent WITH arguments (the rows of R3m are keyed by
     slot 0 and a nullary node has none), so a nullary copy made by
     the traced expansion of a constructor with arguments continues
     with nothing; `has_cached_expansion` and `add_gadt_instance_
     chain` read the node's own row and not the chain behind it
     (`find_expans` goes on through `Mlink`, btype.ml:612-619). No
     generated case differs in either; the turn after owes a witness
     or the reason none exists.
110. **The harness: plan bit `INSTANCES` and `Op::Scope`; what the
     old checker judges** (decision 103 as built). Under the bit a
     case gets `Op::Scope` before a pattern unification (the
     generator is asked only under the bit, so the cases of every
     other plan are unchanged), `Op::Copy` and `Op::Lower` run with
     the environment on both sides, and a pattern unification that
     fails drops the whole environment (`leave_case`). A scope is a
     new environment, and the next expansion in a new environment
     cleans the memos (`check_abbrev_env`, ctype.ml:1163-1167): the
     new side of `Op::Scope` cleans them, as the walk will through
     `Checker::set_env` (seed 87,000,328 differed until it did).
     Observed (`old_checker_refuses_a_member_below_its_scope`, runs
     today): with a scope the old checker refuses to lower the
     expanded node, the `int` it was unified with, and a copy of the
     generalized member; without a scope it accepts all three.
     Against the prototype: 10,000 of 10,000 cases of the plan agree
     in the success mode (3,473 with a failure); of 2,000 explained
     ones 1,995 agree and five are listed
     (`EXPLAINED_INSTANCES_DIFFER`), each read against OCaml: two
     are decisions 77 and 78; two (17,000,064, 20,000,132) are the
     expansion of a failed trace, and there it is the NEW side that
     differs (corrected in the review of this turn; the turn read it
     the other way): after a failure OCaml's `unify` expands the
     types of the trace with tracing off (ctype.ml:2732-2737,
     1697-1701), which puts the expansion in the shared memo, as the
     old side does (`ctype::record_trace_expansions`); the new side
     expands no trace yet (item 5 of "Corrections after the review of
     the ninth turn", at the end of 8.11);
     one (4,000,069) is the chain of `try_expand_head`, which makes
     the unexpanded abbreviation a member before unify2 lowers it
     (ctype.ml:1271-1276 then 587-589): the new side refuses the
     abbreviation itself, the old side lowers it and reports a node
     below it. The lists of the pattern plan: `UNTIL_R3S` becomes
     empty (all seven agree); of `EXPLAINED_UNTIL_R3S` four agree and
     20,000,132 does NOT: decision 79 took it for the memo of R3s,
     and it is the trace expansion above, as is 4,000,045, which
     differs only once the new side traces. So after the build
     `EXPLAINED_UNTIL_R3S` is empty, `EXPLAINED_OLD_DIFFERS` stays
     `[8_000_098, 11_000_046]`, and the two seeds are
     `EXPLAINED_NEW_DIFFERS`, the new side's until it expands a
     failed trace.
111. **The cost for a unit without a member, measured, and the
     placements tried** (decision 104, first point). Instructions an
     operation, cachegrind, 100,000 iterations, each unification
     minus its `build_` twin, instance and copy minus `empty`:

     | Operation | trunk `b877a4814` | prototype, first placement | prototype, one byte | prototype, final |
     |---|---:|---:|---:|---:|
     | `unify_vars` | 152.0 | 152.0 | 152.0 | 152.0 |
     | `unify_ground1` | 152.0 | 154.0 | 154.0 | 154.0 |
     | `unify_ground3` | 871.0 | 882.0 | 881.0 | 880.0 |
     | `unify_datatype2` | 879.0 | 890.0 | 889.0 | 888.0 |
     | `unify_abbrev2` | 2,971.5 | 3,157.5 | 2,989.5 | 2,982.5 |
     | `instance7` | 320.7 | 320.7 | 320.7 | 320.7 |
     | `copy7` | 1,726.8 | 1,726.8 | 1,726.8 | 1,726.8 |
     | `checker_instance7` | 314.7 | 314.7 | 314.7 | 314.7 |

     The `_local` twins of the first three read the same. Every
     column but the first is the working copy of this turn with the
     prototype's bodies; the tree as committed has the same lines in
     every function these operations run (the guards) and `todo!`
     behind them. *First placement*: the chain test inside
     `expand_head_unif` and `subst` cut into a guard and an
     out-of-line body. The function profile showed 142 of the 186
     instructions of `unify_abbrev2` in `expand_head_unif`, which was
     no longer inlined into unify2, and 40 in the call of the plain
     `subst`. *Final*: `expand_head_unif` is as on trunk and its two
     callers add the chain where each already knows that a head
     expanded (`expand_head`; `unify_expanded`, inside its `if
     !unexpanded`); `subst_plain` is `#[inline(always)]` with one call
     in the cold `subst_traced`. *One byte*: `unify_expanded` reading
     `gadt` once for both `PATTERN` and `TRACING` instead of `umode`
     and then `gadt`: one instruction MORE on `unify_ground3` and
     seven more on `unify_abbrev2` than two loads, so two loads it
     is, and `umode` stays what unify2 reads. What remains against
     trunk is the table of sites of 8.11: one load and one branch at
     `unify_distinct` (2), at the arm of two nullary constructors of
     one type (2 a pair: `own_live`), at unify2's comparison (2), at
     `subst`, `memorize` and a nullary `find_expansion` that misses
     (2 each), and at `unify_expanded` after an expansion (2). No
     target is set (decision 46).
112. **The size and the order of the build; what the turn did not
     build** (decision 104, third point). The prototype's part that
     the builder writes is about 270 lines of code without comments
     (the working copy against trunk has 515, the skeleton as
     committed 295, of which 50 are the `todo!` and `allow` lines the
     build removes): the limit is 350. The order is ONE commit of
     bodies, since no body can be reached before the bits are set
     and every test of the slice sets one: the 25 bodies, the three
     setters (`GADT_LOCAL` in `add_gadt_equation` and
     `fresh_abstract`, `GADT_PATTERN` in `unify_pattern`), the guard
     of `resume_frames` deleted, the three seed lists as decision 110
     says; then a commit that removes the `ignore` and `allow` lines.
     The prototype was run with the test of `resume_frames` still in
     place (its diff keeps it); with `GADT_PATTERN` set by
     `unify_pattern` that test is never true where `resume_frames` is
     reached, so the build deletes it. Seen to fail with
     its structure broken: the four shapes of
     `instance_sets_at_ten_thousand` (decisions 106 and 107; shape 3
     with an addition that writes its head twice: the count is no
     longer one a member), `a_pair_after_the_first_equation_of_a_
     pattern_is_traced` (105), `a_node_below_its_equation_is_not_
     expanded_under_tracing` (108) and `a_constructor_expanded_under_
     tracing_is_not_linked_at_once` (with `has_own_expansion` always
     false). One test of built code changed:
     `the_newer_of_two_locally_abstract_types_is_expanded_once` makes
     its two nodes at the level of the newer equation, because an
     expansion under tracing refuses a node below it (ctype.ml:1226),
     and reads the expansion from the node's own memo once the shared
     one is empty. NOT built, each recorded as owed in 8.11: the two
     lowerings under tracing (`unify_fields`, ctype.ml:2490;
     `set_more`, 2610-2611: the first needs the level of `va` in the
     `Field` frame, the second the row as a node; today's checker has
     neither and no program shows them); a member whose
     representative is a VARIABLE, which `bind_leaf` lowers without
     the test (a member is a constructor or its expansion; a variable
     needs an abbreviation that expands to its parameter, expanded
     as a member); loops no step test drives wide: the parents of
     `own_ancestor`, the nodes of `inherit_own`, the scopes of
     `instance_scope_at`, the members `copy_in` adds.

State at the end of the ninth turn: R3s is issued (8.11; its prompt is
in 8.4). `cargo test --lib tc::` after, with trunk `8b9bf5a8e` (R3q
merged) merged: 325 passed, none failed, 13 ignored, the thirteen
tests of R3s.

**Decided in the tenth skeleton turn** (R3i; section 8.12 has the
tables).

113. **`ExpandMode::Rigid` is the public expansion** (built in the tenth
     turn, commit "the rigid expansion is the public one"). OCaml:

     ```text
     (* compiler/ml/ctype.ml:3184-3189 *)
     let expand_head_rigid env ty =
       let old = !(rigid_variants ()) in
       rigid_variants () := true;
       let ty' = expand_head env ty in
       rigid_variants () := old;
       ty'
     ```

     `expand_head` is `try_expand_head try_expand_safe` (1283-1289):
     public abbreviations, a clash of a step is `Cannot_expand`, and the
     chain of GADT instances is added (1271-1276). Since R3b `Rigid`
     counted as private in three places of `expand.rs`. Now
     `Checker::expand_head` sends `Rigid` to `expand_head_rigid`, which
     sets `Extras::rigid_variants`, runs the `Safe` expansion and puts
     the flag back; the three tests read `mode == ExpandMode::Opt`.
     `rigid_variants` is read at ctype.ml:2666 only (`unify_row_field`'s
     `redo`), which an expansion reaches when it unifies a constrained
     parameter. Test: `the_rigid_expansion_is_public_and_adds_the_chain`.
     This pays item 12 of the list after the ninth turn.

114. **`moregeneral` takes no snapshot; `equal` and `matches` take
     one.** `moregeneral` (ctype.ml:3104-3124) saves and restores the
     current level and nothing else. What `moregen` writes: links of
     the variables of the pattern's instance (new nodes, held by nothing
     afterwards), with `inst_nongen` links of the pattern's variables
     that are NOT generic, which `instance` shares with the scheme
     (`may_instantiate`, 2921-2923: every level but `generic_level - 1`),
     levels of the subject's copy (`update_level` in `moregen_occur`),
     and resolved references of the pattern's rows (`set_row_field e1`,
     3069-3086). The one caller is `Includecore.value_descriptions`
     (includecore.ml:47), always with `inst_nongen = true`: a weak
     variable of an implementation is instantiated by its interface and
     stays so. Today's checker has the same form (types/ctype.rs
     `moregeneral`: no snapshot). The kernel follows: no speculation,
     which is also the cheaper form in `Mode::Success` (no trail). The
     memo of constructors without arguments keeps the expansions made in
     the two copies until the next cleanup, as OCaml's does. This
     corrects two sentences that listed `moregeneral` among the places
     that undo: 8.2, decision 6 ("A snapshot in `Mode::Success`") and
     8.3 ("R3i: every relation restores its speculation").

     `equal` (`eqtype_list`, 3361-3369) backtracks on every exit, and
     `matches` (3167-3179) snapshots BEFORE `rigidify` and backtracks
     after either answer: one `Graph::speculate` each, closed with
     `Checker::restore`.

115. **What the memos hold after `equal` and `matches` is not compared.**
     OCaml's `backtrack` cleans the memos only when a change was LOGGED
     since the snapshot (btype.ml:776-779), and a write to a node made
     after the snapshot is not logged (`log_type`: `if ty.id <=
     !last_snapshot`). `Checker::restore` cleans them when the trail
     grew, and inside a speculation the kernel logs every write: a
     compressed path, the link of a new parameter, an opened row. So
     after an `equal` that expanded a type with arguments the kernel has
     forgotten the memo of constructors without arguments where OCaml
     keeps it; after one that expanded only constructors without
     arguments both keep it (`equal_renames_bijectively_and_restores`
     shows that case). Today's checker takes no snapshot in `equal` at
     all and never cleans. The difference is the identity of a later
     copy of a nullary abbreviation (O11), which is in no contract.
     The harness therefore forgets the memos on both sides after
     `Op::Equal` and `Op::Matches`. Open (question 2 of the pull
     request): make `Checker::restore` exact by counting only trail
     entries of nodes older than the speculation that are not a
     compression and whose level, tag or `a` changed.

116. **One loop, the frames of unification, no trace.** Every caller of
     the three relations reads a boolean (includecore.ml:47, 92, 127,
     131, 154, 157, 392, 429, 481, 488, 571, 583, 584, 726, 737;
     typedecl.ml:815, 911, 1017, 1224, 1738; typecore.ml:879;
     ctype.ml:4351), so no trace is built and a clash of a callee cuts
     `Checker::trace` back to its length at the entry (decision 25).
     `moregen` and `eqtype` are `Checker::relate_frames` with a
     `Relation` (2 bytes) passed down, over `Checker::frames` with the
     frame kinds unification has: `Pair`, `LeavePoly`, `PackageEnd`,
     `Field`, `RowField`. So `enter_poly`, `unify_univar` (R3g),
     `unify_package` and `package_end` (R3p, `PackageDecls`) and
     `push_children` are called as they are. The visited pairs are
     `Checker::related`, a hash set of ORDERED pairs (`Type_pairs` keys
     the pair as given), a field of its own: `pairs` and `compatible`
     belong to pattern mode. It is cleared at the entry of each relation
     (`Type_pairs.create`). A hash set because no dense index of a pair
     of nodes exists. `moregen` keeps OCaml's order of work (a field or
     tag is a frame, popped where OCaml reaches it), because what it
     links stays; `eqtype` restores everything and pushes the pairs of a
     row at once.

     Three kernel forms replace OCaml lists, with the same answers:
     the renaming of `eqtype` (`subst`, searched with `List.assq` and
     `List.exists`: O(variables) a pair) is `Checker::renaming`, one
     12-byte row a node live by a generation, O(1) a pair;
     `normalize_subst` (3191-3198, a scan a pair) runs only when the
     trail grew since the last pair of variables; `all_distinct_vars`
     (3156-3165, `List.memq`) is two passes, the expansions first and
     then one generation of marks. `rigidify_rec`'s `List.memq ty !vars`
     is always false for a node met for the first time (the walk marks),
     so it is not built.

117. **`duplicate_type` is not `Checker::duplicate`; today's checker is
     the judge of the answers, and is set aside by name in three
     places.** The generated cases found, in order:
     - `Checker::duplicate` (R3h) copies variables; `Subst.type_expr
       Subst.identity` keeps them (subst.ml:135-143). `moregeneral`
       needs the second: `Checker::duplicate_type` (R3i). Its copy also
       asks no memo (`Tconstr (type_path s p, args, ref Mnil)`,
       subst.ml:172), where `Checker::copy` links a constructor without
       arguments to a memorized node; and the row variable of a static
       row becomes a new generic variable (`dup`, subst.ml:191-207).
       Today's checker was right on all three and the first prototype
       wrong.
     - Today's `equal` answers `false` for two rows of which the right
       one was extended by a unification: it expands the FIELD
       `right.row_more` where OCaml expands `row_more row2`, the
       function that follows the chain (ctype.ml:3327). 68 seeds
       (`ROWS_OLD_EQUAL_DIFFERS`, `UNIVARS_OLD_EQUAL_DIFFERS`).
     - Today's copy keeps `Tnil` as it keeps a variable, where
       `Subst.typexp` copies it: 7 seeds (`ROWS_OLD_NIL_DIFFERS`,
       `UNIVARS_OLD_NIL_DIFFERS`); the answers agree.
     - Five seeds were pinned unclassified at the end of the first
       turn and are decided (second turn of the tenth). Three were the
       DESIGN's fault (16000113, 20000085, 81000256): `duplicate_type`
       restored its speculation after the pass that shares the
       references of a row (`Checker::copy_refs` opens the source row
       when the copy keeps its row variable), so the source was
       unopened again and its fields had references the copy did not
       hold. In OCaml the copy keeps them (`let e = if keep then e else
       ref None`, btype.ml:374, with `keep = not dup`, subst.ml:213),
       and `set_row_field e1 (Reither (c2, [], m2, e2))`
       (ctype.ml:3074) then joins the pattern's field to the SUBJECT's.
       Today's checker was right. The restore now runs between the
       copy and the pass; test
       `the_copy_of_the_subject_shares_the_references_of_its_rows`
       (fails on the first prototype); the three seeds agree and are in
       no list. Two are today's checker (5000086, 13000118,
       `UNIVARS_OLD_FREE_UNIVAR_DIFFERS`): `moregen_occur` calls
       `occur_univar env ty` unconditionally (ctype.ml:2917-2918), and
       with no binder entered a `Tunivar` raises (1584-1585);
       types/ctype.rs runs it only `if !univars.pairs.is_empty()`, so it
       accepts a weak variable against a free universal variable.
       No seed is unclassified.
     - What the mechanical classification of the 75 other seeds tests:
       both sides fail at the same operation or at none and print the
       same number of lines, and EITHER every line is the same or is
       `equal = false` on the old side and `equal = true` on the new
       (the `EQUAL` lists), OR every answer line is the same and the
       new form has more occurrences of `nil` than the old (the `NIL`
       lists). Read in full: 1000013, 3000021, 4000062 and 2000018 of
       the first class (each has a unification of two rows before the
       `equal`), 32000157, 54000224 and 5000060 of the second (the old
       side prints a `nil` of the subject as a back reference to the
       pattern's). The second condition is loose: it would also take a
       case whose forms differ elsewhere while a `nil` count differs;
       the 4 of the 7 not read are pinned on it alone.
     The plain relation plan (10,000 cases) has no difference.

118. **The size and the order of the build; what the turn did not do.**
     The prototype is 803 added lines (comments inside bodies
     included): the limit of the slice is 900 lines of code outside doc
     comments. One commit of bodies and one that removes the `ignore`
     lines, as R3s. Not done in the tenth turn: the source programs of
     8.12 were run through the OCaml compiler only (second turn), not
     through the Rust one; the step tests were not seen to fail
     with the renaming or the marks of `all_distinct_vars` replaced by a
     list scan (a step counts a frame, and a scan would have to count
     its own entries: the two shapes pin linearity of the frames only);
     no hand-built test reaches `normalize_renaming` past its first
     compare, the package arm, the arm of universal variables, the
     `Reither` arms of `moregen_row_field`, `filter_fields` with
     `erase`, or the two expansions of `eqtype_row` and `relate_fields`
     (the generated cases reach rows, fields and universal variables;
     nothing reaches packages); the bench table of `tc_kernel` was not
     taken; R3j and every item of J3 but decision 113.

State at the end of the tenth turn: R3i is issued (8.12; its prompt is
in 8.4). R3j has no design.

Decided in the eleventh skeleton turn (trunk `265ff7e37`; `cargo test
--lib tc::` before: 344 passed, 0 failed, 9 ignored, seen, 1,073
seconds). They are section 8.13 in short; the tables are there.

119. **Subtyping is a loop of its own on a stack of its own.**
     `Checker::subtype_frames` over `Checker::subtyping`, of `SubFrame`
     (16 bytes) with the kinds `Pair`, `Constrain`, `Leave`,
     `Invariant`, `Back`, `Close`. Not a third `Relation` of
     `relate_frames`: a pair of `subtype_rec` carries a trace, collects
     where the relations clash, and three arms need a continuation the
     frame kinds of unification do not have (3689-3690, 4037-4038,
     4114-4134). No signature, `Relation` or `FrameKind` of R3i changes,
     so the R3j builder has no first commit against R3i's code.

120. **A constraint is 16 bytes and the caller owns the collection.**
     `Constraint` (changed from 12 bytes with a trace length): the two
     types, the index of its innermost `TraceLink` (the trace is a
     parent-linked pool, `Mode::Explain` only), the index of its
     innermost `HeldScope`. `Checker::subtype` fills a `Coercion` the
     caller passes (`out: &mut Vec<Constraint>` before);
     `Checker::force_subtype` takes it by reference. `force_subtype`
     opens each constraint's scopes with `open_scopes`, which moves
     from one chain to the next (linear over a coercion; the step test
     reads 1,004,000 against 100,040,000 steps when the stack is made
     again a constraint). After a failure `Checker::subtype_trace` has
     the first component of OCaml's `Subtype` and `Checker::trace` the
     second; neither is expanded (`expand_trace`, 3615, 4228, is the
     printer's, as it is for a unification: the item of the ninth
     turn's list, still open).

121. **`TypeTable::occurs` holds `Variance.get_upper`.** Two bits a
     parameter (`MAY_POS`, `MAY_NEG`) where it held one; still one byte
     a parameter; `TypeTable::upper` reads them and answers `None` for
     a type whose declaration the table does not have, which
     `subtype_constr` turns into the constraint of the two
     constructors (`with Not_found`, 3703-3704) and `enlarge_visit`
     into the node itself (3500). Built in this turn, with
     `the_table_keeps_both_upper_bits_of_a_variance` on a compiled
     unit. Until R5a fills the rows of other units' types, a coercion
     through such a type is as strict as unification.

122. **Quiet regions; the tags of a row are classified before a pair
     is walked.** The two places that drop what a walk collected keep
     OCaml's side effect (the pairs stay in the table) by walking with
     `Coercion::quiet` raised. One difference is taken: `subtype_row`
     reads every common tag (`field_now_at`) in one pass before any
     pair is walked, where OCaml reads tag k after the walks of the
     tags before it. The two differ only if such a walk changes a tag
     of the same row, which needs an expansion that unifies a
     constrained parameter with a type of that row. Not put to OCaml
     as a program.

123. **Departures taken, none with a source program** (each named in
     the doc comment of its body, each to be confirmed or refuted by
     the review):
     - The trial of two packages of different paths calls the typer's
       `unify` (4091), which empties the list of scopes (`let unify env
       ty1 ty2 = unify_pairs (ref env) ty1 ty2 []`, 2773); inside a
       polymorphic type the constraints OCaml makes after such a trial
       record no scope until that type is left. The kernel keeps the
       walk's scopes through the trial.
     - `expand_abbrev_opt` at 3706 is not under `safe_abbrev`: a clash
       of it is an uncaught `Unify` in OCaml. Here the pair goes on to
       step 13 and is a constraint.
     - `generic_abbrev` tests `(repr body).level = generic_level`
       (1356). The kernel reads the flag `ABBREV` (through the
       spellings of a module alias, `Checker::expands`): every manifest
       of the table is a template and the destination of an equation
       is a generic copy. A declaration whose body is not yet
       generalized (inside its own recursive group) cannot be coerced
       through: no expression is typed there.
     - A path through a module alias is expanded only when what it
       spells has a manifest (`Env.find_type_expansion` goes through
       the alias); the kernel's expansion of such a path takes one
       step more (to the constructor it spells), and that intermediate
       pair is in the table where OCaml's is not.

124. **What R3j leaves to R6e is refused, not asked.** Table of
     8.13. Every arm left out either accepts or makes the constraint
     of the two types; the kernel makes that constraint. No trait is
     added for them: R6e adds its arms at steps 9 and 11 of
     `subtype_pair`, with the context of a constraint.

125. **`build_subtype` is a loop with a results stack; `visited` is a
     dense table with two numbers.** `EnlargeFrame` (16 bytes),
     `Enlarged` (8), `EnlargePath` (12), `Checker::path_entries` (four
     bytes a node of a unit that enlarges). The list is a list of the
     path with cuts, not a mark that stays (8.13, "The visited list").
     The first form of the acceptance test expected two new objects
     for `type rec t = {next: t}`; the prototype made one, because the
     copy of `t` in the expansion is a link to the expanded node
     (ctype.ml:782) and the object is found on the path. The test was
     corrected to the lines and a chain of three different
     abbreviations now shows the budget.

126. **What the eleventh turn did not do.** K1 (4), the harness:
     no `Op::Subtype`, no `Op::Enlarge`, no plan bit, no vacuity test,
     no generated cases, so today's checker was not read as a judge of
     R3j and no seed list exists for it. K1 (6) in part: no source
     program was run through either compiler; no built OCaml compiler
     was in the sandbox and the turn's budget went to the prototype
     and its tests. The step shapes pin the linearity of the frames;
     of the structures only the table of pairs, `open_scopes` and
     `on_path` were broken and seen to fail a test. No hand-built test
     reaches: the package arm of `enlarge_visit`, `expands` through a
     spelling with a manifest, a private abbreviation with arguments,
     `Equiv` (no arm makes it: `loops` is empty), the wrap of
     `path_clock`. All of K2 is still owed: nothing of it was started.

State at the end of the eleventh turn: R3j is issued (8.13; its prompt
is in 8.4) WITHOUT its harness operations, which are a task of their
own before or beside the build (the prototype is the oracle for them).
The whole filter with the prototype in place and the ignored tests
included is in the pull request, with the count seen.


### 8.7 The hot paths of unification (K2)

K1 (TC_KERNEL_R3.md, "K1") left unification at these figures, in
instructions per operation, net of the build-only twin:

| Operation | K1 | K2 target | What is removed |
|---|---:|---:|---|
| `unify_vars` | 192 | ≤ 150 | root frame (a), `bind` (b) |
| `unify_ground1` | 157 | ≤ 125 | root frame (a) |
| `unify_ground3` | 701 | ≤ 640 | root frame (a); the walk stays (d) |
| `unify_vars_local` | 267 | ≤ 155 | (a), (b), no-op lowering (c) |
| `unify_ground1_local` | 235 | ≤ 130 | (a), (c) |
| `unify_ground3_local` | 1014 | ≤ 660 | (a), (c) four times |

The targets are arithmetic on the K1 table and the attribution of
TC_KERNEL_R3.md, not measurements: the builder measures first and reports
where a target was wrong. A local form may cost at most 6 instructions more
than its generic form per lowering it does not need (one load and one
compare each): that relation is the gate, the absolute figures follow.

(a) **The frame push and pop of the root pair.** `unify_distinct` pushes
the pair it was given as a `Frame` and `run_frames` pops it at once
(16 bytes written and read, a length update each way, the `match
frame.kind`). The root pair goes to `unify_pair` directly; `run_frames`
runs only when that call left frames above `base`. The lines that go:
`self.push_pair(left, right)` in `unify_distinct`. The trace of a failure
at the root is unchanged: `explain_failure` receives the root pair as the
failing pair when no frame is above `base`. About 30 instructions on every
top-level unification.

(b) **`Checker::bind`'s 48 instructions for two variables.** For a target
that is a variable `bind_routed` links and then calls `lower_to`, which
calls `Checker::lower`, which calls `Graph::lower`: a work list cleared,
pushed and popped for one node. OCaml's is one compare
(`if ty.level > level`, ctype.ml:586, after `link_type`,
ctype.ml:2221-2222). The variable-to-variable arm becomes: link, then
`if target.level > var.level` one `Graph::write` of the level. No call.
Target for `bind` in `unify_vars`: at most 20 instructions.

(c) **A lowering that lowers nothing.** `lower_to` tests only for the
generic level. Every other call pays `Graph::lower`'s set-up, which is the
60 to 78 instructions a `_local` form costs over its generic form (two
calls in unify2, one in the nullary shortcut, one in a binding to a
variable). `lower_to` first reads the representative's level and returns
when it is not above the target, as the outer `update_level` does
(ctype.ml:635). One load and one compare.

(d) **No walk for a right side without children.** `Checker::occur` and the
binding walk start a mark generation and a work list for a node that has
no child (a nullary constructor that is not the shortcut's: two different
paths about to clash, an abbreviation's expanded head, a binding of a
variable to `int`). When the right node's arity is 0 and it is not a
variable, the answer is "does not occur" without a walk; a binding still
lowers that one node (c). None of the six bench operations takes this
path: the builder adds `bind_ground1` and `bind_ground1_local` (a variable
against a nullary constructor) with their build-only twins, measures them
before the change, and reports both. Target: within 25 instructions of
`unify_vars`.

**The deferred occurrence check (decision 1 of 8.6): designed, and not
part of K2's gate.** It removes no instruction from the six operations:
for a three-node pair the walk before the root link visits the two children
of the right node, and a walk after the unification would visit the same
nodes with a costlier mark (three states in place of two). It pays only
where the per-pair walks add up: the `n(n+1)/2` of a deep equal pair
(decision 6 of 8.2). So it is a slice of its own, K2b, built only when a
profile of real units (R5c) shows `Checker::occur` above 2% of checking.
The design, so that it is not rediscovered:

- *When.* `Mode::Success` only, and only at the end of a top-level
  `unify_distinct` (`depth == 0`) that linked at least one structure pair
  (a counter in `Checker`, reset at the top). `Mode::Explain` never
  changes. The walk of a binding (`binding_walk`) stays: it lowers levels
  in the same pass and is not what is quadratic.
- *What it visits.* Every node reachable from the right node of the root
  pair without entering an object or a variant row (`stops_occurrence`,
  ctype.ml:1403), each once, with the three marks of `occur_expanding`
  (free of a cycle, on the path, done). A graph was acyclic in this sense
  before the unification, and every structure pair linked during it is
  below the root pair, so a cycle made by a missed occurrence is reachable
  from there.
- *The expansion rule.* A node met again while on the path is a cycle. As
  in `occur_rec` (ctype.ml:1396-1402), the innermost constructor on the
  path between the two meetings is expanded (`expand_head`, `Unif`) and the
  walk goes on in its expansion in place of its arguments; when no
  constructor on that stretch expands, the unification fails. This is what
  keeps the cycle through an abbreviation's argument that
  `create_recursion` accepts (ctype.ml:2308, 2428-2436).
- *Termination before the walk.* With the per-pair check gone the loop of
  `run_frames` runs on a graph that may hold a cycle. Every pair it pops
  either has one representative on both sides (skipped) or links one
  representative to another, and a link is never undone in `Mode::Success`;
  an abbreviation node expands once per memo. So the number of pairs that
  do work is bounded by the nodes and the expansions, and every walk
  inside (`binding_scan`, `reaches`, `closed_over`, `lower_scoped`) uses
  marks or stops at a level it has written.
- *What a failure leaves.* What any failure in `Mode::Success` leaves:
  `unexplained_failure` outside a speculation, the owner's restore inside
  one. The index of the failing operation is that of the same top-level
  unification.
- *Cost.* One step per node reachable from the root, once per top-level
  unification that linked a structure pair, in place of one walk per
  linked pair: never more steps than the walk of the root pair costs today.
- *Tests it must pass before it merges.*
  `unify_of_equal_deep_types_fits_the_stack` with its bound replaced by a
  relation (n = 10,000 at most 11 times n = 1,000);
  `build_plan_agrees_on_generated_cases`, whose operations unify a type
  with a tuple or a child of itself (10,000 cases, the same failing
  indices); `occurrence_through_an_abbreviation`.
- *What is not proven.* That the final graph has a cycle exactly when one
  of OCaml's checks at the time of a link would have failed. The argument:
  a link only identifies two nodes whose children are then unified pair by
  pair, so a path that existed stays, and an expansion is a function of the
  declaration. It is an argument, not a proof, and it is why K2b waits for
  a profile that needs it.

The build prompt of K2 (the common part of 6.0 is prepended):

```text
You build K2: the hot paths of unification, with no change of behaviour.
Read AGENTS.md; compiler-rust/docs/CHECKER_REWRITE.md section 8.7;
compiler-rust/docs/TC_KERNEL_R3.md ("Machine and method", "Attribution",
"K1"); compiler-rust/src/tc/unify.rs and expand.rs whole;
compiler-rust/benches/tc_kernel.rs.

First edit, before any change to src/tc: add the bench operations
bind_ground1 and bind_ground1_local with their build-only twins, and
measure all eight unification operations on the base as TC_KERNEL_R3.md
does. That table is your "before".

Then one commit per item of section 8.7, in the order (c), (b), (a), (d),
each measured whole: (c) lower_to returns when the representative is not
above the target; (b) a binding of a variable to a variable links and
writes one level; (a) the root pair goes to unify_pair without a frame;
(d) no walk for a node without children. You do not build the deferred
occurrence check.

Your oracle is the bench and the tests. No test changes, none is ignored,
and these pass on every commit:
  cargo test --manifest-path compiler-rust/Cargo.toml --lib tc::
which includes the Full tier and the plans of the differential harness
(explaining mode, scoped types, made nodes) at 10,000 cases each. A step
count in a test that goes DOWN is reported, not edited: stop and say which.

Relations to hold: each _local operation costs at most 6 instructions more
than its generic form per level test it makes; unify_vars is at most 150
and bind inside it at most 20; no operation of the K1 table that is not a
unification moves by more than 2. Shortcuts that count as failure: a level
test that reads a node that is not a representative; skipping a lowering
when types.scoped != 0 without the scope test of Checker::lower; a walk
skipped for a node WITH children; a change in src/tc/graph.rs, level.rs or
template.rs; any change of what Mode::Explain does.

Report the table before and after per commit, and the instruction count
of the CI check (tc is not on a compiler build's path: say so if it is
unchanged).
```

### 8.8 Universal variables, polymorphic types and packages (R3g, R3p)

Decisions 49 to 52 of 8.6 are what was decided and observed; this section
is the design a builder reads. Every function named is in `tc/rows.rs`
unless it says otherwise, and its doc comment lists its steps.

**What the data is.**

| Thing | Stored as | Bytes |
|---|---|---:|
| Universal variable (`Tunivar name`) | one node, `TUPLE \| EXTENDED`, arity 0, `a` the row of `ExtraDescriptor::Univar(name)`; no slot | 16 |
| Polymorphic type (`Tpoly (body, tl)`) of `k` variables | one node, arity `1 + k`: slot 0 the body, slots 1 to `k` the bound variables in the order of `tl`; `a` a row `ExtraDescriptor::Poly` | 16 + 4 × (1 + k) |
| Descriptor row | one per variable or polymorphic type MADE (a segment's, the typer's); a copy shares the row of its source | 12 |
| Scope (`(cl1, cl2) :: (cl2, cl1)` of `univar_pairs`) | `PolyScope { left, right, left_len, right_len, partners }`: the two binder lists by list index and length, and the first of `left_len + right_len` consecutive partner nodes | 20 |
| Partner (`ref None` beside a bound variable) | one node `partner_node(partner)`: a variable at level 0 whose `a` is the partner or `NONE` | 16 |

For a unit with `U` universal variables and `P` polymorphic types of `K`
bound variables in all, made or copied: `16 × (U + P) + 4 × (P + K)`
bytes of nodes and slots, and at most `12 × (U + P)` of rows. Each entry
into two polymorphic types of `k1` and `k2` variables adds `16 × (k1 +
k2)` bytes of partner nodes, which stay until the graph is cut back
(open question 2), and 20 bytes of scope for the time the bodies are
unified. Pinned by `r3_tests::sizes_of_universal_variables`, which runs
today.

`Extras::univars` counts the rows `Extras::univar` made. It is the one
read that decides whether a walk for universal variables can find
anything: 0 means no node of the worker is a universal variable.
`TypeTable::variances` and `TypeTable::occurs` hold, per type and
parameter, whether the parameter may occur in the type's definition
(`May_pos` or `May_neg`); `TypeTable::may_occur` reads them and answers
true for a type without a declaration row.

**What is wired** (built in the skeleton, not to be changed by the
builder). `unify_pair`: two heads with `EXTENDED` that are both universal
variables go to `unify_univars` (out of line): `unify_univar`, the right
node's level lowered to the left's, the link (ctype.ml:2244-2247).
`bind_routed` and the two variable arms of unify3 call `free_of_univars`,
which returns at once when `Extras::univars` is 0 and otherwise calls
`occur_univar` (ctype.ml:2216-2219, 2316-2323). unify3 has the arm of two
universal variables before `create_recursion`. `extended_children` calls
`enter_poly` for two polymorphic types of which one has a variable.
`run_frames` pops `LeavePoly`. `unify_distinct` calls `leave_scopes` on a
failure. `join_either` calls `split_univars` when `Extras::univars` is
not 0 and the record does not have `ROW_UNIVARS`; `row_field_end` runs
the join again when it has. `occur_univar` itself is built: it calls
`free_univar` and makes the pair.

**The five bodies of R3g.**

| Function | OCaml | Cost |
|---|---|---|
| `unify_univar(t1, t2)` | ctype.ml:1544-1559 | per scope from the innermost, a scan of both binder lists, twice: O(scopes × bound variables), one step a slot |
| `enter_poly(left, right)` | ctype.ml:1656-1679 | no scope open: `k1 + k2` partner nodes, one scope, two frames. `s` scopes open with `B` bound variables: `B + k1 + k2` marks, and the escape walk only when a bound variable is already known |
| `univars_escape(binder, other)` | ctype.ml:1612-1652 | the family: one pass over the scopes; then one walk of `other`, each node once, with `g.work` as its stack |
| `free_univar(ty)` | ctype.ml:1563-1607 | one walk with `g.work`; a node is visited once per context it is met in after the one that marked it closed, as OCaml's `visited` map |
| `split_univars(frame, gained)` | ctype.ml:2685-2697 | one `free_univar` per gained type; the types that hold one are unified pairwise through the frame stack, in two phases |

`free_univar` keeps no set of bound variables. A context is a generation
of `Checker::marks`: entering a polymorphic type takes a new generation,
marks its bound variables with it and pushes two entries on `g.work`
that close it again; `Extras::open_polys[generation - first]` says
whether a generation is still open. A node whose mark is an open
generation was visited in a context that still holds (skip it, or for a
universal variable: bound); any other mark is stale. So a node first seen
inside a polymorphic type is seen again outside it, which is what OCaml's
`visited` map of bound sets does, without a set per node.

`split_univars` is two-phase because the unifications it asks for run on
the frame stack. First run: the gained types that hold a universal
variable move out of the two gained lists; when both sides have one, the
record gets `ROW_UNIVARS`, a `RowFieldEnd` frame goes below the pairs
`(tu1, each other)`, and the join is put off. Second run, from
`row_field_end`: the join, without splitting. One side only: a clash with
the pair of `occur_univar`.

**The order of a copy** (btype.ml:504-541; `copy_type_desc` maps `tl`
before the body). `Graph::instance`, `Graph::copy` and `Checker::copy`
copy a polymorphic node's slots in slot order: the body, then the
variables. No case can tell the two orders apart: a copy visits each
node once whichever slot reaches it first, the level of a copy is read
from its source, and the forms number nodes in their own traversal. The
kernel tier agrees with the old checker on 10,000 generated cases of
instances and copies of polymorphic types
(`kernel_tier_agrees_on_universal_variables`). `Subst` is not in the
kernel. A copy of a polymorphic node of `k` variables costs one node and
`1 + k` slots, as any node of that arity; neither `instance` nor `copy`
tests for a polymorphic type.

**Commit order**, checked against what is wired: `free_univar` first (its
callers are `occur_univar` and, later, `split_univars`); then
`unify_univar` and `enter_poly` together (`unify_univars` and the unify3
arm call the first, `extended_children` the second, and a body pair
inside a scope reaches `unify_univar` at once); then `univars_escape`
(reached from `enter_poly` only with a known binder); then
`split_univars` (reached from `join_either` as soon as a unit has a
universal variable, so every generated case with a variant waits for
it). The generated cases are un-ignored with the last commit.

**Packages (R3p).** `unify_package` merges the two name lists of the two
`PackageRow`s once: a name both have gives the pair of the two arguments;
a name one side has asks `PackageDecls::complete` of the OTHER side's
module type, and an answer that is not a type is a clash. It saves the
left descriptor, pushes a `PackageEnd` frame and then one pair a name,
reverses the pairs' part of `frames` so that they pop in name order, and
on a clash cuts `frames` and `saved` back. `package_end`: equal paths are
done; otherwise `PackageDecls::compatible` decides. What R5a must supply
is the trait's three functions (decision 52) and the installation of the
supplier in `Checker::packages`.

**Tests.** In `r3_tests.rs`, ignored for "R3g build":
`universal_variables_pair_by_position`,
`a_variable_of_an_outer_scope_pairs_in_its_scope`,
`a_failure_leaves_no_scope_and_a_restore_undoes_the_pairings`,
`a_known_binder_escapes_before_the_bodies`,
`a_free_universal_variable_is_refused`,
`the_first_free_universal_variable_is_found_in_order`,
`a_free_universal_variable_below_a_swapped_unify3_is_reversed`,
`a_clash_in_the_bodies_below_a_swapped_unify3_is_reversed`,
`the_types_that_hold_a_universal_variable_are_unified_not_gained`,
`universal_variables_at_ten_thousand`; in `differential.rs`:
`universal_variables_agree_on_fixed_cases`,
`univar_plan_agrees_on_generated_cases`. Ignored for "R3p build":
`packages_of_one_module_type_unify_name_by_name`,
`a_package_is_completed_from_the_other_module_type`,
`packages_of_ten_thousand_names_are_linear`. Each quotes the OCaml lines
it follows and names its witness.

**Open questions**, each with the answer recommended.

1. *Who builds `instance_poly`* (ctype.ml:1081-1095) and the lines of
   `copy_row` that only it reaches (decision 47)? Its callers are the
   typer's (a polymorphic record field, a method), not R3i or R3j.
   Recommended: a slice of its own designed with R3h in the next
   skeleton turn, built before R5.
2. *Partner nodes stay in the graph* after their scope is left: 16 bytes
   per bound variable per unification of two polymorphic types.
   Recommended: accept; a separate pool would need an undo log of its
   own. R5c measures it on a 3,735-module application.
3. *The explaining mode is not part of R3g's generated cases* because of
   the old checker's `occur_univar` (decision 49). Recommended: correct
   the old checker in a pull request of its own (the new variable at the
   generic level; `Tpoly (t, [])` against another type a clash), then add
   `EXPLAIN` to `univar_plan_agrees_on_generated_cases`.
4. *The levels of a package's completions* are the lower of the two
   nodes' levels (decision 52). Recommended: accept; R5a's tests judge.
5. *Nested scopes are quadratic*, as in OCaml. Recommended: accept: a
   binder nested in a binder is a method inside a polymorphic field, and
   the depth is the nesting of the source.

### 8.9 Pattern mode, equations, `reify` and `mcomp` (R3h)

What 8.6 decided for this slice: the harness and where the old checker
is a judge (decisions 61 and 62). This section is the design; decisions
63 to 71 of 8.6 are its numbered decisions, written here so that they
are read with their reasons. The work is cut in two slices, **R3h**
(state, equations, `reify`, the arms that need no backtrack) and
**R3r** (`mcomp`, the two arms that try and fall back; a slice name
has one letter, which the check of the ignored tests reads), built in
that order, each under 450 lines.

Rewritten in the seventh skeleton turn after the review of pull request
347 and a run of every test against a prototype of both slices.
Decisions 64, 67, 69 and 71 are rewritten in place and each says what
changed; 63, 68, 70 and the paragraph on `reify` are amended where
marked "(seventh turn)". Every range cited below was read from
compiler/ml/ctype.ml at this trunk, and the lines a decision turns on
are pasted.

**State.** Five things, all on `Checker`.

| state | where | written by | read by |
|---|---|---|---|
| `umode` | `Checker::umode` | `unify_pattern` (entry, exit) | `unify_expanded`, once a call |
| `generate_equations`, `assume_injective` | two bytes of `Checker` | `unify_pattern`; the `Flags` frame and the `Try` record put back what they found | unify3's pattern arms |
| newtype level | `Checker::newtype_level`, 0 outside | `unify_pattern` | `reify`, `add_gadt_equation` |
| assumed equalities | `Checker::pairs` (`PairSet`) | unify3 in pattern mode | `unify_expanded` in pattern mode |
| equations | `Checker::equations`, and the `TypeTable` row of each | `add_gadt_equation`, `cut_equations` | the row: `expand_once`; the length: `unify_pair`'s arm for two newtypes |

*The table of assumed equalities* (`unify_eq_set`,
compiler/ml/ctype.ml:2102-2104). Key: the two node indices of the pair,
the smaller first, in one `u64` (`order_type_pair`, ctype.ml:2104; the
kernel's index is OCaml's `id` for this purpose: a total order on
nodes). It is a hash set: pairs of nodes have no dense index. Size: 8
bytes a pair plus the set's control bytes; empty and unallocated for a
unit that never types a pattern. Cleared when `unify_pattern` returns,
on either result (ctype.ml:2746, 2749): `if !keys.is_empty() {
keys.clear() }`, which is one byte a bucket of the capacity the largest
pattern unification of the unit left. A pattern unification of 10,000
structure pairs costs 10,000 inserts and at most 20,000 lookups; the
next one, of one pair, costs one clear of that capacity (16 KiB of
control bytes written), and that is the only cost that outlives the
call. Never read or written in expression mode.

**63. `package_end` reads the right node as it does today.** In pattern
mode no structure node is linked, so the right node of a `PackageEnd`
frame is the node the frame was pushed with, and decision 55's argument
is not needed. In expression mode nothing changed. The one difference
of pattern mode for packages is the arm of `Not_found`
(ctype.ml:2417-2421): where `unify_package` answers a clash because a
completion was not `Completion::Type`, pattern mode reifies the types of
both lists, left list first, and succeeds (R3r). (Seventh turn) It has
a function: `Checker::package_fallback`, which the `PackageEnd` arm
calls where it answered a clash; in expression mode it answers the
clash, in pattern mode it reifies (ctype.ml:2416-2424; 2422 is
`List.iter (reify env) (tl1 @ tl2)`). No hand-built test reaches its
pattern branch: listed below.

**64. What replaces the link, per arm of unify3.** *What changed in the
seventh turn:* the sentence "the first three arms are as in expression
mode, the occurrence test of a variable included" was wrong for the
occurrence test (decision 69 says what runs); the table is read at two
places, not one; unify3's pattern branch is a function of its own; and
the explaining mode gets a frame for the pair. The rest stands.

`unify_expanded` loads `umode` once and passes `pattern: bool` to unify3
as a fourth argument (the load unify3 made moves; the count of loads of
a unification in expression mode does not change). In pattern mode
`unify_expanded` answers `Ok` when the pair is in the table, at the two
places OCaml reads it: for the pair as it is taken, before any
expansion (`if unify_eq t1 t2 then ()`, ctype.ml:2233), and for the two
expanded heads before unify3 (ctype.ml:2286); both through
`Checker::assumed_equal`, which is built, and neither in expression
mode. The two tests `unify_eq t1 t1'` and `unify_eq t2 t2'` that choose
the swapped call (ctype.ml:2299) stay tests of identity: a pair in the
table is two heads that were distinct when unify3 took them, and a node
and its own expanded head are never that (an expansion is made from the
node, after it stopped being a head). The first three arms of unify3 (a
variable on either side, two universal variables, two fields) run the
code of expression mode; the occurrence test inside the variable arms
is decision 69's. Then, with `pattern`, unify3 calls
`Checker::unify3_pattern` (cold, out of line, so that the pattern arms
add no code to unify3):

1. the pair `(t1', t2')` goes into the table (`| Pattern ->
   add_type_equality t1' t2'`, ctype.ml:2332). No occurrence test
   (decision 69), no link, no `Linked` frame, nothing in `saved`: a
   failure has nothing of this node to put back (`t1'.desc <- d1`,
   ctype.ml:2437, writes what is there). In `Mode::Explain` a
   `FrameKind::Assumed` frame is pushed where expression mode pushes
   `Linked`: it holds the pair for the trace of a failure below it and
   no descriptor (`explain_failure` reads it as it reads `Linked`);
   popped, it does nothing;
2. `create_recursion` is computed and its `Recursion` frame pushed as
   today (ctype.ml:2308, 2428-2436: the repair is outside the match on
   `umode`);
3. the arm, by the two heads, first that applies:

| heads | `generate` | what runs | part |
|---|---|---|---|
| arrow, arrow of one length | any | labels match when equal or when neither is optional (ctype.ml:2337-2343); the pairs of the parameters, then of the results | 1 |
| tuple, tuple | any | the pairs of the elements | 1 |
| constructor, constructor, one type | off | the pairs of the arguments | 1 |
| the same | on, `assume_injective` on | a `Flags` frame, the flags become (on, off), the pairs of the arguments above it (ctype.ml:2352-2354) | 1 |
| the same | on, injective off, the type's row has `LOCAL` or `DATATYPE` | the pairs of the arguments (ctype.ml:2354-2357; decision 66) | 1 |
| the same | on, otherwise | per argument, last first: when `TypeTable::injective` the pair; otherwise a `Try` frame (`TRY_ARGUMENT`; flags (off, off) while it is tried; fallback: reify both) (ctype.ml:2358-2375; 2373-2374 are the two `reify` calls) | 2 |
| nullary constructors of two types, both `instantiable` | on | `add_gadt_equation`: the source is the left type when its newtype level is greater (`find_newtype_level`, compared as pairs), otherwise the right one; the destination is the other side's head (ctype.ml:2376-2387) | 1 |
| nullary `instantiable` constructor, anything | on | `reify` of the right head, then `add_gadt_equation(left type, right head)` (ctype.ml:2388-2391) | 1 |
| anything, nullary `instantiable` constructor | on | `reify` of the left head, then `add_gadt_equation(right type, left head)` (ctype.ml:2392-2395) | 1 |
| a constructor on either side | any | `reify` of the left head, of the right head; with `generate` on, `mcomp` of the two (ctype.ml:2396-2400) | 1; `mcomp` 2 |
| object, object | any | `unify_fields` | 1 |
| variant, variant | any | a `Try` frame (`TRY_ROWS`; flags unchanged; fallback: reify both, and `mcomp` with `generate` on); started, it opens both rows and runs `unify_row` (ctype.ml:2402-2411; 2411 is the `mcomp` call; decision 68) | 2 |
| `nil`, `nil` | any | nothing | 1 |
| polymorphic types | any | as in expression mode | 1 |
| packages | any | `unify_package`; decision 63 | 1; the fallback 2 |
| anything else | any | a clash | 1 |

A `Flags` frame (`FrameKind::Flags`) holds in `extra` the two flags as
they were (bit 0 `generate_equations`, bit 1 `assume_injective`) and
puts them back when it is popped; a clash leaves them to the `Try`
record or to `unify_pattern`, which put back their own.

The rows are in OCaml's order; "left" and "right" are unify3's own
`t1'` and `t2'`, after the swap of unify2, so an equation's direction
does not depend on which side was expanded. Part 1 leaves
`todo!("R3r")` in the three places marked 2 and in `mcomp`.

An equation or a `reify` may clash (`add_gadt_equation` and `reify`
return `Result`): the clash is the arm's.

**65. The arm of `unify` for two locally abstract types**
(ctype.ml:2258-2270) is in `unify_pair`, after the arm for two nullary
constructors of one type, in every mode: when both heads are nullary
constructors (in registers), `equations` is not empty (one load, made
only for such a pair) and both rows are locally abstract types
(`flags & (NEWTYPE | DATATYPE | PRIVATE) == NEWTYPE`: `is_newtype`,
ctype.ml:1862-1868): `expand_once(·, ExpandMode::Unif)` of the right
node when the left type's newtype level is lower, otherwise of the left
node; when it answers `NONE` (`Cannot_expand`) the pair goes to
`unify_expanded` as it is; otherwise the pair of the unexpanded side and
the expansion is pushed with `push_pair` and the arm returns `Ok`: the
pushed pair is the nested `unify` of OCaml, with its own entry in the
trace. Cost for a unit without equations: one load for a pair of two
nullary constructors of different types, nothing for any other pair.
(Seventh turn) The arm is a function, `Checker::unify_newtypes`, called
from `unify_pair` BEFORE the arm for a universal variable and after the
arm for two nullary constructors of one type; the test that guards the
call is `l.head == CONSTR && r.head == CONSTR &&
!self.equations.is_empty()`: two heads in registers, then the one load.
OCaml's guard is `Env.has_local_constraints !env`, which is also true
when the environment holds only a type `reify` made or an existential
type: `Env.add_local_type` fills the map that `has_local_constraints`
tests (env.ml:1047, 1802-1803; ctype.ml:970, 1823). (Corrected in the
review of the seventh turn: this paragraph said those types are not
local constraints and that OCaml does not take the arm for them. OCaml
does take it.) The kernel's guard is narrower and gives the same
result: without an equation no locally abstract type has a manifest,
so `try_expand_once` raises `Cannot_expand` for either side and the
pair goes to `unify2` as it is (ctype.ml:2266-2269), which is what not
taking the arm does. Observed on the prototype
(`the_newer_of_two_locally_abstract_types_is_expanded_once`): with `n1
:= n0` then `n0 := int`, `n1` against `n0` expands `n1` once, and the
memo of the `n1` node is the `n0` node.

**66. Declaration facts.** Held today and read by this slice:
`NEWTYPE` and the `Newtype` row (`type_newtype_level`), `DATATYPE`
(`is_datatype`: a record, a variant or an open type), `ABBREV`,
`PRIVATE`, `ALIAS` (a manifest), `scope` (`Path.binding_time` for a
type that is not a newtype: `get_level`, ctype.ml:562-569, and
`find_newtype_level`, ctype.ml:2085-2091, read the same thing). Added:

- `LOCAL` (bit 7 of `TypeInfo::flags`): `in_current_module`. Set by
  the caller that owns the table (`TypeTable::set_local`; R5a), not by
  `from_segment`: a segment does not say whether it is the unit being
  checked. `TypeTable::non_aliasable` and `TypeTable::instantiable` are
  built and read it.
- `TypeTable::injective_bits: Vec<u32>`, indexed by type index, bit
  `i` the parameter `i` (`Variance.(mem Inj)` of `type_variance`).
  Empty, or shorter than the index, reads as not injective, which is
  what an abstract type without an annotation is (observed: `k`,
  decision 62). Read only by the last constructor arm, for a type that
  is neither `LOCAL` nor `DATATYPE`. A parameter past the 32nd reads as
  not injective. R5a fills it; the tests of R3h write it by hand.
- `expands_to_datatype` of `t1'`, `t1` and `t2` (ctype.ml:2356) is the
  `DATATYPE` flag of the row of the two heads' type: the heads are of
  one type, and `t1` and `t2` expand to them, so the three chains end
  at that row; a type on the way that is a data type with a manifest
  (`type t = M.t = A | B`) names the same constructors as its head.

`find_newtype_level(type_index)`: the `Newtype` row's `(level,
expansion_level)` with `NEWTYPE`, otherwise `(scope, scope)`.

**67. An equation.** *What changed in the seventh turn:* step 1 (the
sixth turn's rule refused every type that names its source and cited
the wrong lines), the order of the steps (the memos are cleaned before
the copy), what the `Newtype` row of the type becomes, and the return
types: both functions can clash. `add_gadt_equation(source,
destination) -> Result<(), Clash>` (ctype.ml:2093-2100):

1. `non_recursive_abbrev(source, destination) -> Result<bool, Clash>`.
   OCaml, ctype.ml:1503-1536, called with `strict = false`:

   ```text
   let rec local_non_recursive_abbrev strict visited env p ty =
     let ty = repr ty in
     if not (List.memq ty visited) then
       match ty.desc with
       | Tconstr (p', args, _abbrev) -> (
         if Path.same p p' then raise Occur;
         if (not strict) && is_contractive env p' then ()
         else
           let visited = ty :: visited in
           try
             (* try expanding, since [p] could be hidden *)
             local_non_recursive_abbrev strict visited env p
               (try_expand_head try_expand_once env ty)
           with Cannot_expand ->
             let params =
               try (Env.find_type p' env).type_params with Not_found -> args
             in
             List.iter2
               (fun tv ty ->
                 let strict = strict || not (is_Tvar (repr tv)) in
                 local_non_recursive_abbrev strict visited env p ty)
               params args)
       | _ ->
         if strict then
           (* PR#7374 *)
           let visited = ty :: visited in
           iter_type_expr (local_non_recursive_abbrev true visited env p) ty
   ```

   So: a constructor of `source` answers `Ok(false)`; a constructor of
   a contractive type (`TypeTable::contractive`: a data type, or a
   predefined type without a manifest, `is_contractive`,
   ctype.ml:1371-1375) is not entered while not strict; any other
   constructor is expanded (`expand_head(·, ExpandMode::Unif)`:
   `try_expand_head try_expand_once`, which may raise `Unify`, hence
   the `Result`) and the walk goes on in the expansion; one that does
   not expand has its arguments walked, strictly for an argument whose
   declared parameter is not a variable (`TypeTable::constrained`, a
   bit a parameter as `injective_bits`; a type without a row: strict
   when the ARGUMENT is not a variable, `with Not_found -> args`); a
   node that is not a constructor is entered only when strict. False:
   no equation, no clash. Seen with both compilers on source programs
   in the review (`Refl: eq<'a, 'a>` matched at `eq<a, T>`): `a := (a,
   int)`, `a := array<a>` and `a := box<a>` are ADDED; `a := M.t<a>`
   for an abstract `M.t` is refused. OCaml's `visited` is the list of
   the nodes on the path; the kernel uses two mark generations, one
   for "visited" and one for "visited strictly": a node is entered
   again only when it was visited not strictly and is now met
   strictly, so at most twice. This answers what OCaml answers: a node
   below itself is not entered again in either, and a node met a
   second time on another path answers what it answered (the walk has
   no state but `strict`). The stack is `Checker::frames` above its
   length (an expansion inside the walk lowers, and a lowering clears
   `g.work`), `extra` holding `strict`. O(nodes reached), two visits a
   node at most;
2. `cleanup_abbrev()`. OCaml calls it last (ctype.ml:2100, after
   `duplicate_type` and `Env.add_local_constraint`); `duplicate_type`
   is `Subst.type_expr`, which reads no memo, so the order makes no
   difference there. The kernel's copy does read the nullary memo, so
   the kernel cleans FIRST: the body must not link a nullary
   constructor to a node that was expanded before the equation;
3. `duplicate(destination)`: the generic copy (`duplicate_type`). Made
   from parts that exist: `g.speculate()`; with `g.level` 0,
   `generalize(destination)`, which makes every node of it generic;
   with `g.level` generic, `copy(destination)`; `g.level` put back;
   `g.restore(token)`. The copy's nodes are new and are not on the
   trail, so they stay; the destination has its levels again. Three
   passes over the destination, shared nodes once each (decision 76
   says what was observed and what differs);
4. a `Manifest` row `{ template: an empty template, params: 0, body:
   the copy }`. The body is a node of the graph, not a `RELATIVE`
   reference. `subst` knows an equation by the `NEWTYPE` flag of the
   row it has loaded (one test of a loaded byte for every other
   expansion): it memorizes FIRST, with the handle the copy is about to
   get (the next node), then copies the body at the node's level
   (`Checker::copy` with `g.level` the node's). Memorizing first is
   what makes the copy of a body that names the type itself (`a := (a,
   int)`) link to the node being expanded, as OCaml's `subst` does
   (`memorize_abbrev abbrev priv path ty body0` before the copy of the
   body, ctype.ml:1124);
5. `equations.push(Equation { type_index: source, previous: the row
   })`, then the row gets `ABBREV | NEWTYPE`, the manifest, and a NEW
   `Newtype` row `(the type's own level, newtype_level)`:
   `Env.add_local_constraint` (compiler/ml/env.ml:1805-1810) keeps the
   definition level and records the pattern's newtype level as the
   expansion level. The sixth turn said the `Newtype` row stays; it
   does not: `find_newtype_level` of a type with an equation answers
   the pair above (observed:
   `the_newer_of_two_locally_abstract_types_is_expanded_once` expects
   `((2, 3), (1, 4))`). The type is still a locally abstract type for
   decision 65 and no longer `instantiable`.

`cut_equations(len)` pops the entries above `len`, last first, writing
each `previous` row back, and calls `cleanup_abbrev()` when it popped
one. It is what a caller does where OCaml drops the environment of a
case (`set_state`, typecore.ml:1303-1305, and the end of a case). The
`Manifest` and `Newtype` rows and the copies are not reclaimed: 28
bytes and the body's nodes for every equation a unit ever adds. Nothing
of an equation is on the graph's trail: `Graph::restore` does not cut
equations, and a caller that restores a mark also cuts. Decision 68
says why the kernel's own backtrack must not. `size_of::<Equation>()`
is pinned at 20.

**`reify(ty) -> Result<(), Clash>`** (ctype.ml:1813-1859). The
signature changes: it can fail. A walk with a new mark generation and
`g.work`, children pushed so that they pop in `iter_type_expr`'s order
(the fresh names are numbered in visit order). Per representative not
yet marked:

- a variable: `fresh = locals.fresh_abstract(name)`; the `TypeTable`
  row of `fresh` is pushed (`rows.len()` must equal `fresh`: the
  supplier counts with the table) as abstract with `NEWTYPE` and a
  `Newtype` row of `(newtype_level, newtype_level)`, scope
  `newtype_level`; a constructor node of it at the variable's level;
  `g.link(variable, node)`; then, when the variable's level was below
  `newtype_level`, a clash whose trace pair in `Mode::Explain` is the
  new node and a new variable at the variable's level
  (ctype.ml:1837-1839). The link stays (decision 62);
- a variant: unless the row is static, for a fixed row the walk goes
  on into `more`; otherwise `more` is a variable (anything else is an
  invariant failure) and becomes, through `g.link`, a variant node at
  its level over a new `VariantRow` without tags, `fixed`, with the
  `closed` and the name of the row it replaces (`{r with row_fields =
  []; row_fixed = true; row_more = t}`, ctype.ml:1848-1850; corrected
  in the review of R3h: this said "not closed"), whose `more` is the
  fresh constructor made as above; then
  the write of `drop_name_children` without its frame
  (`forget_name_children`: the link stays when the unification fails,
  so nothing is to be put back) and the same level test. Then the
  row's children in `iter_row`'s order. (Seventh turn, observed:
  `rows_that_clash_are_reified_and_compared` expects the row variable
  a link to the FIXED variant node, whose `more` is the fresh
  constructor, not a link to the constructor);
- a constructor whose path is an object type (`is_object_type`): no
  kernel type has such a path; not built;
- anything else: its children.

No supplier (`locals` is `None`) and a variable to reify: a panic that
names `Checker::locals`; a caller that types a pattern installs one.

**68. The two arms that try** (the argument of a constructor that is
not injective, ctype.ml:2358-2375; two variants, ctype.ml:2402-2411)
are frames, not recursion. (Seventh turn: the mechanics below replace
the sixth turn's, which took the snapshot when the frame was PUSHED;
OCaml takes it when the argument is reached, after the arguments
before it were unified, and those must not be rolled back.)

A `FrameKind::Try` frame has two phases, told apart by two bits of
`extra`. PENDING (`TRY_ARGUMENT` or `TRY_ROWS`): pushed by the arm with
the two types. Popped pending (`Checker::try_frame`): the attempt
STARTS: a `Try` record (40 bytes, pinned) is pushed on `Checker::tries`
with `g.speculate()`, the index the frame is about to have, the lengths
of `trace`, `saved` and `scopes`, the two flags as they are, and bit 2
for rows; the frame is pushed again with the record's index as `extra`;
then, for an argument, both flags go off and the pair is pushed above
the frame; for rows, both are opened and `unify_row` runs. STARTED
(`extra` is a record index): popped, the attempt succeeded: the record
is popped, `g.keep`, the flags put back.

A clash: `unify_distinct` asks `!self.tries.is_empty()` on its failure
path only (the loop of `run_frames` is not touched and the success path
reads nothing new) and calls `Checker::recover_frames(base, pair)`,
which loops on `Checker::recover(base)`: no record whose frame is at or
above `base`: the clash is the caller's, as today. Otherwise the LAST
record is taken off (the only one read: one step a record, whatever
lies below in `frames`): `frames` is cut to its frame,
`Checker::restore` of its speculation, `scopes`, `trace` and `saved`
cut to its lengths (`scopes` by `truncate`: the scopes above are the
attempt's own; `leave_scopes` is not called), the flags put back; then
`reify(left)`, `reify(right)` and, with bit 2 and `generate_equations`
on, `mcomp(left, right)`. `Some(Ok(()))`: `Checker::resume_frames`
goes on with the frames above `base`, a second entry to the frame loop
that pops them arm for arm as `run_frames` does; a clash of the three,
or of what is resumed, is a new clash, recovered the same way.

In both modes of the graph: `Mode::Success` logs to the trail while a
speculation is open and stops when the last one is kept; `Mode::Explain`
has its own speculation below. The descriptors a `Linked` or `Fields`
frame above the `Try` frame would put back are put back by the restore.
What the backtrack does NOT undo, as in OCaml, where `env` is a
reference that `backtrack` does not know: an equation added inside the
attempt of two variants stays in `equations`, and so does a type
`reify` made. Only the graph goes back.

**69. `occur` in pattern mode.** *What changed in the seventh turn:*
the sixth turn said the two variable arms test occurrence "as in
expression mode". They do not. OCaml (ctype.ml:1467-1490, with
`occur_rec`, 1384-1408) runs `occur_full` with `allow_recursive` in
`Pattern`: a contractive constructor is not entered (1390), a
structure that is not a constructor is not entered (1404-1408), and an
object or a variant never is (1403). So in pattern mode a variable is
bound to a type that holds it below a tuple, where expression mode
clashes; it clashes through a constructor that is not contractive.

Where it is decided: `occur_expanding` is reached only after the
binding walk FOUND the variable (the success path of a binding never
calls it). It loads `umode` once at its top and, in pattern mode, goes
to `Checker::occur_pattern` (cold), which walks from the type as the
lines above say and answers whether the variable is reached. The
binding walk itself is unchanged in both modes, and the levels are
lowered everywhere, also below a structure the occurrence test does not
enter. A binding in expression mode pays: nothing when the variable
does not occur; one load of `umode` when it does (the path that is
about to clash or to expand). A type can be cyclic after a pattern
binding, as in OCaml; every walk of the kernel marks or carries a
visited set already, for recursive object and variant types.

A structure pair is not tested (`occur` is in the `Expression` branch,
ctype.ml:2329-2331): nothing is linked, so no cycle is made.
`add_gadt_equation` has its own test (step 1 of decision 67).

(Eighth turn; decision 84) `occur_full` wraps the walk in a loop
(ctype.ml:1470-1476):

```text
    while
      type_changed () := false;
      occur_rec env allow_recursive Type_set.empty ty0 ty;
      !(type_changed ())
    do
      () (* prerr_endline "changed" *)
    done;
```

The kernel has no such loop. `type_changed` is set only at the top of
`unify` (`type_changed () := true`, ctype.ml:2238); the walk reaches
it through an expansion that is not memorized (`subst`, 1129-1130), so
OCaml runs a second pass after such an expansion, which finds it
memorized and stops. Decision 84 says why the second pass answers as
the first; no case is known where it does not.

Test: `r3_tests::a_variable_is_bound_to_a_type_that_holds_it_below_a_
structure`: `'v` against `('v, int)` in pattern mode is a success and
the variable a link to the tuple; in expression mode a clash; `'v`
against `k<'v>`, `k` abstract and not contractive, a clash in both; the
levels below the tuple are lowered.

**70. `mcomp(left, right)`** (ctype.ml:1905-2009; the citations of
this decision were pasted from the file in the eighth turn: `mcomp`
1905-1965, `mcomp_list` 1967-1969, `mcomp_fields` 1971-1981,
`mcomp_row` 1983-2009, `mcomp_type_decl` from 2011). Never links, never
lowers; it expands (`expand_head(·, ExpandMode::Opt)`), which
memorizes. Its own table `Checker::compatible` (a second `PairSet`;
ORDERED pairs, `Type_pairs.find type_pairs (t1', t2')`), emptied when
it returns. (Seventh turn) Its stack is `Checker::frames` above the
length it finds, one `Pair` frame a pair, not `g.work`: an expansion
inside `mcomp` lowers, and a lowering clears `g.work`. Per pair, after
`repr`: one node, a variable on either side, or two nullary
constructors of one type: compatible. Otherwise both heads expanded;
one node or a pair in the table: compatible; else the pair is added
and, by the heads:

- arrows of one length whose labels match as in decision 64: the
  parameters and the results; tuples of one length: the elements;
- two constructors (`mcomp_type_decl`, ctype.ml:2011-2039): a type
  without a row: compatible. One type: the pairs of the arguments
  whose parameter is `TypeTable::injective`. Two types, both
  `non_aliasable`: a clash. Otherwise by the two rows: both
  `DATATYPE`: the pairs of the arguments (a clash when the lists
  differ in length), then `LocalDecls::compare`, which pushes the
  pairs of the member types with `push_compatible` or answers
  `DeclMatch::Clash`; neither `DATATYPE`: compatible; one `DATATYPE`
  and the other not `non_aliasable`: compatible; else a clash;
- a constructor against anything else: a clash when its row is
  `non_aliasable` or `DATATYPE`, else compatible;
- packages, `nil`: compatible. Objects: `mcomp_fields`
  (ctype.ml:1971-1981) over `flatten_fields` and the merge
  `unify_fields` uses. Variants: `mcomp_row` (ctype.ml:1983-2009) over
  `flatten_row` and `merge_rows`, the table of ctype.ml:1996-2008;
- polymorphic types without variables: the bodies. With variables:
  `enter_poly(left, right)`, which pushes a `LeavePoly` frame and the
  pair of the bodies on `frames`, the stack `mcomp` runs on: the pair
  is taken as any pair, and the `LeavePoly` frame, when it is popped,
  cuts `Checker::scopes` to the length the frame holds
  (`scopes.truncate`). (Seventh turn: `leave_scopes` is private to
  unify.rs and looks for its frame in `frames[base..]` of a
  unification; `mcomp` does not call it. It needs `Checker::scopes`,
  `Checker::frames` and `FrameKind::LeavePoly`, all public.) A clash
  cuts `frames` and `scopes` to the lengths `mcomp` found. Two
  universal variables: `unify_univar`;
- anything else: a clash. A clash has no trace pair (`Unify []`).

**No supplier.** `Checker::locals` is `None` and two different data
types meet: a clash, as decision 52 answers for packages: the kernel
has no declaration to compare and must not accept a pattern on a
guess. R5a installs a supplier before it types a pattern, so the
answer is reached only by a test.

**71. What a unit that never types a pattern pays.** *What changed in
the seventh turn:* the sixth turn left out the hash state, the growth
of `Checker` and the compares of decision 60, and its list of reads is
checked here against the skeleton as it stands.

Reads added to expression mode, per place:

- `unify_expanded`: one load of `umode` at its top, per call, and two
  branches on the register it is in; unify3: one branch on that
  register. (Corrected in the review of the seventh turn: this line
  said "none". In the sixth turn's code the load was in unify3, after
  the arms for a variable, a universal variable and a pair of fields;
  a pair that ends in one of those arms, or before unify3, now pays
  one byte load it did not pay. `assumed_equal` is out of line and
  `#[cold]`, which keeps expression mode's code as it was and costs
  pattern mode a call a pair. Both are measured at R5c with the other
  reads of this decision.)
- the `PackageEnd` frame, on its failure path: one load of `umode` in
  `package_fallback`;
- `unify_pair`: one load of `equations.len()` for a pair of two heads
  that are both plain constructors (`l.head == CONSTR && r.head ==
  CONSTR`: nullary, not extended) of different types; nothing for any
  other pair. (As built by R3h: the arm tests the two tags, the two
  arities and then the type, where it tested the type before the
  arities; the registers and the loads are the same, the order of the
  compares is not.) Under an equation, in the body of a case, two
  locally abstract types of different names pay one byte load of
  `umode` more in `unify_newtypes`, for the table of assumed pairs
  that OCaml's `unify_eq` reads first (ctype.ml:2233); a unit without
  an equation never reaches it;
- `occur_expanding`: one load of `umode` when a binding walk found the
  variable (decision 69);
- `subst`: one test of the `NEWTYPE` bit of the row it has loaded
  (R3h builds it, with the call of `unify_newtypes` in `unify_pair`:
  neither is in the skeleton);
- `unify_distinct`: on the failure path, one load of `tries.len()`;
  nothing on the success path, and nothing in the loop of
  `run_frames`;
- `unify_row`: two compares for each row that is not fixed (`fixed`,
  and "has a name with arguments"), on the `VariantRow` it has loaded:
  the two compares of decision 60, per pair of rows four at most; and
  for a row 1 that has a name with arguments and no `last1`, one load
  of the left node's head;
- `copy_refs`: for a copied row that is fixed, one pass over its
  fields (`match_fixed_fields`); for one that is not, one compare; and
  for every copied row one load of the node of `more` and a test of
  its tag (a row over a constructor is copied as a fixed one, PR#6163,
  ctype.ml:826-830; added in the review);
- `lower_scoped` (a unit with a scoped type only): decision 75.

Memory. The hasher of both sets is `fast_hash::FastState`, a zero-sized
type keyed from fixed seeds: `Checker::new` makes no hash state, reads
no random source, and an empty set allocates nothing. `Checker` is
1,176 bytes on a 64-bit target, of which pattern mode is 136: two
`PairSet` of 32 bytes, `equations` and `tries` of 24 each, `locals` of
16, `newtype_level` of 4, the two flags and `umode` of one byte each
(with padding). `TypeTable` holds `injective_bits` and
`constrained_bits`, 24 bytes each, empty. `TypeInfo` did not grow:
`PREDEF` is bit 0 of its byte `reserved`. The benchmark operations of
TC_KERNEL_R3.md are reported before and after by each slice; no target
is set (decision 46).

**Step tests** (relations, 1,000 against 10,000; tc/r3_tests.rs). Each
was run against the prototype and then run again with the structure it
is there for broken; the last column is what was seen.

| Test | Slice | Relation | Broken, it |
|---|---|---|---|
| `pattern_mode_at_ten_thousand` | R3h | n nested tuples against their copy in pattern mode: linear, no node a link, the table empty afterwards; `reify` of n variables each named twice: n types; `reify` of a chain of n tuples each naming the one below twice: one type, linear; n equations added and cut: linear, every row its `previous` | with the marks of `reify` off: did not finish (the chain has 2^n paths; stopped after 3 minutes). The chain was added in this turn: without it the test passed with the marks off |
| `an_equation_over_ten_thousand_shared_nodes_is_linear` | R3h | `non_recursive_abbrev` and `duplicate` of a chain of n `k2<t, t>` nodes, strict and not, with and without the source at the bottom: both linear, n + 1 nodes made, every level what it was | with the marks of `non_recursive_abbrev` off: did not finish (stopped after 5 minutes). `duplicate` without sharing would make 2^n nodes; the test pins n + 1 |
| `mcomp_at_ten_thousand` | R3r | two tuples of width n naming one chain node n times: linear | with the table lookup off: failed its relation (width n was the review's correction 6; at width 100 it held without the table) |
| `recovering_ten_thousand_attempts_is_linear` | R3r | n arguments that are not injective, each failing and falling back, n - 1 pairs pending below: linear | with `recover` reading the frames from the base to its frame: failed its relation. A first break, reading every record of `tries`, did NOT fail it (one record is open at a time), which is why the relation is stated over the frames below |

**The parts.**

- **R3h**: `Checker::match_unmatched` (the fixed-row rule of
  `copy_refs`, decision 47's last paragraph: `copy_refs` and
  `match_fixed_fields` are built and find the field);
  `Checker::{find_newtype_level, non_recursive_abbrev, duplicate,
  add_gadt_equation, fresh_abstract, below_newtype_level, reify}`
  (rows.rs); the equation arm of `subst` (expand.rs);
  `Checker::{unify_pattern, cut_equations, unify_newtypes,
  occur_pattern, unify3_pattern}` and the call of `unify_newtypes` in
  `unify_pair` (unify.rs). Tests: the twelve ignored for "R3h build".
- **R3r**: `Checker::{mcomp, push_compatible, package_fallback}`
  (rows.rs); `Checker::{try_frame, recover, recover_frames,
  resume_frames}` and the places R3h left `todo!("R3r")` in
  `unify3_pattern` (unify.rs). Tests: the seven ignored for "R3r
  build".

**What the prototype corrected.** Both slices were written as bodies in
the working copy (about 1,090 lines, not committed) and the nineteen
tests run. Every test passed in the end; these are the ones that did
not at first, and why.

| Test | First result | Cause | What changed |
|---|---|---|---|
| `a_recursive_equation_is_not_added` | failed | the test and decision 67 were not what OCaml does (review, correction 1) | replaced by `an_equation_names_its_type_only_below_a_structure_or_a_contractive_type`, ten cases; decision 67 step 1 |
| `the_newer_of_two_locally_abstract_types_is_expanded_once` | failed | the test expected the `Newtype` row of a type with an equation to stay, and the memo of `n0` to hold an entry: `Env.add_local_constraint` writes `(level, newtype_level)`, and a nullary copy links to the node expanded before | the test; decision 67 step 5 |
| `rows_that_clash_are_reified_and_compared` | failed | the test expected the row variable a link to the fresh constructor; `reify` links it to a fixed variant node over it (ctype.ml:1848-1853) | the test asserts the shape `[fixed \| t]` and the path of `more` |
| `an_argument_that_is_not_injective_is_tried_and_then_reified` | passed for the wrong reason | its failing attempt failed before anything was bound, so a snapshot taken too early could not show | the attempt binds `'v` and then fails at two tuples of different lengths; a second case over `k2` shows the first argument kept and the second rolled back; decision 68 (two phases) |
| `two_structures_are_assumed_equal_and_not_linked` | passed, but reached `mcomp` (R3r) in its clash case, `int` against `string` | found by running the R3h tests with only R3h's bodies present: eleven of twelve passed | the clash is two tuples of different lengths; then the twelve pass with R3r's bodies `todo!` and exactly the six R3r tests of `r3_tests.rs` fail |
| `mcomp_at_ten_thousand` | passed without the table | width 100 | width n |
| `pattern_mode_at_ten_thousand` | passed without the marks of `reify` | no shared structure | the shared chain |
| `a_named_row_on_the_left_loses_its_arguments_in_pattern_mode` | failed on the shape | in pattern mode the left node keeps its own tag first (`A B`), in expression mode the right node is read (`B A`) | the test; decision 60 |
| `pattern_plan_agrees_on_generated_cases` | differed on 56 seeds, then on 8, then on the listed ones | the old side's `nil` (decision 77); a fixed copy with an unmatched field panicked in `copy_refs` (decision 47's rule, now built to the call); a failed case kept its equations (decision 80); a lowering with scopes (decision 80); tracing (decision 79) | the harness, `copy_refs`, the two lists of seeds |

The other eleven passed as written (eight of the sixth turn, some with
a cited range corrected, and three written in this turn).

**Arms no hand-built test reaches**: the object-type arm of `reify`
(not built); the pattern branch of `package_fallback` (a package pair
whose completion is not a type, in pattern mode); `mcomp` of two fields
(`Tfield _, Tfield _`, "actually unused" in OCaml), of two objects, of
two packages and of two polymorphic types with variables (the
`LeavePoly` cut); a parameter past the 32nd of `injective_bits` and of
`constrained_bits`; `LocalDecls::compare` answering `Members` for two
open types; `match_unmatched` for a field whose reference is shared
with a row outside the copy (the generated cases reach the other two
branches; `no_generated_case_has_a_fixed_row_with_an_unmatched_field`
is a test of expression plans and stays as it is);
`non_recursive_abbrev` where the expansion clashes (`Err`); `recover`
where `reify` or `mcomp` of the fallback clashes and an outer record
takes the clash; `resume_frames` for the frame kinds a pattern arm
never leaves below an attempt (`Recursion`, `Fields`).

**The open questions of the sixth turn** are answered: decisions 72 to
76 of 8.6.

**The corrections owed after the review of pull request 347**, and
where each went: 1 (`non_recursive_abbrev`): decision 67 step 1 and
`an_equation_names_its_type_only_below_a_structure_or_a_contractive_
type`; 2 (the binding walk in pattern mode): decision 69 and
`a_variable_is_bound_to_a_type_that_holds_it_below_a_structure`; 3
(the home of row 1): decision 60 of 8.6 and
`a_named_row_on_the_left_loses_its_arguments_in_pattern_mode`; 4:
`size_of` tests in rows.rs (`Equation`, 20) and unify.rs (`Try`, 40);
5 (the scopes under `mcomp`): decision 70; 6: `mcomp_at_ten_thousand`
at width n; 7: `an_equation_over_ten_thousand_shared_nodes_is_linear`
and `recovering_ten_thousand_attempts_is_linear`; 8 (ranges): the table
of decision 64 and the doc comments, each read from the file; 9:
decision 71, the cost paragraph of `unify_row`, and the two prompts in
8.4.

R3q (`instance_poly`, `instance_label`) is section 8.10; the ambiguity
of GADT instances (R3s) is section 8.11.

**Corrections after the review of the seventh turn.** Made in place by
the reviewer: 1 to 4. Owed by the next design turn, which makes the
skeletons of R3q and R3s: 5 to 10. The state of each item after the
eighth skeleton turn is the line "State:" below it.

1. Decision 65 said the types `reify` makes are not local constraints.
   They are. The arm's guard is right for another reason, now given
   there.
2. Decision 71 said `unify_expanded` and unify3 pay nothing new. They
   pay one byte load a call; the list also lacked the load of
   `package_fallback` and the tag test of `more` in `copy_refs`.
3. The size of R3h was set at 450 lines on paper. By the markers of the
   prototype its part is about 630 (the bodies 455, the pattern arm of
   unify3 123, the occurrence walk 35, the arm of `subst` 10, the call
   in `unify_pair` 5); the limit is 700. R3r's part is about 410 and
   its 450 stands.
4. The prompt of R3h said nothing of three things, and now does: the
   builder may read the prototype; the prototype's `occur_pattern`
   recurses, so the walk on `Checker::frames` the prompt asks for was
   never run; `match_unmatched` and `occur_pattern` had no step test,
   and the builder adds them.
   State of 1 to 4: paid by the reviewer commit of pull request 354
   and by R3h (pull request 356).
5. `copy_refs` treats a row over a constructor as a fixed one (PR#6163,
   ctype.ml:826-830). That is OCaml's rule and it is built code, but it
   widens what reaches `match_unmatched` beyond the argument of
   decision 47, and the scanner of
   `no_generated_case_has_a_fixed_row_with_an_unmatched_field` reads
   the printed `fixed` only: it does not watch such a row. Nothing that
   runs reaches it. R3h builds the body with a test of such a row; the
   scanner is widened or the decision says why it need not be.
   State: paid in the eighth turn (G1 (d)): the scanner is widened.
   It now finds a row over a constructor with an unmatched field,
   whether the tail is printed in full or as a reference to a node
   printed before; checked on four hand-written forms; none of the
   4,000 cases of the two plans without patterns has one. (A plan with
   patterns reaches `match_unmatched` on purpose, since R3h.)
6. Step tests are missing for three loops that are built:
   `lower_row_name`, `unname_row` and `match_fixed_fields`. For
   `lower_row_name` the cost line is also short of the truth: a chain
   of n variant nodes whose name does not escape is walked to its end
   from each of its nodes that `lower_scoped` visits, n squared over
   two loads the first time the chain is lowered. `update_level` does
   not visit the inner nodes of a chain (`iter_row` walks a `more` that
   is a variant in line, btype.ml:229-241). Decide with a step test at
   1,000 and 10,000: skip the inner nodes, or bound the chain.
   State: paid in the eighth turn (G1 (c)); decision 89 of 8.6. The
   inner nodes are skipped as OCaml skips them. Tests in `rows.rs`:
   `lowering_a_chain_of_ten_thousand_rows_is_linear` (`lower_row_name`
   with and without a name, and `unname_row` when the name escapes)
   and `matching_the_fields_of_a_fixed_row_is_one_step_a_field`.
7. Section 8.11 turns tracing on when `equations` is not empty. OCaml
   turns it on when the environment has a local constraint
   (`check_trace_gadt_instances`, ctype.ml:178-184), and the types of
   `reify` and the existential types are local constraints (item 1).
   The narrower test needs its own argument (only an equation has an
   expansion level, ctype.ml:1220-1227; what `cleanup_abbrev` and a
   nullary constructor's own memo, 200-202, can show without one), or
   OCaml's test is taken. 8.11 also leaves out: that a set gets its
   first member only from an expansion under tracing; that
   `try_expand_head` adds the chain whatever the tracing flag when the
   environment has an instance scope (1271-1276); the wrapper
   `expand_head_trace` (2781-2784); an equation whose level has no
   instance scope.
   State: paid as text in the eighth turn: 8.11 is rewritten in place,
   (i) to (v), each with the lines pasted; decisions 97 to 104. The
   skeleton of R3s is still owed (8.11, its first paragraph).
8. Decision 69 does not mention the `type_changed` loop of
   `occur_full` (ctype.ml:1470-1476): say why the kernel needs none,
   or build it.
   State: paid in the eighth turn, by decision 84 of 8.6 and the
   paragraph added to decision 69: not built; the walk can reach
   `unify` through an expansion, and why the second pass answers as
   the first is argued there, without a case.
9. Decisions 64 and 70 were not compared with OCaml arm by arm in
   either review. Their evidence is the hand-built tests and the run
   of the prototype; the builders stop and report where a test and the
   cited lines disagree.
   State: paid by the final reviews of pull requests 356 (decision 64
   against ctype.ml 2333-2425) and 361 (decision 70 against
   1905-2039); decision 83 of 8.6.
10. Citations: `link_type rm ty` is ctype.ml:2619, not 2616 (decision
    60 and the comment in `unify_row`); `has_cached_expansion` is 2254,
    not 2251 (8.11); the ranges of `mcomp_fields` and `mcomp_row` in
    decision 70 are two lines off. Decision 80 (b) holds for every plan
    without `SCOPED`, not only under `PATTERN` (for a plan without
    scoped types `Checker::lower` is `Graph::lower`, so nothing
    changed there).
    State: paid in the eighth turn (G1 (f)). Each range was pasted
    from the file: `link_type rm ty` is ctype.ml:2619 and `set_more`
    2597-2619 (decision 60, the comment in `unify_row`, the doc of
    `set_more` and three tests); `has_cached_expansion` is called at
    2254 (the comment in `unify_pair`; 8.11 is rewritten in this
    turn); `mcomp` 1905-1965, `mcomp_fields` 1971-1981, `mcomp_row`
    1983-2009 with its table at 1996-2008 (decision 70 and the doc
    comments of the three functions); decision 80 (b).

**Corrections after the review of R3h** (pull request 356). Item 1 is
decided here and built by R3r; 2 to 4 and 6 are owed by the next
design turn; 5 records what the builder changed in the skeleton's
words.

1. `duplicate` is total. As built it is `Graph::generalize` at level 0
   and a copy, and `Graph::generalize` stops at a node that is generic
   already without looking below it: a destination with a generic node
   above one that is not gives a body that shares the lower node with
   its destination. OCaml's `duplicate_type` copies every node
   whatever its level (`Subst.typexp`: `| _ ->` makes a stub with
   `newgenvar` and copies, compiler/ml/subst.ml:144-158). The operands
   typing gives a pattern unification are instances, which have no
   generic node, so no program is known to reach it; the differential
   plans can (a generalized operand given to `Op::Gadt`). Decided: the
   pass that makes the destination generic goes through generic nodes
   (a walk in `rows.rs` with marks; the cost stays three passes over
   the destination). It is the first commit of R3r, with a hand-built
   destination that fails without it.
   State: paid by R3r (pull request 361, its first commit;
   `r3_tests::duplicate_copies_below_a_generic_node`); decision 82.
2. `occur_pattern` remembers what it decided for a constructor across
   the paths of one walk, where OCaml's `visited` is the set of the
   path (ctype.ml:1393-1394). On a graph without a cycle the two agree.
   A cycle is made only below a structure or a contractive constructor,
   which the walk does not enter, or through a constructor whose
   expansion drops the argument; for that one the on-path visit tests
   the expansion at once and the off-path visit tests the arguments
   and then the expansion, and what an expansion reaches of an
   argument it reaches through the argument whole. Write that argument
   out with a hand-built cyclic case, or keep the set per path. The
   `type_changed` loop (item 8 above) needs nothing: its flag is set
   only at the top of `unify` (ctype.ml:2238), which the walk does not
   call.
   State: paid in the eighth turn (G1 (b)): the set is kept per path
   where it matters. The argument above does not hold: a hand-built
   case differs (`e<'x> = int`, `c = k<e<x>>`, `x = k2<c, ('u, int)>`,
   `'u` against `k2<c, x>`: OCaml binds, the walk as built clashed,
   because it remembered "`x` holds it" from a path on which `c` was
   on the way). Now an answer is remembered across paths only for a
   constructor whose visit met no constructor on the way; below one
   that was met the walk is OCaml's, once per path. Test:
   `r3_tests::the_occurrence_test_of_pattern_mode_keeps_its_set_per_
   path`, seen to fail on the walk as built; the depth test at 100,000
   holds. STILL OWED, found while writing it: the walk tests the
   expansion of a constructor while that constructor's own frame is
   on the stack and its mark says "on the way"; OCaml's handler tests
   the expansion with the OUTER set, without the constructor
   (`occur_rec env allow_recursive visited ty0 ty'`, ctype.ml:1401,
   where `visited` is the function's argument, not the set extended
   at 1394). The two differ only when the expansion reaches the
   constructor's own node again; no case was built. The sentence about `type_changed` is corrected by
   decision 84: the walk does reach `unify`, through an expansion.
3. `local_non_recursive_abbrev` runs under `wrap_trace_gadt_instances`
   (ctype.ml:1534). `non_recursive_abbrev` does not trace: R3s (item 7
   above names the wrappers 8.11 leaves out; this is the fourth).
   State: paid as text in the eighth turn: 8.11, (iv), and the table
   of decision 99: `non_recursive_abbrev` turns tracing on at its
   entry. Built by R3s.
4. Decision 65 writes the guard of the arm as `l.head == CONSTR &&
   r.head == CONSTR`; the arm as built tests tags and arities
   (decision 71, corrected above). One of the two texts is made the
   other's at R5c, when the arm is measured.
   State: recorded in the eighth turn (G1 (f)); R5c settles it. The
   two texts, pasted: decision 65 has `l.head == CONSTR && r.head ==
   CONSTR && !self.equations.is_empty()`; `unify_pair` as built has
   `l.tag() == CONSTR && r.tag() == CONSTR && l.arity() == 0 &&
   r.arity() == 0`, then the arm of one type (`l.a == r.a`), then
   `!self.equations.is_empty()` and the call. They differ in one
   thing: `head == CONSTR` is also false for a nullary constructor
   node with a flag bit set in its head (bits 4 to 8), which the
   tag-and-arity form accepts. What R5c must measure and decide: (1)
   whether any nullary constructor node of a checked unit carries a
   head flag (if one can, the one-compare form is wrong and the text
   of decision 65 is made the code's); (2) if none can, the
   instructions of the five unification operations of `tc_kernel`
   with each form of the guard, and the cheaper form is made both
   texts; (3) the one load of `equations.len()` for a pair of two
   nullary constructors of different types on the application, with
   the byte load of `umode` in `unify_expanded` (decision 71).
5. Doc comments of the skeleton the builder changed, each read and
   accepted: `match_unmatched` (a shared chain longer than one node is
   copied from its first shared node, so that no slot of the source's
   chain is written: the prototype wrote one); `reify` (a row over a
   constructor is read as a fixed one, as `copy_refs` reads it: OCaml's
   copy has set the flag on such a row, and where no copy made it OCaml
   stops at `assert false`, ctype.ml:1854); `subst` (a cost sentence
   for the arm of an equation: the cost of the copy of the body);
   `push_children` (`#[inline(always)]`, kept by measurement: out of
   line it cost `unify_ground3` and `unify_datatype2` 28 instructions
   an operation).
   State: a record; nothing owed.
6. Owed by the next design turn, found in the final review:
   `non_recursive_abbrev` enters a constructor again when it meets it
   strictly after a visit that was not strict, also when the first
   visit is still on the path. OCaml's `visited` is the list of the
   path and holds a node whatever the strictness it was met with
   (`List.memq ty visited`, ctype.ml:1505, 1511): the second meeting
   is skipped. The two differ only on a type that reaches itself: a
   constructor `c` that is not contractive, with a first parameter
   that is not constrained and a second that is, whose node is `c<(p),
   (itself)>` and `p` the source: OCaml's walk does not enter the
   first tuple (not strict) and skips the node below the second, and
   answers "not recursive"; the walk as built enters the node again
   strictly and finds `p`. Pattern mode alone makes such a type. Build
   the case by hand and follow OCaml (a mark for "on the path", taken
   off when the node's frame is left), or say why the kernel's answer
   is kept.
   State: paid in the eighth turn (G1 (a)). OCaml is followed: a mark
   for "on the way" in three kinds (entered strictly, entered
   otherwise, entered otherwise and met again strictly), taken off by a
   LEAVE entry of the stack. The review's remedy alone was not enough:
   a node left below a node that was on the way, entered otherwise and
   met strictly, must not be remembered as done, or a later path that
   no longer holds that node skips what OCaml enters. Test:
   `r3_tests::a_type_on_the_way_is_skipped_whatever_its_strictness`,
   two witnesses (`y = k2<(n0, int), (y)>`: "not recursive"; `r =
   k2<y, x>` with `x = (y)`: "recursive"), the first seen to fail on
   the walk as built (it answered "recursive"), the second seen to
   fail with the on-the-way mark alone (it answered "not recursive").
   The step test at 1,000 and 10,000 holds
   (`an_equation_over_ten_thousand_shared_nodes_is_linear`). No source
   program was found for either witness.

### 8.10 `instance_poly` and `instance_label` (R3q)

Designed as text in the seventh skeleton turn; read against the source
and corrected in place in the eighth, which also made the skeleton
(`src/tc/rows.rs`, twelve bodies `todo!("R3q")`), ten acceptance tests
(`src/tc/r3_tests.rs`, `#[ignore = "R3q build"]`) and the build prompt
(8.4), and ran every test against a prototype of the bodies (429 lines,
posted as a comment on the pull request of the eighth turn; not in the
tree). The decisions are 91 to 96 of 8.6. What the seventh turn's text
had wrong is listed at the end of this section.

**What OCaml does** (compiler/ml/ctype.ml:1033-1106, pasted from the
file). `instance_poly ~fixed univars sch` makes one new variable for
each universal variable of `univars` (named when `keep_names`), and
copies `sch` with `copy_sep`:

```text
let rec copy_sep fixed free bound visited ty =
  let ty = repr ty in
  let univars = free ty in
  if Type_set.is_empty univars then (
    if ty.level <> generic_level then ty
    else
      let t = newvar () in
      delayed_copy () := lazy (t.desc <- Tlink (copy ty)) :: !(delayed_copy ());
      t)
  else
    try
      let t, bound_t = List.assq ty visited in
      let dl = if is_Tunivar ty then [] else diff_list bound bound_t in
      if dl <> [] && conflicts univars dl then raise Not_found;
      t
    with Not_found ->
      let t = newvar () in
      (* Stub *)
      let visited =
        match ty.desc with
        | Tarrow _ | Ttuple _ | Tvariant _ | Tconstr _ | Tobject _ | Tpackage _
          ->
          (ty, (t, bound)) :: visited
        | _ -> visited
      in
      let copy_rec = copy_sep fixed free bound visited in
      t.desc <-
        (match ty.desc with
        | Tvariant row0 ->
          let row = row_repr row0 in
          let more = repr row.row_more in
          (* We shall really check the level on the row variable *)
          let keep = is_Tvar more && more.level <> generic_level in
          let more' = copy_rec more in
          let fixed' = fixed && is_Tvar (repr more') in
          let row = copy_row copy_rec fixed' row keep more' in
          Tvariant row
        | Tpoly (t1, tl) ->
          let tl = List.map repr tl in
          let tl' = List.map (fun t -> newty t.desc) tl in
          let bound = tl @ bound in
          let visited =
            List.map2 (fun ty t -> (ty, (t, bound))) tl tl' @ visited
          in
          Tpoly (copy_sep fixed free bound visited t1, tl')
        | _ -> copy_type_desc copy_rec ty.desc);
      t
```

1. *`free ty`* (`compute_univars sch`, 693-713) is the set of universal
   variables FREE below `ty`: the propagation up the inverse graph
   stops at the polymorphic type that binds the variable (699). A node
   with none is `copy`'s business: it is returned as it is when it is
   not generic, and otherwise a new variable stands for it that is
   made a link to its copy AFTER the walk (`delayed_copy`, 1040, 1093),
   all in one copy session, so the parts without a universal variable
   keep their sharing among themselves.
2. *A node with a free universal variable is copied whatever its
   level, and it is NOT shared between two places.* `visited` is an
   argument of the function: what the walk of one child adds, its
   sibling does not see. It holds the nodes ON THE WAY from the root
   (and the bound variables with their copies), so it only closes a
   type that reaches itself. A node reached by two paths is copied
   twice ("Copy without sharing until there are no free univars left",
   1030).
3. *A node on the way that is met again* is its copy, unless a
   variable bound since it was entered is free in it (`conflicts`,
   1023-1025): then it is copied again with the new binding. A universal
   variable is always its pair's copy.
4. *A polymorphic type* gets new universal variables for its own
   (`newty t.desc`), which are bound for its body. It is not put in
   `visited`, and neither is a field.
5. *A variant* is copied as ONE row (`row_repr`), by `copy_row` with
   `fixed' = fixed && is_Tvar (repr more')` and `keep = is_Tvar more &&
   more.level <> generic_level`: the fixed-row rule only this slice
   reaches (btype.ml:375, 389; decision 47).

`instance_label fixed lbl` (1097-1105) is one copy session over the
label's record type (`copy`, first) and its argument: `instance_poly
~fixed tl ty` when the argument is a polymorphic type, else `copy`.
Every caller of `instance_poly` passes the two parts of one `Tpoly`
(typecore.ml 1430, 2554, 4289, 4986, 5098; typedecl.ml 819, 1049).

**The kernel's form** (decisions 91 to 96; the doc comments in
`rows.rs` are the specification, this is the map).

- `Checker::instance_poly(fixed, keep_names, poly, vars) -> Ty` takes
  the polymorphic type node; `Checker::instance_label(fixed, argument,
  result, vars) -> (Ty, Ty)`. A label whose argument is not a
  polymorphic type is a plain copy session of two roots and touches no
  table of this slice.
- *Whether a universal variable is free below a node*
  (`Checker::mark_holders`) is OCaml's algorithm with dense tables: one
  walk that builds the inverse graph as a pool of edges, then a
  propagation one class of variables at a time (the bound variables of
  the type, then those of each polymorphic type inside), each stopped
  at its own binder. The answer is one stamp in a 16-byte row a node
  (`PolySlot`). OCaml keeps the SET a node; the kernel keeps "not
  empty", which is all the copy reads, and asks the one question that
  needs the set (`conflicts`) by a walk of its own when it arises.
- *The copy* (`Checker::copy_sep`, `sep_child`, `sep_fill`) is a walk
  on `Checker::frames`: a child that holds no universal variable is
  shared or gets a stub that is listed for the session; a child that
  holds one gets a stub and a frame, and is filled when the frame is
  taken off. A node being filled puts its copy in its `PolySlot` and a
  frame below its children takes it off again: the slot is OCaml's
  `visited`, read with one load where OCaml reads a list.
- *The delayed copies* (`Checker::poly_session`) are ONE session after
  the walk: `Graph::copy_begin`, a `copy_ref` a root, `Graph::copy_
  drain`, then the pass every copy runs (`Checker::memorized_node` a
  node). The stubs become links, as in OCaml.
- *A row* (`Checker::copy_sep_row`) is copied flat, read through its
  chain without opening it; without `keep` the copy is an unopened
  node, with `keep` it is built opened onto the references of its
  source.
- *The cells of copied fields* are duplicated by `Checker::dup_cell`
  after the session's pass and inside its cell session.

**Cost.** Nothing for a unit that never calls either. `instance` and
`copy` are not changed (`Graph::copy` is `copy_begin`, `copy_ref`,
`copy_drain`, the same code in three functions; the pass of
`link_memorized` calls `memorized_node`, its own loop body). The five
unification operations and the copy and instance operations of
`tc_kernel` were measured before and after the refactor: see the pull
request. `instance_poly`: linear in the nodes below the body when no
node that holds a universal variable is reached by two paths (as
OCaml, a node that is is copied once a path), plus, with polymorphic
types inside each other, one step a node for each class free below it.

**The old side** (types/ctype.rs, `instance_poly`, `instance_label`,
`copy_sep_inner`, `compute_univars_per_node`) is a line-by-line port of
the OCaml above, with `visited` a slice and the univars a hash map a
node; pull request 302 made `instance_label` one copy session for the
label's type and its record type. It is a judge of this slice. The
harness has NO operation for it yet (8.10 of the seventh turn asked
for `Op::InstancePoly`): the generated cases have polymorphic types
only as the type of an object's field (the `UNIVARS` plan), and an
operation needs a way to name that node on both sides. Not done in the
eighth turn; the hand-built tests alone judge R3q, and open question 1
of the pull request asks whether the operation is made before the
slice is issued.

**Tests** (`r3_tests.rs`, all ten passed against the prototype):
`a_node_that_holds_a_universal_variable_is_copied_whatever_its_level`,
`two_places_of_a_holder_are_two_copies_and_of_a_generic_node_one`,
`a_type_that_reaches_itself_is_copied_once`,
`a_polymorphic_type_inside_gets_new_universal_variables`,
`a_node_on_the_way_is_copied_again_when_a_new_binding_is_free_in_it`,
`a_row_copied_without_fixed_loses_its_matched_tags_and_the_flag`,
`a_row_over_a_variable_that_is_not_generic_shares_its_references`,
`a_label_shares_its_record_parameters_with_its_argument`,
`a_field_that_holds_a_universal_variable_gets_its_cell_by_its_row`,
and the step test `instance_poly_at_ten_thousand` (four shapes; three
seen to fail with their structure broken, the numbers in its doc
comment). No source program was run through the two compilers for
them: what they pin is the identity of nodes after a copy, which no
program shows directly; each expectation is followed through the
pasted lines in its doc comment.

**Arms no hand-built test reaches**: a package and an arrow parameter
with a label in `sep_fill` (the arrow arm is reached, labels are not
checked); a universal variable that no binder on the way binds
(ill-scoped; `sep_fill`'s last arm copies its node); `copy_sep_row`
with `keep` on a home that is opened already, on a row with a name
that has arguments, and with a field whose reference is resolved;
`poly_begin`'s clearing of the stamps; `instance_label` with a live
memo of constructors without arguments; a row whose `more` is a
generic constructor or `nil` (the stub is a variable when `fixed'` is
computed, as in OCaml; the test of `fixed` reads rows over universal
variables only).

**What the seventh turn's text had wrong**, each read from the lines
above:
- "the memo of copies is keyed by (node, the length of `bound`)":
  there is no memo. `visited` is the way, and a holder met in two
  places is two copies.
- "no list is needed [for the delayed copies]": one is. `Checker::
  copy_refs` reads the source of a copied row as `g.work[copy -
  first]`, so the nodes of a session must be contiguous and in the
  order of its queue; the walk makes nodes of its own, so the session
  runs after it, from a list, as OCaml's does.
- "`copy_refs` gets `fixed: bool` from the caller": it does not change.
  A session copy is always `copy_row copy true` (ctype.ml:868); the
  rows of the walk are built by `copy_sep_row`, which holds the lines
  of `copy_row` only this slice reaches.
- "one bottom-up pass ... a bit in a mark generation": a bottom-up
  pass is wrong for a type that reaches itself; it is OCaml's inverse
  graph and propagation, and one bit is not enough to stop a class at
  a node another class marked (decision 92).

### 8.11 The ambiguity of GADT instances (R3s)

**State after the ninth skeleton turn: R3s is issued.** This section
was designed as text in the seventh turn and corrected in place in the
eighth against the source and against what pull requests 350 and 352
learned (8.6, decisions 85 to 88). In the ninth turn the whole slice
was written as a prototype from this text, run against the generated
cases and thirteen new tests, and taken out again; the tree holds the
skeleton (25 bodies `todo!("R3s")`, every guard in place, no bit ever
set) and the tests, ignored. What the run changed is decisions 105 to
112 of 8.6 and the part "As built in the ninth turn" below, which
REPLACES the table of sites and the contract further down where the
two differ; the text between is kept as it was reviewed.

**As built in the ninth turn.**

*The byte.* `Checker::gadt`, four bits: `GADT_LOCAL`, `GADT_TRACING`,
`GADT_MEMBER`, and `GADT_PATTERN` (pattern mode, kept by
`unify_pattern`: it lets `unify_distinct` decide with one load,
decision 105). Set by: `add_gadt_equation`, `fresh_abstract` (the
types `reify` makes) and `add_local_type` (`LOCAL`); `trace_on`
(`TRACING`); `push_instance` (`MEMBER`, with one count of
`TypeTable::scoped`, so that every lowering of the unit is the scoped
one from then on); `leave_case` puts `LOCAL` back.

*The table of sites*, per site what a unit without a local constraint
pays and what runs behind the read:

| Site (function) | OCaml | The read | Behind it |
|---|---|---|---|
| `unify_distinct` | ctype.ml:2235 | `gadt & (LOCAL \| PATTERN)`: one load, one branch a unification of two distinct types, at every depth | `unify_distinct_gadt`: `trace_on`, off at the end; in pattern mode without a local constraint the frames run pair by pair (`late_pair`) |
| `unify_var`, the variable arm | 2759-2764 | `gadt & LOCAL`, one load a call | `deep_occur` first (2757), then `trace_on`, off before the link |
| `lower_args`, `non_recursive_abbrev`, `traced` | typecore.ml:2828; ctype.ml:1534; 2781-2785 | `gadt & LOCAL`, one load a call | `trace_on`, off at the end |
| `subst` (an expansion that was not memorized) | 1215-1227 | `gadt & TRACING`, one load an expansion | `subst_traced`: the level of the equation or of the node's set, the refusal, `inherit_own`, two members |
| `memorize` of a constructor without arguments | 200-202 | `gadt & TRACING`, one load | `memorize_own` |
| `find_expansion` of a constructor without arguments that the shared memo does not hold | 200-202, 1191-1192 | `memo.own_live`, one load | `find_own_expansion` (under tracing only) |
| `cleanup_abbrev`, `forget_abbrev` | btype.ml:623-627, 646-650 | `memo.own_live`, one load | a new generation of the own memos; one entry forgotten |
| `unify_pair`, two constructors without arguments of one type | 2254 | `memo.own_live`, one load on that arm | `has_own_expansion`: the pair goes to unify2 |
| `expand_head` (not `Unif`; not `Opt`, whose `try_expand_head_opt`, 1319-1321, has no chain), after a head expanded | 1271-1276 | a compare of two registers; `gadt & MEMBER` when the head expanded | `expanded_instance`: one lookup, the chain |
| `unify_expanded`, inside `if !unexpanded` | 1271-1276 at 2278-2281 | `gadt & MEMBER`, one load a pair of which a head expanded | `expanded_instances` |
| `unify_expanded`, before unify3 | 2289-2298 | `gadt & TRACING`, one load a call that comes there | `join_instance_levels` (nothing without a member) |
| `lower_scoped_loop` | 587-589 | none for a unit without a scoped type (`types.scoped == 0` is `Graph::lower`, as before); otherwise `gadt & MEMBER` once a call and once after each expansion, and a register test a node | `instance_escapes`: one lookup a node above the level |
| `copy_in` | 770-774 | `gadt & MEMBER` and `gadt & LOCAL`, one load a call; `copy` and `instance` do not change | the members read once (decision 107) |
| `recover`, `try_frame` | 2269-2271 | none new: one more bit of the record's flags | tracing put back as the attempt found it |
| `resume_frames` | 2235 | `gadt & PATTERN` a pair, pattern mode only; the test goes with the build | `late_pair` |

Not built (decision 112): the lowerings of `unify_fields` (2490) and
`set_more` (2610-2611). Measured on `tc_kernel`: decision 111.

*The arm of two locally abstract types* is as written below: its guard
is `equations` not empty (decision 65), tracing is on when it runs, and
its one expansion is where the set of the equation gets its first
members. The hand-built test of that arm now makes its nodes at the
level of the newer equation (decision 112).

*The contract R5b receives* (decision 101 as changed by 105 and 107).

| What the walk does | Call | OCaml |
|---|---|---|
| Add a scope, before the patterns are typed | `let mark = c.enter_instance_scope(lev)`, then `c.set_env(..)` for the new environment | `init_env` of `type_function` with a generalized constructor, typecore.ml:4034-4043; of the function with a pattern that is not a variable, 4196-4197 (`if do_init && not has_gadts then init_env ()`); of `type_cases`, 4819-4826; of its exhaustiveness check without one, 4913-4914 |
| Drop the environment of a case, or of a pattern unification that failed (`set_state`, 1299-1305) | `c.leave_case(mark)`; a mark without a scope is `c.case_mark()` | the equations, the scope and the local-constraint bit go back together |
| An existential type of a constructor pattern | `c.add_local_type()` | ctype.ml:970 |
| `expand_head_trace` | `c.traced(\|c\| c.expand_head(ty, ExpandMode::Unif))` | `filter_arrow_n`, `filter_method`, `filter_method_field`, `filter_object_field_for_write` (ctype.ml:2781-2785) |
| `lower_args`, `unify_var`, an equation's `local_non_recursive_abbrev` | nothing: the kernel's functions trace themselves | typecore.ml:2828; ctype.ml:2759, 1534 |
| A copy where OCaml writes `instance env` or `instance_list env` (61 of the 84 copy sites of the expression walk; the table is in the body of pull request 350) | `c.copy_in(root)` for a scheme held as nodes; a template (`c.instance`) needs nothing, it has no member. A scheme generalized while `c.gadt & GADT_MEMBER` is set is kept as nodes and not captured | typecore.ml lines 1869, 2553, 2607, 2660, 2782, 2825, 2826, 2905, 2968, 3044, 3102, 3126, 3148, 3153, 3161, 3189, 3242, 3264, 3288, 3551, 3552, 3780, 3794, 3992, 4065, 4076, 4169, 4172, 4211, 4233, 4235, 4293, 4315, 4338, 4359, 4575, 4591, 4598, 4659-4660, 4740, 4745, 4750, 4848, 4869, 4906, 4911, 4927, 4937, 5102; typetexp.ml 308, 310, 400, 417 |
| A copy where OCaml writes `instance_def`, or typetexp's `instance_list` (19 sites) | `c.copy(root)` or `c.instance(template)` | typecore.ml 340-344 (constants), 2769, 4315 and 4319 (a label, in a record and in a field assignment), 4381-4483 (the results of the operators, seven), 4739 (a constructor); typetexp.ml:373 |
| `instance_poly`, `instance_label` | as built: they never take the environment | ctype.ml:1081, 1097 |
| A restore | `c.restore(token)`, as today: it undoes set additions through the trail | btype.ml:749-751, 773-784 |

Three `instance env` sites of OCaml have no copy in today's checker
(typecore.ml:2498, 4496, 5092: pull request 350's body); R5b reads
them there. The line lists are the ones that pull request matched
site by site; they were not read again in this turn.

**What OCaml does**, each range pasted from compiler/ml at this trunk.

*Tracing* (ctype.ml:176-192):

```text
let trace_gadt_instances_key = Request_local.new_key (fun () -> ref false)
let trace_gadt_instances () = Domain.DLS.get trace_gadt_instances_key
let check_trace_gadt_instances env =
  (not !(trace_gadt_instances ()))
  && Env.has_local_constraints env
  &&
  (trace_gadt_instances () := true;
   cleanup_abbrev ();
   true)

let reset_trace_gadt_instances b = if b then trace_gadt_instances () := false

let wrap_trace_gadt_instances env f x =
  let b = check_trace_gadt_instances env in
  let y = f x in
  reset_trace_gadt_instances b;
  y
```

It is turned on when it is off and the environment HAS A LOCAL
CONSTRAINT, which is wider than "an equation exists" (decision 85: an
existential type of a constructor pattern and a type `reify` made are
local constraints too). Turning it on forgets the memorized expansions.
Who turns it on: `unify` at its top (2235; pasted in decision 65's
range, 2227-2273); `unify_var` in its variable arm (2759-2766);
`expand_head_trace` (2781-2784); `local_non_recursive_abbrev` (1534);
and typecore's application around `lower_args` (typecore.ml:2828):

```text
(* compiler/ml/ctype.ml:2759-2764, in unify_var *)
      let reset_tracing = check_trace_gadt_instances env in
      try
        occur env t1 t2;
        update_level env t1.level t2;
        link_type t1 t2;
        reset_trace_gadt_instances reset_tracing
(* compiler/ml/ctype.ml:2781-2785 *)
let expand_head_trace env t =
  let reset_tracing = check_trace_gadt_instances env in
  let t = expand_head_unif env t in
  reset_trace_gadt_instances reset_tracing;
  t
(* compiler/ml/ctype.ml:1534 *)
    wrap_trace_gadt_instances env (local_non_recursive_abbrev false [] env p) ty;
(* compiler/ml/typecore.ml:2828 *)
    wrap_trace_gadt_instances env (lower_args env []) ty;
```

*A set per scope* (env.ml:1307-1308, pasted in decision 85's
neighbourhood): `Env.add_gadt_instance_level lv env` pushes an empty
set at level `lv`. typecore adds one in the `init_env` of `type_cases`
(typecore.ml:4819-4826) and of the function with patterns, when a
pattern has a generalized constructor, and also where an
exhaustiveness check is made without one (typecore.ml:4196-4197 and
4913-4914: `let lev, env = if do_init && not has_gadts then init_env ()
else (lev, env) in`). The seventh turn cited 4040 and 4826: both are
the `add_gadt_instance_level` line of an `init_env`, 4826 the one of
`type_cases` and 4040 the one of `type_function` (typecore.ml:4034-4043:
`let lev, env = if has_gadts then init_env () else
(get_current_level (), env)`), which this section left out (corrected
in review).

*The first member of a set* comes from one place only, the expansion
of an abbreviation that was not memorized, under tracing
(`expand_abbrev_gen`, ctype.ml:1215-1227):

```text
        let ty' = subst env level kind abbrev (Some ty) params args body in
        (* For gadts, remember type as non exportable *)
        (* The ambiguous level registered for ty' should be the highest *)
        (if !(trace_gadt_instances ()) then
           match
             Ext_pervasives.max_int_option lv (Env.gadt_instance_level env ty)
           with
           | None -> ()
           | Some lv ->
             if level < lv then raise (Unify [(ty, newvar2 level)]);
             Env.add_gadt_instances env lv [ty; ty']);
        ty'))
```

`lv` is the expansion level of the declaration, which only an equation
has (`find_type_expansion`, the third component), or the level of a set
that holds the node already. So without an equation no set ever gets a
member, whatever tracing is.

*The readers and the other additions.* `try_expand_head` adds the chain
of memorized expansions WHATEVER the tracing flag, when the expanded
head is in a set (1270-1276, pasted in decision 84's neighbourhood:
`match Env.gadt_instance_level env ty' with ... Some lv ->
Env.add_gadt_instance_chain env lv ty`); `update_level` refuses to
lower a member below its set's level (587-589, pasted in decision 89's
neighbourhood); the copy WITH an environment that has local
constraints adds the copy of a member to the member's set (770-774);
unify2, under tracing, adds the chain of the node in the lower set to
the higher set (2289-2298); and two lowerings are made only under
tracing (`unify_fields`, 2490: `if !(trace_gadt_instances ()) then
update_level !env va.level f1.f_typ`; `set_more`, 2610-2611).
Membership is by representative (env.ml:1314-1323). Every addition is
`set_typeset`, which is logged and so undone by a backtrack
(btype.ml:749-751), unlike an equation (decision 68):

```text
let set_typeset rs s =
  log_change (Ctypeset (rs, !rs));
  rs := s
```

*The memo.* Under tracing every constructor has its own memo
(`proper_abbrevs`, 200-202, pasted in decision 79), and the arm of
`unify` for two nullary constructors of one type is taken only when
neither has a cached expansion (`has_cached_expansion`, called at
2254).

*The refusal* is `Unify [(ty, newvar2 level)]` in both places (589 and
1226). The printer tells it from an escaping constructor by the pair
(printtyp.ml:1342-1359):

```text
  | Tconstr (p, _, _), Tvar _ when unif && t4.level < Path.binding_time p ->
    escape_explanation ppf p
  | Tvar _, Tconstr (p, _, _) when unif && t3.level < Path.binding_time p ->
    escape_explanation ppf p
...
  | Tvar _, _ | _, Tvar _ ->
    let t, t' = if is_Tvar t3 then (t3, t4) else (t4, t3) in
    if occur_in Env.empty t t' then
      fprintf ppf "@,@[<hov>The type variable %a occurs inside@ %a@]" type_expr
        t type_expr t'
    else
      fprintf ppf "@,@[<hov>This instance of %a is ambiguous:@ %s@]" type_expr
        t' "it would escape the scope of its equation"
```

**The five corrections of the seventh turn's text** (first list of
8.9, item 7; second list, item 3).

(i) *When tracing is on.* The seventh turn turned it on when
`equations` is not empty. OCaml's test is taken instead (decision 97).
The narrower test is not equal: without an equation no member can be
added (above), but turning tracing on forgets every memorized
expansion (`cleanup_abbrev`) and, while it is on, the expansion of a
constructor without arguments goes to the node's own memo and not to
`simple_abbrevs`, so a later copy of such a constructor does not link
to the node that was expanded (O11). A case with an existential type
and no equation shows both in OCaml; the narrower test would show
neither.

(ii) *A set gets its first member only from an expansion under
tracing* (the lines above). It is what the guard is chosen from
(decision 87): the flag "a member was pushed in this unit" is set in
that one place and in the three that add to a set that has a member
already.

(iii) *`try_expand_head` adds the chain whatever the tracing flag.* It
reads `gadt_instance_level` of the expanded head on every call. In the
kernel that read is behind the member flag, not behind the tracing
flag.

(iv) *The wrappers.* `expand_head_trace` is used by typecore's
`filter_arrow_n`, `filter_method`, `filter_method_field` and
`filter_object_field_for_write`: it is the walk's, through
`Checker::traced`. `unify_var` and `local_non_recursive_abbrev` are the
kernel's own (`Checker::unify_var`; `Checker::non_recursive_abbrev`,
which as built does not trace): each turns tracing on at its entry by
the same one read. `lower_args` is the kernel's function too
(`Checker::lower_args`, R3d) though OCaml's wrapper is at its caller:
the kernel's turns tracing on itself, so the walk cannot forget it; it
is the one wrapper with a witness program (CHECKER_DEPARTURES A1,
"Second part").

(v) *An equation whose level has no instance scope adds nothing.*
OCaml asserts that the scope exists (`List.assoc lv env.gadt_instances
with Not_found -> assert false`, env.ml:1326-1328); typing never
builds an equation without one, the tests of `src/tc` do. The kernel
adds nothing there, as today's checker does since pull request 350.

**Where the sets live and how an addition is undone** (decision 98).
A scope is a row of `Checker::instance_scopes` (`level: u32`, `parent:
u32`, `head: Ty`; 12 bytes); `Checker::instance_scope: u32` is the
innermost scope of the environment the caller is in, `NONE` outside.
`head` is a node of the graph, a variable with no name whose `b` is
the index of the scope's newest member in the pool
`Checker::instance_members` (`ty: Ty`, `next: u32`; 8 bytes), or
`NONE`. An addition pushes one pool row and WRITES THE HEAD NODE with
`Graph::write`: logged inside a speculation and put back by its
restore, as `set_typeset` logs `Ctypeset`. So the restore of an
attempt of pattern mode (`recover`) and an owner's restore undo a set
addition with no line of their own, and `Try` does not change
(`undo_compress` undoes none, here as in OCaml: it puts back links
only, as `Btype.undo_compress` puts back `Ccompress` only,
btype.ml:792-804; corrected in review); the pool row an undone addition pushed is not
reached again. This is the design of the references of a variant row
(decision 34). Not chosen: the pool's length in the `Try` record and
in a mark the walk holds (the seventh turn's text): an owner's restore
that forgets to cut would leave members, and an addition outside any
`Try` but inside an owner's speculation needs the owner to know of the
pool.

`instance_level(ty)` walks the scopes from `instance_scope` outwards
and, per scope, its list, comparing `repr(member)` with the node; the
first scope that holds it gives the level. Linear in the additions of
the scopes visited (a member added twice is listed twice, as in
today's checker; OCaml's set holds it once). A unit reaches it only
behind the member flag.

**The one read that decides** (decision 99). One byte of `Checker`,
`gadt`, beside `umode`, with three bits: `LOCAL` (the environment has
a local constraint: kept by `add_gadt_equation`, by `reify`'s fresh
types, by `Checker::add_local_type` for an existential type, and put
back by `leave_case`), `TRACING`, and `MEMBER` (a member was pushed in
this unit; set where a pool row is pushed; never cleared). Per site,
for a unit without a member:

| Site (kernel) | OCaml | The read | With the bit set |
|---|---|---|---|
| `unify_distinct`, at depth 0 | 2235 | `gadt & LOCAL`: one load, one branch a top-level unification of two distinct types | `TRACING` on, `cleanup_abbrev`; off again at the end if this call turned it on |
| `unify_var`, `lower_args`, `non_recursive_abbrev`, `Checker::traced` | 2759, typecore 2828, 1534, 2782 | the same read at the entry | the same |
| `subst`, the arm of an equation (an expansion that was not memorized) | 1220-1227 | `gadt & TRACING`: one load, behind the test for an equation, which a unit without one does not pass | `instance_level(ty)`, the level test, two pushes |
| `memorize` and `find_expansion` of a constructor without arguments | 200-202 | `gadt & TRACING` in `memorize`; in `find_expansion` one load of `memo.own_live` (0 when no own memo is live) | the own memo (decision 100) |
| `expand_head` (the chain) | 1271-1276 | `gadt & MEMBER`: one load a call | `instance_level(head)`, then the chain |
| `lower` | 587-589 | none new: `types.scoped == 0` is `Graph::lower` as today; the first member increments `types.scoped`, so a unit with a member takes `lower_scoped`, which reads `gadt & MEMBER` once a call | `instance_level` a node above the level |
| the binding walk | 587-589 through `update_level` | none new: it lowers through `lower_to`, behind the same test | as `lower` |
| `instance`, `copy` | 770-774 | none: they do not change. The walk calls `Checker::instance_in` and `copy_in` where typecore passes the environment; each reads `gadt & MEMBER` once and is `instance` or `copy` when it is clear | one `instance_level(source)` a copied node, a push a member |
| `unify_expanded` (unify2) | 2289-2298 | `gadt & TRACING`: one load a call that reaches the comparison, to be folded with the load of `umode` at R5c | two `instance_level` and a chain |
| `unify_fields`, `set_more` | 2490, 2610-2611 | `gadt & TRACING`, one load a call | one lowering a field, one a new row |
| `unify_pair`, two nullary constructors of one type | 2254 | one load of `memo.own_live` on that arm | the two own memos |
| `unify_newtypes` | 2258-2270 | nothing new: `equations` is not empty, as built | its expansion is a traced one (below) |

So a unit that never has a local constraint pays one load and one
branch at each of: a top-level unification of distinct types, an
entry of the three kernel wrappers, an `expand_head`, a
`unify_expanded` past its equality test, a `unify_fields`, a
`set_more`, an `instance_in` or `copy_in`, and the arm of two nullary
constructors of one type. Each is listed to be measured on the five
unification operations and the copy and instance operations of
`tc_kernel` by the builder, without a target.

**The arm of two locally abstract types** (place G5 of the
pattern-mode search; decision 65; built as `unify_newtypes`). It and
this slice meet in one place: the arm expands the NEWER type once
(`try_expand_once`) and lowers nothing first, and that expansion is
the one that, under tracing, gives the equation's set its first
members at the node's own level. Without the arm the pair goes to
unify2, which lowers both nodes to the lower level before expanding,
and the expansion is then refused (the program `eq<a, b>`, `Refl => if
true { x } else { y }`, which OCaml accepts: CHECKER_DEPARTURES A1,
p11). The arm's guard stays `equations` not empty (decision 65: without
an equation neither side expands); tracing is on when it runs because
`unify_distinct` turned it on.

**The memo of a constructor without arguments while tracing**
(decision 100). A dense table `Memo::own`, indexed by the NODE's
handle (8 bytes a row: the generation of the memos and the expansion;
the private bit in the generation's low bit), grown to the node when
one is memorized under tracing, and `Memo::own_live`, how many rows
are of the current generation. `cleanup_abbrev` already makes a new
generation, which empties it. `has_cached_expansion` (2254) is one row
load behind `own_live != 0`. Not chosen: the head bit `OWN_MEMO` with
the expansion in the node's `b` (the seventh turn's text; bit 6 of the
head is free): a copy of the node (`Node { level, ..node }` in
`Graph::copy_ref`) would carry the bit, and every test `head ==
CONSTR` for a nullary constructor (`mcomp_frames`; the guard text of
decision 65) would read a memorized node as something else. The
prototype of the seventh turn wrote the expansion to `lists[b]` and
corrupted slot 0 of another node.

**The contract R5b receives** (decision 101).

- *A scope*: `Checker::enter_instance_scope(level) -> CaseMark` where
  typecore calls `init_env` (typecore.ml:4819-4826 for `type_cases`
  with a generalized constructor, 4034-4043 for `type_function` with
  one, 4913-4914 for its exhaustiveness
  check without one, 4196-4197 for the function with a pattern that is
  not a variable), before the patterns are typed;
  `Checker::leave_case(mark)` where the environment of the case is
  dropped: it puts back `instance_scope`, cuts `equations` and puts
  back the `LOCAL` bit. One call, so that one cannot be done without
  the others. (Today's checker adds no scope at 4913-4914; no program
  shows it: A1, "Open".)
- *A local type*: `Checker::add_local_type()` for each existential
  type of a constructor pattern (ctype.ml:970).
- *Tracing*: `Checker::traced(|c| ...)` around each use of
  `expand_head_trace` (`filter_arrow_n`, `filter_method`,
  `filter_method_field`, `filter_object_field_for_write`). The kernel's
  own entries trace themselves, `lower_args` included.
- *Copies*: `Checker::instance_in` and `copy_in` exactly where
  typecore calls `instance env` or `instance_list env` (61 of the 84
  copy sites of the expression walk, listed by OCaml line in the body
  of pull request 350), `instance` and `copy` at the 19 sites of
  `instance_def` and typetexp's `instance_list`; `instance_poly` and
  `instance_label` never take the environment (ctype.ml:1081, 1097).
- *A restore* is `Checker::restore`, as today: it undoes set additions
  through the trail.

**How the refusal is reported** (decision 102). The clash is `Unify
[(ty, newvar2 level)]` at both places. In `Mode::Success` it is a
`Clash`. In `Mode::Explain` the pair is pushed on `Checker::trace` by
`escape_pair`, which `lower` already uses for a constructor below its
scope (decision 14): the node and one new variable at the level. The
kernel reports the pair and no text; what tells "This instance of T is
ambiguous: it would escape the scope of its equation" from "The type
constructor would escape its scope" is the pair's shape and the level
of the variable against the binding time of the path (the lines
above), which the printer reads; no new kind of clash.

**The harness** (decision 103). The generated cases get both: an
operation `Op::Scope` (old side: `Env::add_gadt_instance_level` at the
current level; new side: `enter_instance_scope`) generated before the
first `Op::Gadt` of a case under `PATTERN`, and `Op::Instance` and
`Op::Lower` run with the environment while a scope is open
(`instance_in`; the scoped lowering). Without a scope the old side
adds nothing and judges nothing of this slice. The slice must make
agree, and its builder empties, exactly two lists: `UNTIL_R3S` (seven
seeds of the pattern plan) and `EXPLAINED_UNTIL_R3S` (five explained
ones); `EXPLAINED_OLD_DIFFERS` stays as it is (decisions 77 and 78).
The test of the lists fails when a listed seed agrees, so a builder
cannot leave a seed listed. The old side is NOT a judge at the sites
today's checker left open without a program (decision 88): the chain
of unify2 after expansion (2293-2298), the lowerings of `unify_fields`
and `set_more`, the wrappers of `unify_var`, `expand_head_trace` and
`local_non_recursive_abbrev`, `copy ?env ~partial`, and the scope of
4913-4914. There the hand-built tests judge, each written from the
pasted lines: the clash of an expansion below its set's level; the
chain of unify2 in both directions; a member that is a link; an
addition undone by `recover` and by an owner's restore; a set with a
level and no equation; tracing turned on by an existential type alone
(its memo effects); the three kernel wrappers; and the step tests (a
lookup at 1,000 and 10,000 members; a unit without a member takes the
same steps as before the slice on the pattern step tests).

**Not decided, for the turn that makes the skeleton** (decision 104):
whether the read of `LOCAL` at the top of `unify_distinct` and the read
of `TRACING` in `unify_expanded` are one load with `umode` (a 16-bit
read of two adjacent bytes) or two, which the prototype measures on
the five operations; whether `instance_level` needs the per-scope list
or one pool scanned once (the seventh turn's form), which the step
test at 10,000 members decides; the size of the slice (the seventh
turn said 300 lines on paper; a size is taken from the prototype).

**Corrections after the review of the eighth turn.** Made in place by
the reviewer where no design decision was needed (1 to 4); owed by the
turn that makes the skeleton of R3s (5 to 11); accepted as they are
(12).

1. Decision 84: the argument was wrong for a constraint that makes two
   parameters one variable; the decision now rests on the invariant
   that a constructor node satisfies its declaration's constraint when
   it is made.
   State: paid in the review of the eighth turn (on trunk).
2. This section: `type_function`'s `init_env` (typecore.ml:4034-4043)
   is a place where a scope is added, in the text and in the contract
   of decision 101; `undo_compress` undoes no set addition.
   State: paid in the review of the eighth turn (on trunk).
3. The build prompt of R3q: the clippy and `cargo doc` gates, the rule
   on loops, and the reading ranges (`diff_list`, `conflicts`,
   `delayed_copy` are ctype.ml 1016-1028; the copy sessions and the
   duplication of a mutability cell are btype.ml 421-470). The row of
   R3q in 8.1 says `rows.rs` and 500 lines, as its prompt does.
   State: paid in the review of the eighth turn (on trunk).
4. Citations: `conflicts` is ctype.ml 1023-1025, `delayed_copy`
   1027-1028, the `Tpoly` stop of `add_univar` 699, `inv_parents`
   678-681.
   State: paid in the review of the eighth turn (on trunk).
5. OWED, decision 84: say how the kernel expands a declaration with a
   constrained parameter (whether a unification runs inside the
   occurrence walk at all); if one does, build OCaml's loop behind the
   flag that unification sets; if none does, pin the invariant with a
   debug assertion where a constructor node is made and a test that a
   constrained declaration's arguments arrive unified.
   State: still owed, to the next design turn; the ninth turn ended
   with H1 and the tenth in R3i (decision 118); neither looked at it.
6. OWED, G1 (a) and (b): below a node that was met again on the way,
   `non_recursive_abbrev` and `occur_pattern` remember nothing and
   enter a node once a path, as OCaml does everywhere (its set is the
   path). On `y = k2<a, D0>`, `D_i = (D_{i+1}, D_{i+1})`, `D_n = (y)`
   with only the second parameter of `k2` constrained, that is 2^n
   entries. No test covers that regime: a test that pins the count as
   a relation between two depths, and cost sentences that say
   "exponential in the depth of sharing below a met node, as OCaml on
   every shared type".
   State: still owed, to the next design turn; the ninth turn ended
   with H1 and the tenth in R3i (decision 118); neither looked at it.
7. OWED, G1 (c): the in-line walk of `lower_scoped` pushes the name
   arguments of every inner node of a chain; OCaml's `iter_row`
   visits only the name of the row whose `more` is not a variant
   (btype.ml:237-240). The code before this turn lowered them too. A
   case with a named inner node, or the reason none exists.
   State: still owed, to the next design turn; the ninth turn ended
   with H1 and the tenth in R3i (decision 118); neither looked at it.
8. OWED, G1 (b), as the turn recorded: the expansion of a constructor
   is tested with its own frame on the way, where OCaml's handler
   uses the outer set (ctype.ml:1401).
   State: still owed, to the next design turn; the ninth turn ended
   with H1 and the tenth in R3i (decision 118); neither looked at it.
9. OWED, R3q: OCaml's `instance_label` calls `instance_poly`, which
   opens a copy session inside the label's, and a mutability cell is
   duplicated once a session (btype.ml:421-425, 465); the kernel runs
   one session (decision 94, which records one difference already).
   Both with a hand-built case, or as recorded differences with the
   reason no source type reaches them. The builder of R3q builds
   decision 94 as written. OCaml forces the delayed copies most recent
   first (ctype.ml:1040, 1093) and `poly_session` runs them in order:
   node identity does not depend on it; the doc comment says so.
   State: still owed, to the design turn after R3q's merge (pull
   request 370, merged during the ninth turn), with what its review
   lists; neither the ninth nor the tenth turn looked at it.
10. OWED, tests: two step tests were not seen to fail
    (`matching_the_fields_of_a_fixed_row_is_one_step_a_field`; shape 3
    of `instance_poly_at_ten_thousand`); `Op::InstancePoly` in the
    harness, judged by today's checker, as the first commit after R3q
    is built.
    State: still owed, to the next design turn, all three parts; the
    tenth turn ended in R3i (decision 118).
11. OWED, R3s: the skeleton, tests, prototype and prompt; the three
    points of decision 104. The guard of the arm of two locally
    abstract types stays as decision 65 left it for R5c.
    State: paid by the ninth turn (the commit "Checker rewrite R3s:
    skeleton, harness and acceptance tests of GADT instances" and the
    document commit after it): decisions 105 to 112, the part "As
    built in the ninth turn" above, the prompt in 8.4. Owed from it,
    to the next design turn: the two lowerings under tracing, the
    chain of a nullary copy through a parent with arguments, a member
    that is a variable, and the step tests of four loops (decisions
    109 and 112): still owed after the tenth turn.
12. Accepted: the R3q entry of
    `ignored_tests_name_the_slices_they_reach` names R3h and R3r (its
    tests build on the checker of pattern mode); `#[inline(always)]`
    on `memorized_node`, the loop body of `link_memorized` cut out
    (the five unification operations read the same to the instruction
    before and after); `PolyCopy` without a size test (one a checker,
    not one a node).
    State: accepted; nothing owed.

**Corrections after the review of the ninth turn.** Made in place by
the reviewer (items 1 to 4), owed (5 to 12), answered (13) or accepted
(14). Each owed item names the direction in which the kernel as
designed differs from OCaml, where one is known.

1. Made, decision 110 and the doc comments of the seed lists. They
   said OCaml's `unify` expands no trace (citing ctype.ml:2779, which
   is the wrapper). The `unify` that wrapper reaches is 2732-2737:
   after a failure it runs `expand_trace` (1697-1701), a `full_expand`
   of every type of the trace, with tracing already put back, so a
   nullary expansion goes to the shared memo (200-202). The old side
   does the same. Seeds 4,000,045 and 20,000,132 of the explained
   pattern plan and 17,000,064 and 20,000,132 of the plan with scopes
   are therefore the NEW side's difference: `EXPLAINED_NEW_DIFFERS`
   (added, empty until the build) and `EXPLAINED_INSTANCES_DIFFER`
   (renamed) say so. Decision 79's reading of 20,000,132 was nearer
   than decision 110's.
   State: made in the review it names (on trunk).
2. Made, built code: `expand_head` added the chain of instances in
   every mode but `Unif`. `expand_head_opt` has no chain step
   (`try_expand_head_opt`, ctype.ml:1319-1321), and `mcomp` expands in
   `Opt`. The guard now leaves `Opt` out: one compare of a register
   where a head expanded. No test runs it (item 11).
   State: made in the review it names (on trunk).
3. Made, the build prompt of R3s in 8.4: the count the builder must
   see (338); the test run in the background; the ranges 1113-1135,
   1319-1336, 1697-1701, 2732-2737 and env.ml 1802-1811; what of the
   prototype is not the builder's to copy (it deletes four size
   assertions and keeps the test of `resume_frames`); the three lists
   of seeds; what is not in the slice.
   State: made in the review it names (on trunk).
4. Made, text: decision 108 (what a backtrack keeps), decision 112
   (the prototype ran with the test of `resume_frames` in place), the
   row of `expand_head` in the table of sites, the doc comment of
   `unify_distinct_from` (`late` is a value at its second call).
   State: made in the review it names (on trunk).
5. OWED, the expansion of a failed trace (item 1). The kernel has no
   counterpart of `expand_trace`: after a unification that fails under
   tracing, OCaml's shared memo holds the expansion of each nullary
   abbreviation of the trace and a later copy of that abbreviation is
   a link to the node (`find_repr`, ctype.ml:778-782); the kernel
   makes a new node. A hand-built test, then the expansion, then the
   two lists emptied of those seeds. "Not observable in a
   compilation" is not shown: typecore.ml goes on after a caught
   `Unify` in several places (2496-2499 is one).
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
6. OWED, three places where the kernel as designed ACCEPTS where
   OCaml refuses, each with a hand-built case and then its build:
   the lowerings under tracing (`unify_fields`, ctype.ml:2490;
   `set_more`, 2610-2611); a member whose representative is a
   variable, which `bind_leaf` lowers without the test (reachable:
   the expansion of an abbreviation to its parameter joins a set at
   1227, and unify2 reached from the `deep_occur` arm, 2240, can add
   the chain of a variable at 2297-2298); the copy with `partial`
   (ctype.ml:752-766, typecore.ml:4065), which copies the nodes that
   are not generic too, each copied member joining. None may be open
   when the new checker is first allowed to accept a unit with a
   local constraint (the gate of R5c).
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
7. OWED, decision 109, the chain through a parent with arguments:
   the kernel makes a node where OCaml links, and `has_own_expansion`
   reads false where `has_cached_expansion` reads through `Mlink`
   (btype.ml:618), so the kernel links at once (ctype.ml:2248-2257)
   where OCaml goes to unify2. A case, or the reason the answers are
   the same.
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
8. OWED, decision 108: a second `Safe` or `Opt` expansion of a node
   refused once under tracing, where the first touched no older node:
   OCaml expands (the memo stayed), the kernel refuses again. A case
   through `expand_head`, or the reason the node is never asked twice.
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
9. OWED, decision 107: `copy_in` adds a copy to the scope in which it
   found the member; OCaml adds it to the first scope of that level
   (`List.assoc lv` in `add_gadt_instances`, env.ml:1324-1329). They differ when two visible
   scopes have one level and the member is in the outer one: the
   lookup answers the same level, but OCaml's addition leaves with
   the inner environment. A case with two scopes at one level.
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
10. OWED, `unify_pair`: the new test `l.a != r.a` keeps two nodes of
    ONE locally abstract type, one with an expansion of its own, out
    of the arm of ctype.ml:2258-2269, which OCaml takes for them (it
    expands the first once and unifies again). The kernel sends the
    pair to unify2. A case that shows the same answer, or the arm.
    State: still owed, to the next design turn; the tenth turn ended
    in R3i (decision 118) and did not look at it.
11. OWED, tests: step tests of the loops no shape of
    `instance_sets_at_ten_thousand` runs wide (the parents of
    `own_ancestor`, the nodes of `inherit_own` and their product, the
    scopes of `instance_scope_at`, the additions of `copy_in`, one
    scope of 10,000 members asked by a lowering of 10,000 nodes); an
    `Opt` expansion that adds no member (item 2); the arms the turn
    lists as reached by no hand-built test (`subst_traced` in `Opt`;
    a clash inside a traced pair of a late pattern unification and
    `recover` putting tracing back; `own_ancestor` past its first row
    and through a row a cleanup emptied; `inherit_own` on a private
    entry; `copy_in` with one source in two scopes; `leave_case`
    after a failed pattern unification). And
    `the_newer_of_two_locally_abstract_types_is_expanded_once` reads
    either memo since this turn: once R3s is built it says which.
    State: still owed, to the next design turn; the tenth turn ended
    in R3i (decision 118) and did not look at it.
12. OWED, for the design of R3i: `ExpandMode::Rigid` expands private
    abbreviations (`matches!(mode, Opt | Rigid)` in expand.rs, since
    R3b), but `expand_head_rigid` is `expand_head` with rigid
    variants (ctype.ml:3184-3189): public, and with the chain. No
    caller yet.
    State: paid in the tenth turn (the commit "the rigid expansion is
    the public one"; decision 113; test
    `the_rigid_expansion_is_public_and_adds_the_chain`).
13. The turn's five questions. (1) The two lowerings are not built
    in R3s; they are item 6. (2) One commit of bodies and one that
    removes the `ignore` and `allow` lines: yes. (3) A scheme
    generalized in a unit with a member, as nodes or with members
    recorded by the capture: decided by R5b's design, which holds the
    schemes. (4) `bind_leaf` and a member that is a variable: item 6;
    a program is looked for first, in today's checker too. (5) The
    explained seeds are NOT left as differences of today's checker:
    items 1 and 5.
    State: answered here; what it leaves owed is in the items it
    names.
14. Accepted: the one test of built code that changed; `#[inline
    (always)]` on `subst_plain` and `unify_distinct_from`, `#[cold]`
    on the new out-of-line bodies; the figures of decision 111 taken
    on the prototype and not on the skeleton (the builder reports
    both columns); the eighth turn's items 5 to 10 untouched, each
    still owed.
    State: accepted; nothing owed.

**Corrections after the review of R3s** (pull request 382). R3s is
built as section 8.11 and decisions 97 to 112 say; what its review
found is the design's.

1. Made, in the pull request of R3s (the builder's second turn):
   decision 106 took a generation of `Checker::marks` for membership
   in an instance set. `add_instance_chain` is reached from
   `expand_head` and from unify2 inside walks that hold generations of
   the same array across that call (`non_recursive_abbrev`,
   `occur_expanding`, `occur_pattern`, `lower_args_walk`), so a node
   that joined a set lost "on the way" or "seen", and on a type that
   reaches itself the walk went round again where OCaml's `visited`
   and `seen` lists stop it (ctype.ml:1505, 1511, 1393-1394;
   typecore.ml:2505). The sets now have marks of their own
   (`Checker::instance_marks`, four bytes a node in a unit that has
   a member). Three tests at the end of `r3_tests.rs`, each seen to
   fail without the change: a walk's marks survive an addition;
   `lower_args` over `n0 := (int => n0)` (it did not end);
   `non_recursive_abbrev` over a type that holds such a node (its
   frames grew without end).
   State: made in the review it names (on trunk).
2. OWED: `instance_clash` puts its pair on the trace without cutting
   the trace to the base of the unification, which `escape_pair`
   does for the refusal of `update_level` (the `Unify` of ctype.ml:
   1226 is the whole trace, as the one of 589 is). They differ when
   the trace holds pairs above the base at the clash. A case, or the
   reason none exists.
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
3. OWED: on the refused path of `ExpandMode::Unif` the memo of the
   expansion stays (decision 108) and `inherit_own` does not run, so
   a second expansion finds a body whose copies without arguments
   have no row of their own. A case after a caught clash.
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
4. OWED: `own_ancestor` passes a row that `forget_abbrev` emptied,
   also after a cleanup; OCaml's cleanup makes that reference `Mnil`
   (it was registered by `memorize_abbrev`, btype.ml:629-634), which
   ends the chain. A case, or the reason the order cannot happen.
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
5. OWED: `subst_traced` reads the level of the node's set before the
   plain expansion; OCaml reads `gadt_instance_level env ty` after
   `subst` (ctype.ml:1217, then 1222). They differ only when binding
   the parameters adds `ty` to a set.
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
6. OWED, to R5: a `Checker` is not reset between units. The state of
   this slice (the byte `gadt`, the scopes and members, the own
   memos and their count, `instance_marks`) needs its reset with the
   rest, and a test that a second unit starts with none of it.
   State: still owed, to R5, as it says.
7. OWED, the same hazard where it was before R3s. Four walks hold a
   generation of `marks` across an expansion (`occur_expanding`,
   `occur_pattern`, `non_recursive_abbrev`, `lower_args_walk`; the
   table is in the pull request of R3s). The expansion of a type with
   a constrained parameter unifies the parameter with its argument
   (`subst_plain`), and that unification can reach other takers of
   `fresh_marks` (`reaches`, `binding_scan`, the occurrence walks
   themselves, in pattern mode `reify` and `duplicate`), which visit
   the argument: a node the outer walk can have marked when the type
   shares or reaches itself. No generated case has a constrained
   parameter yet. A hand-built case, then either marks of their own
   for the walks that expand or a rule that an expansion takes none;
   and a debug assertion that a generation still held is not written
   over. `begin_cell_session`, reached through `link_memorized`,
   marks cells the expansion just made: followed only in part.
   State: still owed, to the next design turn; the tenth turn ended
   in R3i (decision 118) and did not look at it.
8. Made: the cost sentence of `own_ancestor` (the chain is every
   traced expansion above the copy, ended or not: n rows at the n-th
   of a chain of abbreviations, as `find_repr` over OCaml's `Mlink`
   chain) and the size sentence of `OwnMemo` (the table grows to the
   graph's length).
   State: made in the review it names (on trunk).

### 8.12 The relations (R3i, R3j)

Written in the tenth skeleton turn. R3i is designed, with a skeleton,
tests that passed against a prototype, and a prompt in 8.4. R3j was not
designed in that turn; it is section 8.13 (the eleventh turn).

**The callers, and the signatures they need.**

| Relation | Called from | What is passed | What is read |
|---|---|---|---|
| `moregeneral env inst_nongen pat subj` | includecore.ml:47 (`value_descriptions`) | `true`, the two `val_type` | the boolean; the links in the pattern's weak variables stay |
| `equal env rename tyl1 tyl2` | includecore.ml 92, 127, 131, 154, 157, 392, 429, 481, 488, 571, 583, 726, 737 (`true`); 584 (`false`); typedecl.ml 911, 1017, 1224 (`false`), 1738 (`true`); ctype.ml:4351 (`false`) | two lists: parameters with a type, parameters with arguments, one type each | the boolean |
| `matches env ty ty'` | typecore.ml:879 (the result of an arrow against an expected type); typedecl.ml:815 (a constraint on a parameter) | two types | the boolean |

`Checker::moregeneral(inst_nongen, pattern, subject)` takes two nodes
of the graph and makes the instances itself; `Checker::moregen` is the
inner call for a caller that made them from templates.
`Checker::equal(rename, left, right)` takes two slices (a caller copies
a list out of the graph's pools: the walk writes them).
`Checker::matches(ty, pattern)`.

**What each relation writes, and what puts it back.**

| | `moregeneral` | `equal` | `matches` |
|---|---|---|---|
| Speculation | none (decision 114) | one, restored on either answer | one, opened before `rigidify`, restored on either answer |
| Writes that stay | links of the pattern's weak variables with `inst_nongen`; the memo of constructors without arguments | none (the memos: decision 115) | none (the memos are cleaned before the unification, ctype.ml:3170) |
| Expansion | `ExpandMode::Safe` (`expand_head`, 2940-2941) | `ExpandMode::Rigid` (3218-3219; decision 113) | unification's own, then `Safe` for each variable (3160) |
| Universal variables | `enter_poly` and `unify_univar` on `Checker::scopes`, cut back to the length at the entry, which a debug assertion holds at zero (OCaml empties the list and does not put the old value back: `current_univar_pairs () := []`, 3093, 3363) | the same | unification's |
| Packages | `unify_package` with the relation's loop popping its pairs; `package_end` (`PackageDecls`); no supplier: a clash | the same | unification's |
| Pair table | `Checker::related`, cleared at the entry (decision 116) | the same | none: OCaml's `matches` has none |
| Trace | none; cut back to the entry's length | the same | the same |

**The arms of `moregen` (ctype.ml:2925-2991)** against the bodies:

| OCaml | Lines | Body |
|---|---|---|
| `t1 == t2` before and after `repr` | 2926, 2930 | `relate_frames`, the `Pair` frame |
| `Tvar _, _ when may_instantiate` | 2934-2937 | `moregen_pair` 1: `moregen_occur`, `occur`, link |
| two constructors without arguments of one path | 2938 | `moregen_pair` 2 |
| `expand_head` both, one node, `Type_pairs` | 2940-2948 | `moregen_pair` 3 |
| `Tvar _, _ when may_instantiate` of the expanded head | 2950-2952 | `moregen_pair` 4: `moregen_occur` with the unexpanded `t2`, link, no `occur` |
| arrows, tuples, constructors of one path | 2953-2968 | `relate_children`: `push_children` |
| `Tpackage` | 2969-2974 | `relate_children`: `unify_package`; `PackageEnd` |
| `Tvariant` | 2975-2976; 3031-3089 | `moregen_row`, `filter_fields`, `moregen_row_field` |
| `Tobject`, `Tfield` | 2977-2981; 2997-3029 | `relate_fields`, `relate_field` |
| `Tnil` | 2982 | `relate_children` |
| `Tpoly` without and with variables | 2983-2987 | `relate_children`: the pair of bodies; `enter_poly` |
| `Tunivar` | 2988-2989 | `relate_children`: `unify_univar` |
| anything else | 2990 | a clash |
| `moregen_occur` | 2901-2919 | `moregen_occur`, `row_children` |

**The arms of `eqtype` (ctype.ml:3200-3274)**: the same table with
`eqtype_pair` for 3201-3235 (`rename_pair` for the two arms of
variables, `normalize_renaming` for 3191-3198), `relate_children` for
3236-3273, `relate_fields` for 3280-3323 and `eqtype_row` for 3325-3358.

**`matches` (3167-3179)**: `rigidify` (3130-3154) with `row_children`,
`Checker::cleanup_abbrev`, `Checker::unify`, `all_distinct_vars`
(3156-3165).

**Marks.** Every walk of the slice that marks, the structure it marks,
which state OCaml has (a list of the path, or a mark that stays), who
can hold a generation of the same structure when it is called, and what
it calls while it holds its own.

| Walk | Marks | OCaml's state | Callers that hold a generation | Calls while it holds one |
|---|---|---|---|---|
| `moregen_occur` | `Checker::marks`, one generation | a mark that stays (levels negated, `unmark_type` after the walk; 2906, 2912) | none: reached from `moregen_pair` and `moregen_row`, which hold none; `moregeneral` is called by a signature inclusion, outside every walk | `Graph::children`, `row_children`: neither takes one. `occur_univar` and `lower` run AFTER the walk |
| `duplicate_type` | `Checker::marks`, one generation | none (`Subst` marks with `Tsubst`) | none: called by `moregeneral` only | `Graph::children`, `row_children`, `Graph::write`; the copy runs AFTER the walk |
| `rigidify` | `Checker::marks`, one generation; the array grows with the nodes the walk makes | a mark that stays (3132; `unmark_type` at 3153) | none: `matches` is called by the typer, outside every walk | `Graph::children`, `row_children`, `build_variant`, `Graph::link`, `forget_name_children`: none takes one |
| `all_distinct_vars` | `Checker::marks`, one generation, taken AFTER every expansion | a list (`List.memq ty !tyl`, 3161): a set of the heads, not a path | none | nothing: the expansions are a pass of their own before it, because an expansion of a type with a constrained parameter unifies |
| `rename_pair` | `Checker::renaming`, its own table and generation | a list (`subst`) | none: nothing else reads the table | nothing |
| `relate_frames` | `Checker::related`, a hash set | a hash table (`Type_pairs`) | none: `pairs` and `compatible` are pattern mode's | `expand_head`, `occur`, `lower`, unification inside an expansion: none reads `related` |

The relations hold no generation of `marks` across an expansion or a
unification, so the hazard of 8.11 (item 7 of the list after R3s) is
not theirs.

**Cost, and what a unit that calls no relation pays.** Nothing: the six
fields of `Checker` are empty vectors and an empty set, and no built
function tests them. `Checker::expand_head` gained one compare of its
mode (decision 113), which folds at every call with a constant mode.
Per call, each body's doc comment states its cost; the two step tests
pin them as relations between 1,000 and 10,000.

**Source programs** for the three relations, each run through the
OCaml compiler in the second turn of the tenth (`bsc -nostdlib
-nopervasives -bs-no-builtin-ppx -color never`, built from this tree);
the Rust compiler was not run on them. The first `matches_bad` of the
first turn (`type u<'b> = t<'b>`) is ACCEPTED by OCaml, and a use
outside a recursive group (`type bad = t<string>`) is refused by
`Typetexp` before `matches` is asked; the program below is the one
that reaches typedecl.ml:815.

```text
moregeneral_ok    module M: { let f: int => int } = { let f = x => x }
    accepted (exit 0; JavaScript printed)

moregeneral_bad   module M: { let f: 'a => 'a } = { let f = (x: int) => x }
    We've found a bug for you!
    moregeneral_bad.res:1:33-57
    1 │ module M: { let f: 'a => 'a } = { let f = (x: int) => x }
    Signature mismatch:
    Actual declaration (moregeneral_bad.res:1:39):
      let f: int => int
    Expected declaration (moregeneral_bad.res:1:13-27):
      let f: 'a => 'a
    (exit 2)

equal_ok          module M: { type t = (int, string) } = { type u = int; type t = (u, string) }
    accepted (exit 0)

equal_bad         module M: { type t = int } = { type u = private int; type t = u }
    We've found a bug for you!
    equal_bad.res:1:30-65
    1 │ module M: { type t = int } = { type u = private int; type t = u }
    Signature mismatch:
    Actual declaration (equal_bad.res:1:54-63):
      type t = u
    Expected declaration (equal_bad.res:1:13-24):
      type t = int
    (exit 2)

matches_bad       type rec u = U(t<string>)
                  and t<'a> = 'a constraint 'a = int
    We've found a bug for you!
    matches_bad.res:1:16-24
    1 │ type rec u = U(t<string>)
    2 │ and t<'a> = 'a constraint 'a = int
    Constraints are not satisfied in this type.
    Type t<string> should be an instance of t<int>
    (exit 2)
```

(Blank lines of the output are left out.) The outputs agree with the
tables above: `moregeneral` refuses an interface more general than its
implementation, `equal` does not expand a private abbreviation, and
`matches` refuses `t<string>` against `t<int>`.

**What the tenth turn did not do**: decision 118. **R3j** (`subtype`,
`force_subtype`, `enlarge_type`) keeps its three signatures and
`todo!("R3j")` bodies; the range ctype.ml:3396-4235 was not read in the
turn, so nothing is said here about its arms. What the next turn
inherits for it: `Checker::related` is the pair table `subtype_rec`
clears (`TypePairs.clear subtypes`, 4217); `relate_frames` and
`relate_children` are the form its walk should take; `row_children` is
`iter_row`; the entry of R3j in
`ignored_tests_name_the_slices_they_reach` names R3i.

**Corrections after the review of the tenth turn** (pull request 393:
a first-pass review that applied the prototype and read each body
beside its OCaml function, then the final review).

1. Made: line numbers of ctype.ml in the doc comments of `relate.rs`,
   in two tests, in the comment of a seed list, in decisions 114 and
   117 and in the tables of this section. From the arrow arm of
   `moregen` on, and for `moregen_fields`, `moregen_row`,
   `eqtype_fields` and `eqtype_row`, they were 3 to 13 lines off. The
   prototype was posted before the correction: where a line it cites
   differs from the skeleton's, the skeleton is right.
2. Made, in the prompt of R3i, the table above and the doc comments of
   `moregen` and `equal`: OCaml EMPTIES its list of universal-variable
   scopes at the entry of the two relations (ctype.ml:3093, 3363) and
   does not put the old value back; the kernel cuts `scopes` back to
   its length at the entry. The two are one thing only when no scope
   is open at the entry, which the build asserts in debug builds
   (`unify_univar` reads every scope, so a relation entered with one
   open could pair two universal variables OCaml refuses, 1559). No
   caller exists yet: the walks that will call a relation (R5, R6)
   inherit the rule that none is called with a scope open.
3. Made, in the prompt: the loops no step shape runs wide name the
   walk of `moregen_occur` (every shape calls it at the generic
   level, which skips it) and the common tags of `moregen_row`; the
   reading list holds `occur_univar` (1561-1600); what counts a step
   in `normalize_renaming` is said once; the comment that holds the
   prototype is named.
4. OWED BEFORE THE BUILDER OF R3i STARTS, as a task of its own with
   the prototype as the oracle: `relation_plan_agrees_on_generated_cases`
   exempts a listed seed wholly. It asserts that the seeds that differ
   are the listed ones, and nothing about HOW a listed seed differs;
   the classification of the tenth turn was a script run once and is
   not in the test, so a fault of the new side that stays inside the
   77 listed seeds is not seen. A listed seed must differ AND fit the
   class its list names, else the test fails with the seed: for the
   two `EQUAL` lists, the two forms differ only in answer lines that
   read `equal = false` on the old side and `equal = true` on the new;
   for the two `NIL` lists, every answer line agrees and the lines
   that differ are explained by a `nil` node the new side copied (the
   turn's condition, more occurrences of `nil` in the new form, is
   loose: four of the seven seeds rest on it unread; read them);
   for `UNIVARS_OLD_FREE_UNIVAR_DIFFERS`, the first line that differs
   is an answer of `moregeneral`, `true` on the old side and `false`
   on the new. A listed seed that does not fit against the prototype
   is read against the OCaml lines before a body is built. Even then
   the `EQUAL` class would take a new side that answers `true`
   wrongly: the lists are emptied by item 5, not trusted.
   State: made (pull request 396). After its assertions on the set of
   seeds, `relation_plan_agrees_on_generated_cases` makes each listed
   seed again, runs it on both sides and asks `fits` with the class of
   its list, collecting every refusal of a plan before it panics:
   `Equal`, the same failure and line count and every line that
   differs an answer of `equal` with one index, `false` old and `true`
   new; `FreeUnivar`, the first line that differs an answer of
   `moregeneral` with one index, `true` old and `false` new; `Nil`,
   the same failure, every answer line equal line for line, and the
   forms equal after `unshare_nil`, which prints every `nil` node (its
   mark `&n[level]nil` and every reference `@n` to it) as a bare `nil`
   without number or level, as the `nil` of an equation prints, and
   renumbers every other mark and reference in order of first
   appearance. The level goes because the copy can be made at another
   level than the kept node (seed 54000224: a `nil` at level 0 by
   reference against one at level 1). `a_listed_seed_must_fit_its_class`
   runs today and sees each class refuse faults inside a listed seed.
   Against the prototype the test passed: all 77 seeds fit, the four
   `NIL` seeds not read before (69000217, 84000296, 12000099,
   14000052) included, each differing only in `nil` nodes the old side
   shares. Still unseen: the `Equal` class takes a new side that
   answers `equal = true` wrongly on a listed seed, since that is what
   the class expects there; a `FreeUnivar` seed is judged on its first
   difference only; and a fault of the new side that makes a listed
   seed agree is seen by the set of seeds, not by the class (a
   `duplicate_type` that keeps `nil` failed the existing assertion).
5. OWED, today's checker, each with a source program first (decision
   20): `equal` on a row that a unification extended
   (`equal_rows_without_renaming` expands the field `row_more` where
   OCaml follows the chain, ctype.ml:3327 and btype.ml:148-151; 68
   seeds); the copy of `moregeneral` keeps `Tnil` (subst.ml:135-143; 7
   seeds, sharing only); `moregen_occur` asks `occur_univar` only with
   a scope open (ctype.ml:2918; 2 seeds; a free universal variable
   does not come from a program); `equal` takes no snapshot
   (3361-3369). When one is corrected its list is emptied in the same
   pull request, and the test says so by failing.
6. OWED by the eleventh turn, tests: step shapes that run the walk of
   `moregen_occur` (a variable below the generic level), the common
   tags of `moregen_row` with `moregen_row_field`, and `equal` with
   renaming over n rows that each get opened (`normalize_renaming`
   scans the renaming again after every write of the trail: n squared
   over two, as OCaml's `normalize_subst`; the cost sentence of its
   doc comment says less and is corrected with the test); hand-built
   tests for the arms the turn lists as reached by none (packages,
   universal variables, the `Reither` arms, `normalize_renaming` past
   its first compare, `filter_fields` with `erase`); the step shapes
   not seen to fail with their structure broken.
   State: not done, as the eleventh turn was told (it waits for R3i
   to be merged). Still owed, to the review of R3i or the turn after.
7. OWED by the eleventh turn, each decided by a measurement or by the
   lines: `Checker::related` is cleared at the entry of every relation,
   and a clear writes every control byte of a table that one large
   relation grew (clear by count, or shrink); whether `Graph::copy`
   gives the copy of a constructor an empty memo slot
   (`ref Mnil`, subst.ml:172) and copies the arguments of a row's name
   as `Subst.typexp` does, and what `duplicate_type` does for a
   private row (`has_fixed_row`, subst.ml:153-166); the level of the
   node `rigidify` links a row variable to (OCaml's is the marked
   level of the row, ctype.ml:3139-3144); `moregen` called at a level
   other than the generic one (`build_variant` makes the extension at
   the current level where OCaml uses `newgenty`, 3052-3054): its one
   caller is `moregeneral`, so make it private or state the
   precondition.
   State: not done. The eleventh turn ended in K1 (R3j) and started
   nothing of this item; one fact was met on the way: R3j clears
   `Checker::related` at the entry AND at the end of `subtype`
   (ctype.ml:4213, 4217), so after a subtyping the table is empty and
   the next relation's clear finds no entry; whether a clear of an
   empty table that one large relation grew still writes its control
   bytes is not measured. Still owed.
8. Checked in the review beyond the turn's runs: the five source
   programs of this section and thirteen more (open and closed rows in
   both directions, open and closed objects, a weak variable against
   an interface, a polymorphic record field, parameters renamed and
   swapped, records, a constrained parameter given a variable) through
   the OCaml compiler and today's Rust checker: the same answer and
   the same text on all eighteen. CI on the reviewed head ran `tc::`
   at 343 passed and 9 ignored, the count the turn had inferred.
9. Accepted: decisions 113 to 118. 114 (no speculation in
   `moregeneral`) and 115 (the memos are not compared after `equal`
   and `matches`) were read against ctype.ml:3104-3124 and 3361-3369
   and `Btype.backtrack`; for 116, a hash set of pairs is OCaml's own
   structure here and no dense index of pairs exists; `#[inline(never)]`
   on `expand_head_rigid` and the allowance on `mod relate` until R3j
   stand. R3j and the owed items of 8.11 go to the eleventh turn.
   State: R3j is section 8.13 (the eleventh turn). The owed items of
   8.11 were not touched in the eleventh turn: every item of its
   deliverable K2 (the same-marks hazard that predates R3s, the
   lowerings under tracing, the expansion of a failed trace, the rest
   of the R3s, ninth-turn, R3q and eighth-turn lists) is still owed
   as it stands in those lists.

### 8.13 Subtyping (R3j)

Written in the eleventh skeleton turn (trunk `265ff7e37`). R3j is
designed, with a skeleton (27 bodies `todo!("R3j")` in `relate.rs`),
eleven acceptance tests that passed against a prototype, and a prompt in
8.4. Its harness operations are NOT made (decision 126). The line
numbers of this section are trunk's and were read with `sed` and `grep`
from `compiler/ml/ctype.ml` before they were written.

**The callers, and the signatures they need.**

| Function | Called from | What is passed | What is done with the answer |
|---|---|---|---|
| `subtype env ty1 ty2` | typecore.ml:748 (a variant spread in a pattern) | the spread type and the expected type; the closure is called at once | `Subtype (tr1, tr2, ctx)` becomes the error `Not_subtype`; no snapshot |
| | typecore.ml:3608 (a coercion `(e :> t)`) | the type of `e` and the target; then `force ()` of the annotation, then the closure | the same error; no snapshot |
| | error_message_utils.ml:770 (the hint of a type clash) | two types of the clash; the closure at once | `true` or `false`; no snapshot: what it linked stays while the message is printed |
| `enlarge_type env ty` | typecore.ml:3597 | the target of a coercion whose source is not generalizable | the type is unified with the source under the CALLER's snapshot (3594-3604), which is backtracked when that fails; the flag is not read (`let ty, _b = ...`) |

So:

```text
Checker::subtype(left, right, out: &mut Coercion) -> Result<(), Clash>
Checker::force_subtype(coercion: &Coercion) -> Result<(), Clash>
Checker::enlarge_type(ty) -> (Ty, bool)
```

`Coercion` is the closure as data, owned by the caller: the
constraints in the order they are unified, the traces, and the scopes
of universal variables. A caller that never forces drops it or passes
it again; the checker holds nothing of it. `subtype` fails only for two
tuples of different lengths (`subtype_list`, 4104); everything else is
collected.

**What each writes, and what puts it back.**

| | `subtype` | `force_subtype` | `enlarge_type` |
|---|---|---|---|
| Speculation | none (OCaml: none) | none | none (the caller's, typecore.ml:3596) |
| Writes that stay | expansions and their memos, opened rows, compressed paths, the nodes of built constraints, partner nodes | every link of every constraint unified, also before and in a clash | the new nodes, expansions and memos, opened rows |
| Speculation inside | the trial of two packages of different paths (4089-4098), restored on either answer | the top-level unification's own in `Mode::Explain`, closed with `undo_compress` | none |
| Expansion | `expand_once` in `Safe` for a public abbreviation on either side (3673-3678); in `Opt` for a private one on the left (3705-3706) | unification's | `expand_once` in `Safe` (3466-3468, 3483) |
| Universal variables | `enter_poly` on `Checker::scopes`, left by a `Leave` frame; each scope also kept as a `HeldScope` | `open_scopes` puts back the scopes each constraint recorded; emptied at the end | none |
| Pair table | `Checker::related`, cleared at the entry and at the end (4213, 4217) | none | none |
| Trace | `Mode::Explain`: one `TraceLink` a pair pushed; on the error `subtype_trace` | on a clash `subtype_trace` and `trace` without its first pair | none |
| After a failure | `out` is empty, `scopes` empty, `unexplained_failure` in `Mode::Success` | the links stay; the constraints after the clash are not unified | cannot fail |

What the callers do after a failure: typecore.ml 748 and 3608 raise
the error of the unit and read no type again; error_message_utils.ml:770
goes on printing with what was linked. None restores, so the kernel
restores nothing.

**The arms of `subtype_rec` (ctype.ml:3643-4101)**, in the order of the
source.

| Arm | Lines | Where | Body |
|---|---|---|---|
| `t1 == t2` after `repr`; the pair table | 3644-3652 | R3j | `subtype_pair` 1 |
| a variable on either side | 3654-3655 | R3j | `subtype_pair` 2: `constrain` |
| two arrows of one arity and labels | 3656-3668 | R3j | `subtype_pair` 3: parameters swapped, then the results |
| two tuples; `subtype_list` | 3669-3671; 4103-4107 | R3j | `subtype_pair` 4: the one error |
| two constructors without arguments of one path | 3672 | R3j | `subtype_pair` 5 |
| a public abbreviation on the left, then on the right | 3673-3678 | R3j | `subtype_pair` 6: `expands`, `expand_once` in `Safe` |
| two constructors of one path, by variance | 3679-3704 | R3j | `subtype_constr`; `Invariant`, `Back`, `Close` |
| a private abbreviation on the left | 3705-3706 | R3j | `subtype_pair` 8: `expand_once` in `Opt` |
| anything against a private record or variant | 3707-3720 | R6e: reads `type_private` and `type_kind` of the right type's declaration (`extract_concrete_typedecl`) | refused: step 13 |
| `int` to `float` | 3721-3724 | R6e: reads which type indices are `Predef.path_int` and `path_float`, which the kernel's table does not say | refused |
| a primitive to an unboxed variant | 3725-3768 | R6e: reads the constructors and the unboxed attribute | refused |
| a variant to a primitive | 3769-3797 | R6e: reads the constructors' runtime representation | refused |
| two variants, two records, two other declarations | 3798-4027 | R6e: reads constructors, labels, representations; calls `subtype_list` on their types | refused |
| two objects that both end in a variable | 4030-4033 | R3j | `subtype_pair` 10: `object_row`, `constrain` |
| two objects | 4034; 4109-4173 | R3j | `subtype_fields` |
| two variants | 4035-4038; 4175-4210 | R3j | `subtype_row` |
| a closed variant to a variant declaration | 4039-4061 | R6e: reads the constructors | refused |
| a variant to another type (`variant_is_subtype`) | 4062 | R6e: a hook the typer installs, over the tags and the target's declaration | refused |
| two polymorphic types, three cases | 4063-4072 | R3j | `subtype_poly`; `Leave` |
| two packages | 4073-4100 | R3j with the supplier `PackageDecls` (`compare`, `complete`, and the two methods of this turn, `same_path` and `subtype`); without a supplier refused | `subtype_package` |
| anything else | 4101 | R3j | `subtype_pair` 13: `constrain` |

"Refused" is the same thing for every arm left to R6e: the pair
reaches step 13 and becomes the constraint of the two types, which
unification accepts only when they are one type. Every one of those
arms either accepts or makes exactly that constraint (with a context
for the message), so the kernel without them never accepts what OCaml
refuses; it refuses what they accept (`(1 :> float)`). The places
where R6e inserts them are named in the doc comment of `subtype_pair`
(steps 9 and 11). Test: `abbreviations_expand_and_what_is_left_out_is_refused`
(`int` against `string`, a closed variant against a constructor).
`Completion::Abstract` and `Completion::Missing` are skipped for the
names only the left package lists (`~allow_absent:true`, 4077-4078) and
end the arm for the names only the right one lists.

**The arms of `build_subtype` (ctype.ml:3427-3587)**: all built in R3j;
none reads a label or a constructor.

| Arm | Lines | Body |
|---|---|---|
| a variable (`loops` is `[]` at the one entry, 3592) | 3430-3437 | `enlarge_visit`: itself |
| an arrow | 3438-3454 | `enlarge_visit`, `enlarge_leave` |
| a tuple | 3455-3464 | the same |
| a constructor that is expanded | 3465-3471 | `enlarge_expansion`, `has_constr_row`; a leave frame with `ENLARGE_EXPANDED` |
| a constructor, by variance | 3472-3500 | `enlarge_visit` (`TypeTable::upper`; `ENLARGE_KEEP`, `ENLARGE_FRESH`), `enlarge_leave` |
| a static variant | 3501-3537 | `enter_row`, `enlarge_variant` |
| an object | 3538-3547 | `enter_row`, `enlarge_leave` |
| a field | 3548-3575 | `enlarge_visit`, `enlarge_leave`: a new cell |
| `Tnil` | 3576-3582 | `enlarge_visit` |
| a polymorphic type | 3584-3586 | `enlarge_visit`, `enlarge_leave` |
| a universal variable, a package | 3587 | itself |

**The loop, and why it is its own** (decision 119). `subtype_rec`
differs from `moregen` and `eqtype` in what a pair IS: it carries a
trace, it collects where they clash, its arrow arm swaps the sides,
and three of its arms need a continuation after a walk (the two
directions of an invariant argument, the end of a row that raised
`Exit`, a constraint that OCaml makes after a walk that is still
pending). So it has its own stack, `Checker::subtyping`, of `SubFrame`
(16 bytes: two types, the trace link, a kind byte and a flag byte)
with six kinds: `Pair`, `Constrain`, `Leave`, `Invariant`, `Back`,
`Close`. Nothing of R3i is changed: `relate_frames`, `Relation` and
`FrameKind` stay as they are. `enter_poly` is called as it is; the two
frames it pushes on `Checker::frames` are taken off at once and their
meaning goes on `subtyping` (the pair of the bodies above a `Leave`).

**The constraints** (decision 120). OCaml's constraint is `(trace, t1,
t2, univar_pairs, ctx)` (3655; ctype.ml:96 for the exception that
carries what it yields). In the kernel: `Constraint` is 16 bytes: the
two types, `trace` and `scopes`.
- *The trace* is a list whose tail every deeper pair shares. Here one
  `TraceLink` (12 bytes: the pair and the parent's index) a pair
  pushed, in `Coercion::links`, in `Mode::Explain` only; a constraint
  holds the index of its innermost pair. On a failure
  `read_subtype_trace` follows the parents and reverses, into
  `Checker::subtype_trace`. An expansion adds no pair (3675, 3678), nor
  do two polymorphic types without variables (4063).
- *The scopes.* `enter_poly` leaves its scope when the bodies are done,
  so the stack cannot be what a constraint keeps. Each scope entered is
  also appended to `Coercion::scopes` as a `HeldScope` (the 20-byte
  `PolyScope` and the index of the scope around it); a constraint holds
  the index of the innermost. The partner nodes of a scope are nodes of
  the graph, so two constraints that hold one scope see each other's
  pairings, as OCaml's share the `ref`s. `force_subtype` unifies under
  those scopes (`unify_pairs`, 2769-2771): `open_scopes` moves
  `Checker::scopes` from one constraint's chain to the next by popping
  and pushing only what differs, which over a coercion is linear (the
  constraints are in walk order); making the stack again a constraint
  is quadratic for nested scopes, and the step test fails on it.
- *The context* (`ctx`) is `None` in every arm R3j builds; R6e adds
  it with its arms.
- *The order.* OCaml conses and reverses (4231), so constraints are
  unified in the order they were made, except those of two packages,
  which are put in front of the list in name order and so unified last
  name first (`cstrs' @ cstrs`, 4086, 4094). `subtype_fields` makes two
  constraints AFTER the walk of the two rests (4114-4134): they are
  `Constrain` frames below that pair.
- *No scope is open at the entry of `subtype` and of `force_subtype`*
  (debug assertions): OCaml empties its list at 4214, and the kernel
  empties `scopes` at the end of both. The two agree because the entry
  length is zero. No arm calls `equal` or `moregen`, so R3j needs no
  relation of R3i entered with a scope open.

**Quiet regions** (decision 122). Two places of `subtype_rec` walk
pairs and drop what the walk collected, while the pairs it visited
stay in the table:
- an invariant argument: `subtype_rec ... t1 t2 [] = [] && subtype_rec
  ... t2 t1 [] = []` (3689-3690);
- a row that raises `Exit` after some of its tags were walked: the
  handler at 4037-4038 has the list of before the row.

`Coercion::quiet` counts the open regions and `Coercion::dirty` says
whether the innermost made a constraint; inside one, `constrain` only
sets `dirty` and no node is built (the nodes of a dropped constraint
are held by nothing). The first is the three frames `Invariant`,
`Back`, `Close`; the second is a `Close` frame with no pair above a
`Constrain` of the two rows.

**The visited list of `build_subtype`** (decision 125). OCaml's
`visited` is a list of the PATH: a node is consed on entry (3441,
3458, 3479) and is gone on return; an object or a variant makes it `t
:: filter_visited visited` (3506-3508, 3543-3544), which drops the
entries down to the nearest object or variant (3404-3407), or `[t]`
when the budget went down. `memq_warn` (3409-3413) scans it. It is not
a mark that stays: `the_enlarged_type_of_a_coercion_without_a_source`
has a cycle `T = (O, int)`, `O = {a: T}` in which `T` is entered twice.

So the list at any moment is: the objects and variants entered since
the last cut to `[t]` that are still open, and the other nodes entered
since the innermost of those. `Checker::path_entries` gives each node
the number of its entry (a clock that only grows) and `EnlargePath`
holds two numbers: a node that is not a row is in the list when its
entry is above `base` (the entry of the innermost open row), a row
when its entry is at or above `floor` (the entry of the row that last
cut). Entering a node writes its entry and keeps the old one in its
leave frame; entering a row moves `base`, and `floor` when it cuts; the
leave frames put all three back. Membership is one load and one
compare; OCaml's is a scan, and `filter_visited` another. The answer
is the same because the two numbers describe exactly the list above.
Its own table and not `Checker::marks`: the walk holds its entries
across `expand_once`, and an expansion of a type with a constrained
parameter unifies and takes generations of `marks`.

The budget is the `level` of the frames (4 at the entry, 3589-3592;
`pred_expand` 3395 at an expansion, `pred_enlarge` 3396 at a row), three
bits of `EnlargeFrame::state`. The flag `warn` is returned.

**Marks and shared scratch.** Every structure a body of R3j uses that
something else may hold.

| Structure | Used by | Held across | Who else can hold it then |
|---|---|---|---|
| `Checker::subtyping` | `subtype_frames`, above the length at the entry | `expand_once`, `enter_poly`, `instance_poly`, the trial `unify`, the supplier | nobody: no other function reads it |
| `Checker::related` | `subtype_pair` | the same | nobody: the relations of R3i run outside `subtype`; pattern mode has `pairs` and `compatible` |
| `Checker::frames` | `subtype_poly` takes off the two frames `enter_poly` pushed, in the same call | nothing | a `subtype` called inside a unification would see that unification's frames below: only the top two are touched |
| `Checker::scopes` | `subtype_poly`, `Leave`, `open_scopes` | the walk; a forced unification | asserted empty at both entries |
| `Extras::fields` | `subtype_fields`: taken, cut back to the length found, put back | `build_field` only | `unify_fields` takes it for one call; no call of it is pending during `subtype_fields` |
| `Extras::row_scratch` | `subtype_row`, `has_constr_row`, the variant arms of `enlarge_visit` and `enlarge_variant`: above the length found, cut back before any walk goes on | `open_row`, `flatten_row`, `merge_rows`, `field_now_at` | `unify_row` works above the length it finds too |
| `Checker::rigid_vars` | `subtype_poly`: the variables `instance_poly` returns, taken and put back empty | `instance_poly` | `matches` (R3i) uses it for one call; `subtype` is not called inside `matches` |
| `Checker::marks` | none of R3j's own walks | — | `enter_poly`, `expand_once` and `unify` take generations inside their own calls; R3j holds none across them |
| `Checker::path_entries` | `on_path`, `enter_path`, the leave frames | `expand_once` | nobody |
| `Checker::enlarging`, `enlarged` | `enlarge_type`, above the lengths at the entry | `expand_once` | nobody |
| `Graph::work` | none of R3j | — | — |
| `Checker::trace` | cleared by a failed `subtype`; cut by the package trial | — | a `subtype` called inside a unification that is building a trace would lose it: no caller does |

**Cost, and what a unit that never coerces pays.** Nothing: the new
fields of `Checker` are empty vectors and no built function reads them.
`TypeTable::occurs` is one byte a parameter as before (decision 121).
Per call, each doc comment states its cost; the two step tests pin
them.

**Source programs.** Not run in this turn (decision 126): the sandbox
had no built OCaml compiler and the turn's budget went to the
prototype. The programs the review should run through both compilers
are listed with the open questions of the pull request.

## 9. R4 as designed

Section 6.5 gave R4 as one slice of seven commits. It is replaced by this
section: nine build slices, a skeleton (`src/tc/{name_table,scope,names}.rs`,
every body `todo!("R4x")`), the old environment's trace
(`src/tc/scope_trace.rs`), an oracle that replays it
(`src/tc/scope_oracle.rs`) and acceptance tests (`src/tc/r4_tests.rs`). A
builder fills bodies in. It does not change a signature, a stated cost or a
test; when one cannot be met it stops and reports a reproduction.

### 9.1 The data

Sizes are pinned by `scope::tests::sizes`, `names::tests::sizes` and
`name_table::tests::sizes`.

| Row | Bytes | One per | Layout |
|---|---:|---|---|
| `Name` | 4 | distinct name of a worker | dense index into `NameTable` (bytes in one buffer, a span per name, one hash table by content). Kept for the worker |
| `Key` | 4 | name in a namespace | `name << 3 \| namespace`; indexes the head table, orders a member table |
| binder | 18 | bound name | `Binders`: `key` 4, `payload` 4 (a type, a type index, a member row, a table or an alias target, by kind), `loc` 4, `previous` 4 (the binder of the same key it hid), `kind` 1, `used` 1 (used, the three constructor usages, deprecated) |
| head | 4 | key | `Scopes::heads[key]`: the innermost binder of the key, or none |
| log entry | 4 | binding in an active scope | the binder; its undo datum is `previous` |
| `Scope` | 12 | scope | `parent`, `first_binder`, `opens` (innermost visible layer) |
| `Layer` | 12 | `open` | `table`, `mark` (the binder count when opened), `older` |
| `Open` | 16 | `open` | `loc`, `root`, `shadowed` (list of names already reported), `flags` (used, `open!`) |
| `ShadowNote` | 8 | name an open was reported to shadow | `key`, `next` |
| `Table` | 12 | member table | `first`, `len`, `unit` |
| `Member` | 12 | member of a module | `key`, `target` (a binder, or the index of an `ExportItem` in the unit's segment), `origin` (local, or the unit with a deprecated bit) |
| `UnitSlot` | 16 | dependency a worker has read | `Arc<Segment>`, `name`, first slot of its tables in `table_index` |
| `Resolved` | 4 | what a use means | bits 31..30: a binder; a row of `imported_members`; a unit |
| `Found` | 8 | answer of a lookup | `item: Resolved`, `layer` (the open it came through, or none) |
| `Warning` | 16 | warning raised | `kind`, `loc`, `a`, `b` |

**What an identifier resolves to.** A `Resolved`, 4 bytes: a binder of this
unit (also for a member of a module of this unit, reached through an open
or a path), or a row of the worker's imported members (which names the unit
and the export item), or a unit. The walk of R5b stores it in
`ExprRow::resolved` and passes nothing else down for a name. A lookup
returns `Found` (8 bytes) because the use needs the layer once, for the
open's usage and shadowing; it is not stored.

**What a lookup walks.** By name: one load of the head, then one binary
search in each visible layer whose `mark` is above the head binder,
innermost first, stopping at the first that has the key
(`Scopes::find`). By path: the first component as a name (or as a unit),
then per component one `module_shape` (aliases followed, 1 step each) and
one binary search in the module's table (`Scopes::lookup_path`). By binder:
one indexed load of the array wanted.

**Where the rows live.** `Scopes` is one value per worker. Names, units and
imported tables stay for the worker; binders, scopes, layers, local tables,
warnings and read logs are truncated to the frozen prefix by
`Scopes::reset`. The head table is never cleared: leaving every scope
restores it.

### 9.2 The slices

| Slice | Builds | File | Depends on | Can be built beside | Lines |
|---|---|---|---|---|---:|
| R4a | The name table; `Binders::push` | `name_table.rs`, `scope.rs` | R2 | R4h | 150 |
| R4b | Scopes, the head table, the undo log, `freeze` and `reset` | `scope.rs` | R4a | R4h | 250 |
| R4c | Member tables of this unit, `seal`, opened layers, `find`, `find_below`, `candidates` | `scope.rs` | R4b | R4h | 450 |
| R4d | Dependencies: units by name, an export table imported once per worker, deprecation bits | `scope.rs` | R4c | R4h, R4i | 350 |
| R4e | Paths: `module_shape` through aliases, `lookup_path`, `candidates_in` | `names.rs` | R4d | R4h, R4i | 450 |
| R4f | Usage and the warnings of a use: `arm`, `mark`, `use_found`, `use_modules`, `finish` | `names.rs` | R4e | R4h, R4i | 350 |
| R4g | Reads of other units | `names.rs`, two call sites in `scope.rs` | R4f | R4h, R4i | 150 |
| R4h | Deletes `types/env_log.rs` and `types/env_log_tests.rs` | `types/` | nothing | any slice | -4,466 |
| R4i | The oracle under `RESCRIPT_CHECKER=both` in builds with debug assertions; the bench | `driver.rs`, `scope_oracle.rs`, `benches/tc_kernel.rs` | R4c | R4d to R4h | 300 |

R4a to R4g are one line: they fill the same two files and each uses the
one before. R4h reads nothing of the rest. R4i needs the lookup of R4c and
nothing later.

**What still reads `env_log.rs`.** Nothing. Its only reference is
`#[path = "env_log.rs"] mod env_log;` under `#[cfg(test)]` at the end of
`types/env.rs`, and `env_log.rs` includes `env_log_tests.rs` the same way.
`rg -n 'env_log' compiler-rust/src` prints those two lines and the file's
own text. Deleting the two files and the `mod` line removes 4,466 lines and
their tests, and no other test.

Every slice has its acceptance tests in full in `r4_tests.rs`, ignored
with the slice's name, except R4h (a deletion: its criteria are commands)
and the wiring of R4i (a command on `tests/tests`; the oracle itself is
tested today).

### 9.3 Decisions

Each is settled by a test that runs on the old checker today
(`r4_tests.rs`, `scope_oracle.rs`), by a probe with a release build of
trunk and the OCaml compiler as witness, or by the OCaml source.

**1. Lookup order and shadowing.**

- *Local over open, open over an older local.* One table per namespace
  holds current bindings and, below them, an opened layer and the table
  before the open (`IdTbl`, compiler/ml/env.ml:240-290). A lookup takes
  the current bindings first, then the layer, then what was there before:
  a binding made after the open hides the layer's member, the layer hides
  every binding made before it. Pinned by `LOCAL_SHADOWS_AN_OPEN`
  (`y: int`), `OPEN_SHADOWS_A_LOCAL` (`y: string`) and `LOCAL_OPENS` (an
  open inside a function hiding a binding of the enclosing function, and
  ending with its block). In the design this is one comparison: a layer is
  probed when its `mark` is above the head binder.
- *Later open over earlier.* `LATER_OPEN_WINS`: `y: float` from the second
  open, `z: int` from the first.
- *The same name in two namespaces.* `ONE_NAME_IN_EACH_NAMESPACE`: the type
  `t`, the label `t` and the value `t`; the constructor `T` and the module
  `T`. A `Key` carries the namespace, so they are different heads.
- *Constructors and labels.* A lookup returns every candidate, innermost
  first (`TycompTbl.find_all`, env.ml:202-213, and `lookup_all_simple`,
  env.ml:1028-1045); the choice among them by the expected type is
  `disambiguate` (compiler/ml/typecore.ml:976-1070). **R4's part**:
  `Scopes::candidates` (and `candidates_in` for `M.A`), in that order,
  with the layer each came through. **Not R4's**: choosing by the expected
  type, reading a label or a constructor straight from the expected
  type's declaration when it is not in scope at all, and the warnings of
  the choice (40, 41, 42); that is R5b for records and variants of the
  core language. `TYPE_DIRECTED` pins both halves on the old checker:
  `(r: a) => r.x` is `a => int` although `b` was declared later with the
  same label, and `r => r.x` is `b => string`, the first candidate.
- *A qualified path through aliases.* `PATH_THROUGH_TWO_ALIASES`:
  `module N = A; module O = N; O.B.v` and, across units,
  `module P = Dep; module Q = P.A; Q.B.v`, both `string`; the signature
  keeps `module Q = P.A` as written. `Env.lookup` resolves the module
  prefix with `lookup_module_descr` and then reads the component
  (env.ml:952-1026); an alias is followed when its components are needed
  (env.ml:732-760, 854-880). In the design an alias binder's payload is the
  `Resolved` of its target and `module_shape` follows it, 1 step an alias.

**2. Warnings at a lookup.** Probes, each compiled by a release build of
trunk and by the OCaml compiler with the same output:

| Program | Reported |
|---|---|
| `open M` hides a local `x`; `let y = x`; then a type error | warning 44 at the `open`, then the error |
| the same with the type error before `let y = x` | the error only |
| `open M` never used, then a type error | the error only: no warning 33 |
| `M.v` deprecated; `let a = M.v`; a type error; `let c = M.v` | warning 3 at the first use, then the error |
| unused type, constructors, value, variable, no error | 34, 37, 37, 34, 34, 32, 26 in declaration order, after everything else |

So there are two kinds, and the contract (2.1, O15) follows from when each
is raised.

- *Raised when the walk reaches the use*: deprecation (3;
  compiler/ml/typetexp.ml:98-123, env.ml:940-945 for a module on a path)
  and "this open statement shadows" (44 for a value, type, module or module
  type; 45 for a constructor or label). The latter is raised by the open's
  `using` callback the first time a lookup goes through the layer and finds
  something older that it hides, once per name and open, not for `open!`
  (env.ml:279-288, 1881-1908). `Scopes::use_found` and `use_modules` raise
  both, with one exception (9.7, decision 6): for a constructor or a label
  the open shadows only when the two result types differ
  (`check_shadowing`, env.ml:415-420), so `use_found` hands the hidden item
  back and the walk reports through `Scopes::shadows`. Finding raises
  nothing: `find`, `candidates` and `lookup_path`
  write no flag and no warning, so a lookup that disambiguation or a
  speculative typing abandons leaves no trace (2.4, idea 5).
- *Armed at the declaration, raised at the end of the unit*: unused value,
  variable, type, constructor, module (26, 27, 32, 34, 37, 60) and unused
  open (33). OCaml registers a delayed check when the declaration enters
  the environment (`check_usage`, env.ml:1562-1576; env.ml:1890-1894 for
  an open) and runs the checks in that order after typing; a unit with an
  error never runs them. `Scopes::arm` and `arm_open` keep the order;
  `Scopes::finish` raises; the caller does not call `finish` for a failing
  unit.
- *What "used" means.* An open: a lookup went through its layer and was
  used (`OPEN_USED`). A value, type or module: `mark(binder, USED)`
  (`mark_value_used`, `mark_type_used`, `mark_module_used`,
  env.ml:947-950, 1080-1088). A constructor: any of built, matched,
  privatized (env.ml:38-47). *Which* uses count is the walk's rule, not
  R4's: a use of a `let rec` binding inside its own definition does not
  (compiler/ml/typecore.ml, `type_let`, the `current_slot` and
  `rec_needed` refs), and signature inclusion marks what a signature
  exports. R4 gives the bit and the order.

Pinned today by `old_checker_lookup_warnings_are_pinned`: the warnings of
the thirteen programs, in order.

**3. Unit reads.** The old checker records two things.

- *The units whose interface it loaded*: `PersistentEnv::find_pers_struct`
  records an import for the unit and for every unit its CRC list names
  (`record_import`, cmi/persistent_env.rs; `Env.find_pers_struct` and
  `add_import`, compiler/ml/env.ml:570, 646-691); under `-no-alias-deps`
  an alias names a unit without loading it (`check_pers_struct`,
  env.ml:666, called from types/typemod.rs). The driver reads the set as
  `loaded_units` (sorted) and `imports` (with CRCs, for the `.cmi`).
- *Item reads for incremental builds*: `types::unit_reads` walks the typed
  tree after checking and collects every path rooted at a unit and every
  type the tree carries (its module comment; `structure_reads`,
  `signature_reads`), which `cmi::item_deps::resolve_reads` closes over the
  declarations they reach.

R4 logs: a unit when its interface is loaded for this unit
(`unit_by_name`, also when the worker knew the unit from an earlier
compilation, and also for a lookup that is abandoned, as OCaml's load is);
an imported member when it is used (`use_found`). Both are dense bits with
a list in the order first read. That order is the order of the walk, so it
does not depend on worker count; the *indices* in the lists do (they are
the worker's), and a consumer turns them into names
(`reads_do_not_depend_on_what_the_worker_checked_before`).

R4 deliberately leaves: reads through a type that no lookup of this unit
named (the inferred type of `Dep.f()` mentions `Other.t`), reads of an
expansion that crosses a unit (R5a fills `expand::TypeTable` rows and logs
there), the CRC closure of a loaded unit and the `.cmi` import list (R5c),
and the port of the item-read consumer (R9c). Until R9c the old
`unit_reads` walk runs on the bridge's typed tree.

**4. The oracle.**

- *Where the old checker reports.* In `types/env.rs`: `bump_id` (a new
  environment version and the one it extends), the seven `add_*` functions
  (a binding with namespace, name and stamp), `add_prebuilt_open_layers`
  (a layer with every member), and the seventeen `find_*` functions by
  name (a lookup with the stamps found: one for `IdTbl.find_name`, all
  candidates for `TycompTbl.find_all`). An item's identity is namespace,
  name and stamp: the old side reads it off the `Ident`, the replaying
  side binds it as a number.
- *What it costs when off.* The hooks are under `#[cfg(debug_assertions)]`:
  a release build has no instruction for them, so the CI instruction count
  cannot move. In a debug build a hook is one thread-local load while no
  capture runs.
- *The same scope structure without a walk.* The new side cannot have the
  walk's scopes before R5b. It does not need them: the old environment is
  persistent, its versions form a tree, and a lookup names its version.
  `scope_oracle::replay` moves a scope structure through that tree with a
  stack discipline (leave to the common ancestor, enter down to the
  lookup's version, one scope a version) and asks the same question. That
  the trace is sufficient is not argued, it is run:
  `the_reference_model_answers_what_the_old_environment_answered` replays
  the thirteen programs on a naive model and agrees on every lookup, and
  `a_wrong_resolution_is_reported` shows a model with one rule wrong being
  caught. Slice R4c runs it on `Scopes`
  (`scopes_answer_what_the_old_environment_answered`); slice R4i runs it
  on every unit of `tests/tests` under `RESCRIPT_CHECKER=both`.
- *What it cannot check before R5b.* The replay opens a layer with the
  members the old layer had, not with a segment's: that an imported table
  lists the same members is `an_import_lists_the_members_of_the_old_layer`
  (R4d). A qualified path is not a lookup of `Env`'s tables in the old
  checker (the prefix is one, the rest goes through component tables of
  `env_lazy.rs`): paths are tested on the pinned programs (R4e) and on
  whole units by R5c's oracle, which compares resolved rows. The choice by
  expected type is not R4's.

**5. The two measurement gates.** The old checker costs, from H.2.11
(table of 2.2): 299 instructions a lookup by name (603 M for 2,017,342),
105 a lookup by identifier (684 M for 6,487,233), 932 a binding with its
undo. The kernel of 2.2 measured 5, 5 and 44 for a design without layers.

The bench (`benches/tc_kernel.rs`, measured as TC_KERNEL_R1.md describes)
gets these operations; every one takes an interned `Name`:

| Operation | Shape | Gate |
|---|---|---:|
| `binder` | `binders.payload[b]` for a binder in an array of 1,000 | 10 |
| `find_local` | `find` of a name bound after two opened layers of 256 members | 80 |
| `find_open` | `find` of a name with no binding, in the inner of two layers of 256 members | 80 |
| `find_miss2` | `find` of a name in the third layer after missing two of 256 members | reported |
| `bind_leave` | `enter`, `push`, `bind`, `leave` | reported, beside the kernel's 44 |
| `intern` | `NameTable::intern` of an 8-byte name already in the table | reported |

Interning is not inside the 80: a lookup takes a `Name`. How a syntax node's
name becomes a `Name` is R5b's (question 2 of 9.6).

**6. Corrections to the task text of 6.5.**

- *"Open layers that point at a Segment's export table."* An export
  table's names are indices of the segment's own string pool and the table
  is sorted by them (bridge/from_old.rs, "Export names are segment string
  indices"). A worker cannot probe it with its own name. A layer therefore
  points at a member table; for a dependency that is the export table
  imported once per worker and table: one 12-byte row and one hash per
  export item, then never again. "Open a module: O(1)" (3.3) holds from the
  second open of a table on. The alternative is question 1 of 9.6.
- *"The per-namespace head table indexed by interned name."* One table
  indexed by `Key`: the namespaces of one name are adjacent.
- *"The undo log" of 8-byte entries `name, previous` (3.2).* `previous`
  is a binder array, because the candidates of a constructor or label are
  the chain through it; a log entry is the binder, 4 bytes.
- *"Used bit."* A byte: a constructor has three usages (env.ml:38-47).
- *"The warnings a lookup raises (deprecation, unused open)."* Unused open
  is not raised by a lookup; it is armed at the open and raised at the end
  of the unit. A lookup raises deprecation and the shadowing warnings 44
  and 45, which the text does not name.
- *"A lookup under 10 opened modules probes at most 10 layers."* A probe is
  a binary search, so the count is 1 plus the comparisons. The test uses
  one-member tables, where a probe is one comparison and the counts are
  exact (11 for a miss, 4 for a hit in the third layer, 1 when the binding
  is younger than every layer), and one 10,000-member layer (at most 15).
- *"Every identifier the old checker resolved resolves to the same item
  here."* As decision 4: every lookup by name of the old environment, by
  replay; qualified paths and the choice by expected type are not
  replayable before R5b.
- *"Unit reads logged at the lookup."* A unit at its load, an item at its
  use; reads no lookup names are R5's and R9c's (decision 3).
- *Paths R4 does not resolve.* A module whose type is a named module type
  resolves to that module type's members (`ModuleShape::Abstract`); giving
  their types the module's path is `Mtype.strengthen`, R6d's. A functor
  application in a path and a module type that is neither a signature nor
  a name of one give `PathErrorKind::Unsupported`; R6d declines or builds
  them.
- *"A lookup by name outside the walk's current scope" is a failure.* Kept.
  It follows that a row's `scope` index cannot answer "what does this name
  mean there" later; `Scope` rows stay for the unit, and what a reader
  needs from them is question 5 of 9.6.
- *"`rg -n 'HashMap|Rc<|RefCell' src/tc/scope.rs src/tc/names.rs` gives
  0."* Kept, with `src/tc/name_table.rs` beside them holding the one hash
  table (`hashbrown::HashTable`): no index exists for the bytes of a name.
  `UnitSlot` holds an `Arc<Segment>`, cloned once per worker and unit.
- *3,000 lines.* About 2,150 of implementation in seven slices, 300 for
  the oracle's wiring and the bench.

### 9.4 Per slice: functions, end state, commits, failure, gates

The gates of 5.3 apply to every slice. Tests are in `src/tc/r4_tests.rs`;
a slice is done when its tests pass without `ignore`. `rg` is run from
`compiler-rust/`.

**R4a.** Functions: `NameTable::{intern, find, text}`, `Binders::push`. End
state: `rg -n 'todo!\("R4a"\)' src/tc` is empty; tests
`names_are_interned_once_and_dense`,
`ten_thousand_binders_are_one_step_each`. Commits: (1) the name table; (2)
binders. Failure: a `String` or a `Box` per name; a hash seeded per
process (names must hash the same in every run: fixed seeds, as
`crate::name` does); a binder row wider than the six arrays.

**R4b.** Functions: `Scopes::{enter, leave, bind, head, freeze, reset}`.
End state: `rg -n 'todo!\("R4b"\)' src/tc` is empty; tests
`ten_thousand_bindings_then_leaving_is_three_steps_a_binding`,
`a_lookup_under_ten_thousand_nested_scopes_is_one_step`,
`shadowing_and_namespaces`, `reset_returns_to_the_frozen_prefix`. Commits:
(1) enter, bind, head; (2) leave; (3) freeze and reset. Failure: clearing
or scanning the head table; a scope that copies its parent's bindings; a
`leave` that walks binders instead of the log.

**R4c.** Functions: `Scopes::{table_from, seal, open, search, member,
find, find_below, candidates}`. End state: `rg -n 'todo!\("R4c"\)'
src/tc` is empty; tests
`a_table_of_ten_thousand_members_is_searched_in_fourteen_steps`,
`a_lookup_under_ten_opened_modules`,
`an_open_shadows_a_local_and_a_local_shadows_an_open`,
`seal_lists_what_a_structure_exports`, `candidates_are_innermost_first`,
`scopes_answer_what_the_old_environment_answered`. Commits: (1) tables and
search; (2) seal; (3) open and find; (4) find_below and candidates.
Failure: probing a layer older than the head binder; a linear scan of a
table; a sort that is not stable; copying a table to open it.

**R4d.** Functions: `Scopes::{add_unit, unit_by_name, import_table,
item}`. End state: `rg -n 'todo!\("R4d"\)' src/tc` is empty; tests
`an_export_table_is_imported_once`,
`an_import_lists_the_members_of_the_old_layer`,
`an_import_knows_what_is_deprecated`. Commits: (1) units; (2) the import;
(3) deprecation bits. Failure: importing a unit's every table when one is
asked; an import per unit compiled instead of per worker; asking the
source twice for one name; an `Arc` clone per lookup.

**R4e.** Functions: `Scopes::{module_shape, lookup_path, candidates_in}`.
End state: `rg -n 'todo!\("R4e"\)' src/tc` is empty; tests
`a_path_through_two_local_aliases`,
`a_path_through_aliases_of_another_unit`,
`long_paths_and_alias_chains_are_linear`. Commits: (1) local modules and
aliases; (2) paths; (3) modules of a dependency: signatures, aliases,
named module types, functors. Failure: recursion over an alias chain or a
path; marking or warning in a lookup; resolving an alias when it is bound
instead of when its members are needed.

**R4f.** Functions: `Scopes::{arm, arm_open, disarm, mark, use_found,
shadows, use_modules, finish}`. End state: `rg -n 'todo!\("R4f"\)' src/tc`
is empty; tests `marking_ten_thousand_uses_is_ten_thousand_steps`,
`an_open_is_used_or_unused_and_reports_shadowing_once`,
`the_walk_decides_whether_an_opened_constructor_shadows`,
`unused_binders_are_reported_in_the_order_armed`,
`a_deprecated_item_warns_at_each_use`. Commits: (1) arm, mark, finish; (2)
opens: usage and shadowing; (3) deprecation and `use_modules`. Failure: a
warning raised by `find`, `candidates` or `lookup_path`; an unused warning
raised before `finish`; `finish` in binder order instead of armed order; a
set keyed by name for the shadowing notes.

**R4g.** Functions: `Scopes::{read_unit, read_item}`; one call in
`unit_by_name` and one in `use_found`. End state: `rg -n 'todo!\("R4'
src/tc` prints nothing; the
`#[allow(...)]` lines of `name_table`, `names` and `scope` in
`src/tc/mod.rs` are gone; tests
`reads_are_logged_once_in_the_order_first_read`,
`reads_do_not_depend_on_what_the_worker_checked_before`. Commits: (1) the
two logs; (2) the two call sites and the reset. Failure: clearing a bit
set by its length at `reset`; a sorted or hashed read set; a read logged
by `find`.

**R4h.** End state: `src/types/env_log.rs` and
`src/types/env_log_tests.rs` do not exist; `rg -n 'env_log' src` prints
nothing; `cargo test --manifest-path compiler-rust/Cargo.toml` runs the
same tests as before minus those of `env_log_tests.rs` (paste both
counts). One commit. Failure: any other change to `types/env.rs`.

**R4i.** Changes: `scope_trace::capture` and `tc::scope_oracle` compiled
with `debug_assertions` instead of `test`; in `driver.rs`, with
`CheckerChoice::Both` and debug assertions, the type checking of a unit
runs under `scope_trace::capture` and its events are replayed on a
`Scopes` (the `OnScopes` resolver moves from `r4_tests.rs` to
`scope_oracle.rs`); a `Mismatch` fails the unit as a signature mismatch
does; the bench operations of decision 5. End state: a debug build of
`rescript` with `RESCRIPT_CHECKER=both` builds `tests/tests` with no
mismatch and the log line `tc-names-replayed <unit> <lookups>` for every
unit (`rg -c`); a release build's instruction count on `tests/tests` is
within 0.02% of its base; the bench table. Commits: (1) the resolver and
the cfg; (2) the driver; (3) the bench. Failure: a hook, a branch or a
thread-local on the release path; replaying under `old`; a capture that
is left on after a panic.

### 9.5 The build prompts

The common part of 6.0 is prepended to each. Then, verbatim, with the
slice's name in place of "R4x":

```text
You build slice R4x of the type checker rewrite. Read, in this order:
AGENTS.md; compiler-rust/docs/CHECKER_REWRITE.md sections 2.1, 3.3 and 9;
compiler-rust/src/tc/name_table.rs, scope.rs and names.rs whole; the tests
of your slice in compiler-rust/src/tc/r4_tests.rs. The skeleton is fixed:
you fill in every body that says todo!("R4x") with your slice's name, and
nothing else. You do not change a signature, a doc comment's stated cost,
a size test, or a test. You do not add `#[ignore]`, and you remove the
`#[ignore = "R4x build"]` of your slice only. If a signature, a cost or a
test cannot be met, stop: write the smallest reproduction in the pull
request (the test, the line that fails, the OCaml lines the doc comment
cites and what they say) and end your turn. Do not work around it. A test
that contradicts the OCaml lines its doc comment cites is reported the
same way; it is corrected by the designer, not by you.

The behaviour is OCaml's, at the location each doc comment cites; read
that code before you write the body. The programs at the top of
r4_tests.rs pin what the current checker answers; they run today and must
keep passing unchanged.

The intent, not a layout: how you split a body into private helpers is
yours to decide; say what you did in the commit message. A private helper
has a doc comment that states its cost. Steps: `#[cfg(test)]
super::steps::tick()` exactly where the module comment of scope.rs says a
step is counted, and nowhere else. No recursion: a chain is a loop. No
allocation in a lookup. No hash map anywhere but NameTable. Nothing in
compiler-rust/src/types/ is called from these files.

When a module has no todo! left, remove its #[allow(...)] line in
src/tc/mod.rs and fix what the compiler then reports.

Done means, all on your last commit:
  cargo test --manifest-path compiler-rust/Cargo.toml tc::   passes, and
    the tests named for your slice in section 9.4 are not ignored;
  rg -n 'todo!\("R4x"\)' compiler-rust/src/tc                prints nothing;
  rg -n 'HashMap|Rc<|RefCell' compiler-rust/src/tc/scope.rs
    compiler-rust/src/tc/names.rs                            prints nothing;
  cargo clippy --locked --manifest-path compiler-rust/Cargo.toml
    --all-targets --all-features -- -D warnings              passes;
  the gates of section 5.3. Nothing of R4 is on a build's path, so the
  instruction count of tests/tests must not move: say the two numbers.
Paste the output of each in the pull request.
```

Then one of these:

```text
R4a. First edit: NameTable::intern in src/tc/name_table.rs. Hash the bytes
with ahash::RandomState::with_seeds and four fixed constants (not
RandomState::new: the numbering must not depend on a per-process seed
beyond the order names arrive in); the table holds name indices and
compares by the bytes of the span. Then find and text, then Binders::push
in src/tc/scope.rs. Commits as in section 9.4. Relations to hold:
interning a text a second time writes nothing; the n-th distinct text is
Name(n - 1); push is one row in each of the six arrays and one step.
```

```text
R4b. First edit: Scopes::enter in src/tc/scope.rs, then bind and head.
bind writes previous[binder] = heads[key], heads[key] = binder, and
appends the binder to the log; when the key is beyond heads, grow heads to
8 * names.len() filled with NONE first. leave pops the log down to the
length recorded in `entered` and, for each binder popped, writes
heads[key] = previous (innermost first), then makes the parent current.
freeze records the seven lengths; reset leaves every scope above scope 0
through the log, truncates binders, scopes, log, layers, opens, notes,
tables and members to the frozen lengths, and clears armed, warnings and
the read logs (the read bits through the two lists). Commits as in
section 9.4. Relations to hold: a head load is 1 step whatever the depth;
entering costs no step; leaving a scope with k bindings is k steps; after
leaving every scope the head table equals what it was before the first
enter; a Scope row is never removed before reset.
```

```text
R4c. First edit: Scopes::table_from in src/tc/scope.rs: append the rows to
`members` with origin LOCAL, sort that run by key with a stable sort, push
the Table. Then search (binary search for the FIRST row of the key), then
seal, then open, find, find_below, candidates. seal reads log[from..]: a
binder whose namespace is Value, Type, Module or ModuleType is a member
when heads[key] is that binder; a Constructor or Label always; rows of one
key are in the order younger first, so give table_from the log's entries
in reverse. find: h = head(key); walk the layers from the current scope's
`opens` through `older` while layer.mark > h (every layer when h is NONE);
the first whose table has the key answers with that member and the layer;
otherwise h with layer NONE. candidates merges two chains by age: the
binders from h through `previous`, and the layers; a layer's members come
before every binder below its mark. Commits as in section 9.4. Relations
to hold: find writes nothing; a layer whose mark is not above the head
binder is never searched; search of a table of n members is at most
floor(log2 n) + 1 steps; the oracle test
scopes_answer_what_the_old_environment_answered passes on all thirteen
programs. If it reports a Mismatch, paste it: it names the lookup and what
each side found.
```

```text
R4d. First edit: Scopes::add_unit in src/tc/scope.rs, then unit_by_name
(unit_heads grows to names.len() with NONE; MISSING is recorded when the
source has no such unit), then import_table. An export table is
Segment::children[signature], a range of Segment::items; an item's name is
an index of the segment's string pool: its text is
signature.bytes[signature.strings[name]]. Intern it, make the key with the
item's kind as the namespace (the discriminants are equal), write one
Member with target = the item's index in Segment::items and origin = the
unit, sort the run by key with a stable sort, push the Table to
imported_tables and store its id with the IMPORTED bit in table_index.
The deprecated bit: a value's attributes are signature.values[payload]
.attributes, a type's signature.type_details[payload].attributes, a
module's or module type's signature.modules[payload].attributes; a member
is deprecated by its first attribute named `deprecated`, as 9.7,
decision 9 says. Constructors and labels get no bit in
this slice. Commits as in section 9.4. Relations to hold: the second
import of a table is 1 step and writes nothing; importing table s of a
unit imports no other table; the source is asked once per name and worker.
```

```text
R4e. First edit: Scopes::module_shape in src/tc/names.rs, the Binder
cases, as a loop. Then lookup_path for local modules, then the imported
cases of module_shape: an imported Module item's payload is a
signature.modules row; its module_type indexes signature.module_types:
Signature(s) is export table s; Alias { path } is a signature.paths row:
PathRow::Ident(i) with signature.identifiers[i].scope an item index k
below UNIT_SCOPE names signature.ordered_items[k] of the same unit (its
declaration is a modules row: continue with it, no name lookup), with
scope NONE names a unit by the identifier's name (unit_by_name), and
PathRow::Dot continues from the parent's shape with one search;
ModuleTypeRow::Ident(path) resolves the module type's row the same way and
answers Abstract of its signature's table; Functor answers Functor.
Everything else answers PathErrorKind::Unsupported. Commits as in section
9.4. Relations to hold: a lookup marks nothing and warns nothing; `modules`
has one entry per component before the last, the alias binder itself and
not its target; an alias chain of length k is k steps and no recursion;
two paths that end at one imported item return the same Resolved.
```

```text
R4f. First edit: Scopes::mark in src/tc/names.rs, then arm, arm_open,
disarm and finish, then use_found. use_found for an item found through
layer L: set OPEN_USED on opens[L]; when the open is not OPEN_OVERRIDE and
find_below(key, L) is Some and no ShadowNote of this open has the key:
for a Value, Type, Module or ModuleType key push the note and the warning
OpenShadows at the open's loc with a = the key and b = L; for a
Constructor or Label key push nothing and return what find_below found
(the walk calls shadows(L, key), which pushes that note and warning
without scanning). Every other case returns None. Then, for any item: when
the binder has DEPRECATED or the
imported member has MEMBER_DEPRECATED, push Deprecated at `loc` with a =
the Resolved. finish walks `armed` once, in order: a binder is unused when
its `used` byte has none of USED, POSITIVE, PATTERN, PRIVATIZE. Commits as
in section 9.4. Relations to hold: the warnings vector after a sequence of
uses is the same whatever was found and not used in between; a second use
of the same name through the same open adds no shadowing warning; finish
adds one warning per armed entry that is unused and nothing else.
```

```text
R4g. First edit: Scopes::read_unit in src/tc/names.rs, then read_item
(which reads the item's unit). Then call read_unit(unit, READ) in
unit_by_name for every answer that is a unit, also on the path that only
loads unit_heads, and read_item in use_found for an imported member. reset
already clears the logs through the two lists. Remove the three
#[allow(...)] lines of the R4 modules in src/tc/mod.rs. Commits as in
section 9.4. Relations to hold: the names of read_units, in order, are the
same for a worker that checked other units before and for a fresh one; a
second read of a unit or an item appends nothing.
```

```text
R4h. This slice deletes; it fills no body. First edit: remove the two
lines `#[path = "env_log.rs"]` and `mod env_log;` at the end of
compiler-rust/src/types/env.rs. Then `git rm
compiler-rust/src/types/env_log.rs compiler-rust/src/types/env_log_tests.rs`.
Nothing else reads them: before you delete, run
`rg -n 'env_log' compiler-rust/src` and paste it; it must show only that
`mod` line, the `#[path = "env_log_tests.rs"]` line inside env_log.rs and
the files' own text. Done means: the two files are gone, the same command
prints nothing, cargo test passes with the test count lower by exactly
the tests of env_log_tests.rs (paste both counts), and the gates of
section 5.3. One commit.
```

```text
R4i. First edit: in compiler-rust/src/tc/mod.rs compile scope_oracle with
`#[cfg(debug_assertions)]`, and in scope_trace.rs give `capture` the same
cfg; move the OnScopes resolver and its `namespace` function from
r4_tests.rs to scope_oracle.rs unchanged. Then the driver: where
CheckerChoice::Both is handled in compiler-rust/src/driver.rs, under
`#[cfg(debug_assertions)]`, run the unit's type checking inside
scope_trace::capture, replay the events on OnScopes with a new Scopes, and
on a Mismatch fail the unit with the text of the Mismatch and the unit's
name; on success log `tc-names-replayed <unit> <lookups>` at debug level
with target "rescript_checker". Then the bench: add the operations of
section 9.3, decision 5, to compiler-rust/benches/tc_kernel.rs and measure
them as docs/TC_KERNEL_R1.md describes. Relations to hold: with the
switch at `old` or `new`, or without debug assertions, no capture starts;
a release build's instruction count on tests/tests is within 0.02% of its
base (paste both numbers); `binder` is at most 10 instructions and
`find_local` and `find_open` at most 80. If a gate is missed, report the
number and the annotated lines; do not change the shape measured.
```

### 9.6 Open questions

1. **An export table is imported into each worker's names, 12 bytes and
   one hash an item, once per worker and table.** The alternative is one
   name table for the build, filled at publication, so that every worker
   probes a segment's table in place and nothing is imported. It needs a
   lock at publication and when a worker meets a new name, a change to
   R2's `ExportItem::name`, and name numbers that depend on scheduling in
   a published segment. Recommended: keep the import; R5c reports the
   imported members per worker on the application, and the build-wide
   table is built only if that is above 1% of a build.
2. **A syntax node's name becomes a `Name` by one hash, unless R5b keeps a
   dense table per unit from the parser's string index.** The parser gives
   every identifier occurrence its own index (`Interner::push_interned`),
   so that table has one slot an occurrence and saves nothing by itself.
   Recommended: R5b measures `intern` on real units first; the 80 of the
   gate excludes it either way.
3. **Qualified paths are not replayed by the oracle**, because the old
   checker does not resolve them in `Env`'s tables. Recommended: accept;
   the pinned programs cover aliases now and R5c's oracle compares the
   resolved row of every expression on whole units.
4. **The names check of `both` mode needs a build with debug assertions.**
   Recommended: R4i reports how long a debug `rescript` takes on
   `tests/tests` under `both`; the coordinator adds it to the
   `compiler-tests` job if it is under ten minutes, and otherwise a
   release build with `-C debug-assertions` only for that job.
5. **A row keeps a scope index, but a name cannot be looked up at a
   remembered scope.** The printer of the explaining mode (shortest path
   of a type at the error) and editor completion ask "what is visible
   here". The `Scope` rows and `first_binder` are kept for the unit, but
   a binder does not record its scope, so the visible set of a left scope
   is not recoverable when the walk bound into one scope after a child was
   entered. Recommended: R5b enters a scope for every binding construct
   whose continuation must not see later bindings (as OCaml makes a new
   environment), which makes a scope's own binders the run from
   `first_binder` to its first child's; R8a states what the printer needs
   before anything is added to a binder.

### 9.7 Decided in review

These bind the builders of R4 and the designers of R5.

1. **The export table of a dependency is imported per worker** (question
   1). No build-wide name table: it would put a lock on every new name and
   scheduling-dependent numbers into a published segment. R5c reports, on
   an application of several thousand units, the imported members per
   worker and the instructions of `import_table`; a build-wide table is
   designed only when that is above 1% of a build.
2. **A name of the syntax tree becomes a `Name` by one hash in R5b**
   (question 2), and R5b reports that hash per source line on real units.
   The gate of 80 excludes it; the gate of R5c (covered units at most 60%
   of the old checker's cost) includes it. A dense table from the parser's
   string index is designed only on that figure.
3. **Qualified paths are not replayed** (question 3). The pinned programs
   cover them until R5c's oracle compares the resolved row of every
   expression.
4. **The names check of `both` mode runs in a build with debug
   assertions** (question 4). R4i reports the time of a debug `rescript`
   on `tests/tests` under `both`; the coordinator wires it into CI.
5. **Nothing is added to a binder for "what is visible here"** (question
   5). R5b enters a scope where OCaml makes a new environment that a
   continuation must not see past; R8a states what the printer needs.
6. **An open shadows a constructor or a label only when the result types
   differ.** `check_shadowing` (compiler/ml/env.ml:415-420) reports
   `Constructor` and `Label` only when `same_constr` says the two result
   types are different type constructors after head expansion; a value,
   type, module or module type is reported whenever something is hidden.
   The skeleton's `use_found` reported every hidden name. Witness, the
   same output from the OCaml compiler and a release build of trunk: with
   `type t = A | B` and `module M = { type t2 = t = A | B }`, `open M`
   followed by a use of `A` reports nothing; with `type t2 = A | C` it
   reports warning 45. Names have no types, so `use_found` returns the
   hidden item for a constructor or label and the walk (R5b), which has
   both descriptions, compares the result types' head constructors and
   calls `Scopes::shadows`. No note is written before the walk's verdict:
   OCaml adds to `shadowed` only what it reports. Tests:
   `old_checker_open_of_the_same_type_reports_no_shadowing` (runs today)
   and `the_walk_decides_whether_an_opened_constructor_shadows` (R4f).
7. **`open!` is never armed.** OCaml gives an `open!` no slot at all
   (env.ml:1884): no usage, no shadowing, no unused-open warning. R5b
   calls `arm_open` only for an `open` without `!` whose location is not a
   ghost.
8. **`segment_of` in the tests reads a published unit through a fresh
   `TypeContext`.** That is a conversion, not a check: nothing is unified
   in it. A test that unifies or lowers on the old checker builds its
   context as the driver does (8.6, the harness's start level).
9. **Which declaration is deprecated** (review of R4d; the builder
   followed the test and OCaml where the build prompt named a narrower
   rule). `Builtin_attributes.check_deprecated`
   (compiler/ml/builtin_attributes.ml:68-125) reads the first attribute
   named `deprecated` and no later one. A plain payload (`@deprecated`,
   `@deprecated("why")`) is deprecated. The record form is deprecated only
   when it has a `reason` field that is a string; a segment keeps the
   record form as an `AttributePayloadRow::Deprecated` row, whose reason
   is then not `Missing`. A reason that is an error when read counts as
   deprecated, so that the use reports it. R4f reads the text and the
   migration templates from the same attribute when it warns.
10. **What the read logs hold** (review of R4g). `read_units` holds every
    unit whose name was asked and found, in the order first asked;
    `read_items` holds every imported member the walk chose with
    `use_found`, in the order first chosen, and reading an item reads its
    unit. A module on a path is not logged as an item: `use_modules` marks
    and warns, and the unit of each such module is in `read_units` through
    `unit_by_name` or through the item at the end of the path. Whether a
    module on a path needs an entry of its own (its shallow identity: an
    alias target, or which table it has) is decided by the designer of
    the first reader of `read_items` (R9), who then adds it in
    `use_modules` with a test; nothing reads `read_items` before that.
    A use of an imported member costs two steps, the use and the read it
    logs; a name that is asked again costs two as well.
