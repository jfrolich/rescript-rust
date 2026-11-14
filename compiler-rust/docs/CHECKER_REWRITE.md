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
| R3m | Inherited memo entries: a constructor with arguments copied by an expansion links to the expanding node of the same type (8.6, decision 16) | `expand.rs` | R3b | R3k | 150 |
| R3e | Worker-local descriptor pools; objects and fields | `rows.rs` | R3c, R3m | nothing | 500 |
| R3f | Polymorphic variant rows | `rows.rs` | R3e | R3g | 600 |
| R3g | Universal variables, polymorphic types, packages | `rows.rs` | R3e | R3f | 500 |
| R3h | Pattern mode, equations, `reify`, `mcomp` | `rows.rs`, `unify.rs` | R3f, R3g | R3i, R3j | 600 |
| R3i | `moregeneral`, `equal`, `matches` | `relate.rs` | R3f, R3g | R3h, R3j | 600 |
| R3j | Subtyping without the declaration-directed coercions | `relate.rs` | R3f, R3g | R3h, R3i | 600 |
| K2 | The hot paths of unification, no behaviour change (8.7) | `unify.rs` | R3c | every slice above | 150 |

State after the second skeleton turn. Merged: R3a, R3b, R3d, R3c, and K1
(the kernel's hot paths, TC_KERNEL_R3.md). Designed in the second turn, with
acceptance tests that are ignored until the slice is built: R3k, R3m, and
the generated-case acceptance tests of R3e and R3f (the harness prints
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

**R3e to R3j.** Functions: every signature of `rows.rs` and `relate.rs`
carrying the slice's name. End state for each: no `todo!` with its name;
its generator extension and old-side vacuity test (first commit); the
`Full` tier at 10,000 cases with the extension on. R3e: fields in OCaml's
order, the mutability cells. R3f: the fresh row for the missing tags is
made once; closedness and the row name as ctype.ml:2560-2600. R3g: scopes
of universal variables are a stack, not a map. R3h: the pair set only
here; an equation writes one `TypeTable` row and cleans the memos. R3i:
every relation restores its speculation. R3j: the constraints are
returned, not unified inside the walk.

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

The last prompt is superseded by decision 5 of 8.6: no builder starts R3e
to R3j from it.

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
      own memo (ctype.ml:2251), which a nullary constructor never gets
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
    R3m, in `expand.rs`: `Memo::parents`, a dense `Vec<Ty>` by node handle,
    grown only when written, `NONE` by default. `subst` writes, for every
    constructor with arguments its instance made, the expanding node as
    parent, unless that constructor names the type of a node on the
    expanding node's chain whose slot 0 is live, in which case the new node
    becomes a link to that node (`link_node`). The chain of a node is the
    node, then its parent, and so on; a node whose memo was cleaned ends
    the chain (`cleanup_abbrev` clears its parent with its slot 0, as
    `abbr := Mnil` cuts the list, btype.ml:623-627) and a node whose entry
    was forgotten does not (`forget_abbrev` removes one entry and keeps the
    tail, btype.ml:636-647). Cost: nothing for a body without a
    constructor with arguments (the pass over the instance's nodes runs
    only when the manifest has one: a bit in `Manifest`, set by
    `TypeTable::from_segment`); otherwise one step per node of the
    instance and one step per chain entry per such constructor. Acceptance:
    `expand_tier_agrees_on_recursive_abbreviations` (ignored, `R3m build`),
    and a step relation the builder adds as a reviewed first commit: the
    expansion of a chain of n nested `po` nodes is linear (n = 1,000 against
    n = 10,000 within a factor of 11).
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
