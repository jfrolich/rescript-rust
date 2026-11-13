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
| O11 | A copy of a nullary constructor links to the node whose expansion is memoised, while that memo lives (`find_repr` in `Ctype.copy`, `compiler/ml/ctype.ml`; `copy_type_cached` in Rust) | to add: no fixture isolates it. Slice R0 writes one or records that no program shows it | **stored** if observable: the simple-abbreviation memo |
| O12 | Lowering a level can fail (a type constructor would escape its scope) and can expand an abbreviation to avoid that, which renames | `weak_variable_escapes_later_type.res`, `gadt_existential_escape.res` | follows from O10 with the scope of each path; the walk must run where OCaml's runs |
| O13 | Programs with a cyclic type are rejected | `occurs_check_function_type.res`, `occurs_check_large_type.res`, `occurs_check_through_constructor.res` | follows: a check, not a state |
| O14 | Weak variables: a variable that is not generalised stays one node for the rest of the unit; one left at the end is an error | `non_generalizable.res`, `identity_does_not_generalize.res` | follows from O10 |
| O15 | Diagnostics come in the order the checker meets them, and the warnings met before the first error are printed before it | `fun_return_poly1.res`, `unused_warnings.res` | **order of work**: a lookup-time warning is raised when the walk reaches the use, not before |
| O16 | A type clash prints the two types as they stood when unification failed, with the trace expanded | every `type clash` fixture, e.g. `checker_identity_02_annotated.res` | **failure path only** (2.4, idea 8) |
| O17 | The names of type variables in printed types (`'a`, `'b`, weak `_a`) follow the order the printer meets them and the names variables carry | `fun_return_poly2.res` | **stored**: the name in a variable node; `link_type`'s rule for which name survives |
| O18 | The output does not depend on worker count or scheduling | `scripts/test_worker_determinism.py` | **order of work**: nothing shared is written in an order that depends on scheduling |

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
stand-alone program of 520 lines (measurement probe, not compiler code): a
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
expansion road, at 900. Sum 833 M, **1,270 a line**; with 45% for what the
kernel lacks, **1,850**. *Extrapolated from the kernel; the sizes (pairs
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
| P6 `env_log.rs` (test-only, 4,466 lines) | built, not switched on | **deleted** by the slice that builds scopes (R3) |

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

Both checkers implement the interface: the old one over the typed tree and
`Env` (slice R1, which is a refactor of the readers), the new one over its
tables. That is what lets the backend stay untouched while the checker
underneath it changes, and what the oracle compares through.

Editor tooling asks for a typed tree today. Until it is ported to rows
(THREE_TREES T12) a tooling session keeps using the old checker on the file
being inspected; the last slice ports it and deletes that use.

### 3.8 What is not designed here

- The module language beyond paths and structures (functors, first-class
  modules, `module type of`, recursive modules): ported onto the new
  graph, with substitution as OCaml has it. 1.1% of the checker on the
  application, 3.5% on the test project.
- Rows, objects, polymorphic variants, universal variables, GADT
  equations: ported. They are the `false` branches of the kernel.
- The exhaustiveness algorithm: ported onto pattern handles.
