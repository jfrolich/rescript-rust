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

## 4. Proof by prototype

The two items with the largest predicted saving that a patch on trunk can
test are unification with its journal (8,297 instructions a line, 2.3 items
1 and 12) and instantiation (4,341, item 4). Names are larger (9,812) but
no patch on today's `Env` tests the design for them: that design removes
`Env`, and CHECKER_REDESIGN H.2.11 is what a replacement behind `Env`'s API
measures.

Both patches apply to trunk 7e1dbc2bd4 (`git apply`), build, and compile
both projects with no difference in signatures, diagnostics or generated
files. They are measurement prototypes, not reviewed code.

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
| R1 | `tc/graph.rs`, `tc/level.rs`, `tc/template.rs`: nodes, pools, `repr`, links, the trail, levels, generalisation, templates with capture and instance, the general copy with a forwarding array. Not wired to the driver | Nothing yet | 2,500 | step counts at 10,000; a property test against the old `instance`, `generalize` and `update_level` through R2's converters is added by R3 | the kernel's operations within 25% of 2.2 when run from the crate's bench | R0 | yes |
| R2 | `tc/segment.rs`, `tc/publish.rs`, `tc/bridge/{from_old,to_old}.rs` for signatures; the canonical signature printed from a segment | Nothing yet | 3,000 | for every unit of both corpora: `to_old(from_old(g))` and `g` print the same canonical signature, with shared-node numbers | publication of a segment from an old graph costs at most what `publish_signature` costs today (1.34% of the application) | R1 | yes |
| R3 | `tc/unify.rs`, `tc/expand.rs`: unification with every case of `ctype.rs`, expansion and its memo, `moregeneral`, `equal`, subtyping | Nothing yet | 6,000 | differential property test: random graphs converted both ways, the same operations on both, canonical forms and failures equal; the `checker_identity_*` shapes as unit tests on the new graph | kernel operations with abbreviations added, reported | R1, R2 | no |
| R4 | `tc/scope.rs`, `tc/names.rs`: binders, scopes, open layers over export tables, path resolution, usage bits, lookup-time warnings | `types/env_log.rs`, `types/env_log_tests.rs` (4,466 lines: the binding log P6 built and did not switch on) | 3,000 | step counts at 10,000 binders and 10,000 nested scopes; a differential test of lookups against `Env` on every identifier of both corpora in `both` mode | lookup by name at most 80 instructions, by binder at most 10, in the crate's bench | R2 | no |
| R5a | `tc/decl.rs`, `tc/walk/typetexp.rs`: type declarations (records, variants, abbreviations, abstract, externals), annotations | Nothing yet | 4,000 | `both` mode on declaration-only units | - | R3, R4 | no |
| R5b | `tc/walk/`: the core expression language on the success path, patterns, `tc/exhaust.rs`, `tc/rows.rs`; structures, aliases and opens in `tc/module.rs` | Nothing yet | 9,000 | step counts at 10,000 for sequences, applications, record fields, match cases | - | R5a | no |
| R5c | The driver takes the new road for units that are not declined; `to_old` for rows (typed tree for the backend); `RESCRIPT_CHECKER=new` works | The ratchet entries of every unit now covered | 2,500 | the oracle, first time on real units | type checking of the covered units of the test project at most 60% of the old checker's instructions for the same units, the bridge included | R5b | no |
| R6a..R6f | One family each, each with its `Declined` reasons: (a) labelled and optional arguments, JSX; (b) polymorphic variants, objects, rows; (c) GADTs, existentials, locally abstract types; (d) functors, module types, `include`, first-class and recursive modules; (e) exceptions, `async`, dicts, unboxed and untagged variants, coercions; (f) interface files and signature inclusion (`tc/include.rs`) | The `Declined` variants of the family and their ratchet rows | 2,000 to 5,000 each | the oracle; the family's `super_errors` fixtures still fail (through the old checker) | the declined count of the family goes to 0 on both corpora; instructions per line of type checking reported | R5c | first of each kind no, then yes |
| R7 | `new` is the default. The old checker runs only for a unit with an error and for tooling | `Declined`, `tc_coverage.txt`, `tc/bridge/from_old.rs` | 600 | every project under `tests/` builds with zero declined units | **type checking at most 24,000 instructions per line on the application** (surroundings included, bridge included), and the CI instruction count of the test project down by at least 12% | all R6 | yes |
| R8a..R8c | The explaining mode: `tc/explain.rs`, `tc/print.rs`. (a) type clashes and the type printer; (b) every other expression and pattern error; (c) declaration, module and inclusion errors. Tooling entry points check with the new checker and get their typed tree from `to_old` | (c) deletes `types/typecore.rs`, `types/typemod.rs`, `types/includemod.rs`, `types/includecore.rs`, `types/parmatch.rs`, `types/printtyp.rs`, and every function of `types/ctype.rs` the backend does not call | 3,000 each | `scripts/test_error_output_parity.sh`, the `super_errors` and `super_errors_multi` suites, with `RESCRIPT_CHECKER=old` no longer accepted after (c) | a failing unit costs at most 2.2 times a passing one | R7 | (a) no, (b) and (c) yes, one error at a time |
| R9a..R9c | Readers on rows and `TypeFacts`: (a) `raw_lambda/typeopt.rs` and `convert.rs`; (b) `matching.rs` and the pattern pool; (c) genType and unit reads (THREE_TREES T9, T10, T11, T3) | (c) deletes the batch build's use of `to_old`, the rest of `types/ctype.rs`, `types/context.rs`, `types/type_expr.rs`, `types/env.rs`, `types/env_lazy.rs`, `types/thread_store.rs`, `types/shared_store.rs`, `types/module_view.rs`, `types/world.rs`, `types/btype.rs`, `types/type_marks.rs` | 3,000 each | JavaScript, stdlib and genType parity | **type checking at most 20,000 instructions per line on the application** | R8 | (a) and (b) no, (c) yes |
| R10 | Editor analysis on rows (THREE_TREES T12) | `types/{typedtree,tast_arena,tast_iterator,sexp_typedtree}.rs`, `tc/bridge/`, the switch | 3,000 | analysis tests | - | R9 | yes, arm by arm |

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

**The order is forced** except for two freedoms: R6a to R6f can be built in
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
   the bound (for example: at most 3 steps per element).
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
The bench must show each kernel operation within 25% of the table in
CHECKER_REWRITE 2.2; put its output in the pull request.

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

### 6.10 R7: the default flips

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

### 6.11 R8a to R8c: the explaining mode

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

### 6.12 R9a to R9c: readers on rows

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

### 6.13 R10: tooling, and the last deletions

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
