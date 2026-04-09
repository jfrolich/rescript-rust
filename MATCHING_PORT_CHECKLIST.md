# matching.ml Port Checklist

Port of OCaml's `compiler/ml/matching.ml` (2978 lines, 201 functions) to Rust.
Target: `compiler-rust/src/raw_lambda/matching.rs`

Current parity: 510/657 (78%). ~90 of 147 remaining failures are from matching differences.

## Layer 1: Core Types and Context (lines 26-344)

### Types
- [ ] `matrix` type (line 62) — `pattern list list`
- [ ] `ctx` type (line 66) — `{left: pattern list; right: pattern list}`
- [ ] `jumps` type (line 276) — `(int * ctx list) list`
- [ ] `pattern_matching` type (line 348) — `{cases; args; default}`
- [ ] `pm_or_compiled` type (line 357)
- [ ] `pm_half_compiled` type (line 363)
- [ ] `pm_half_compiled_info` type (line 370)

### Context operations
- [ ] `le_ctx` (line 78)
- [ ] `lshift` (line 80)
- [ ] `lforget` (line 85)
- [ ] `small_enough` (line 90)
- [ ] `ctx_lshift` (line 94)
- [ ] `rshift` (line 98)
- [ ] `ctx_rshift` (line 103)
- [ ] `nchars` (line 105)
- [ ] `rshift_num` (line 114)
- [ ] `ctx_rshift_num` (line 118)
- [ ] `combine` (line 124)
- [ ] `ctx_combine` (line 129)
- [ ] `ncols` (line 131)

### Matrix operations
- [ ] `add_omega_column` (line 64)
- [ ] `filter_matrix` (line 138)
- [ ] `make_default` (line 159)
- [ ] `ctx_matcher` (line 172)
- [ ] `filter_ctx` (line 229)
- [ ] `select_columns` (line 252)
- [ ] `ctx_lub` (line 263)
- [ ] `ctx_match` (line 271)

### Jump operations
- [ ] `jumps_extract` (line 288)
- [ ] `jumps_remove` (line 297)
- [ ] `jumps_empty` (line 302)
- [ ] `jumps_is_empty` (line 304)
- [ ] `jumps_singleton` (line 308)
- [ ] `jumps_add` (line 312)
- [ ] `jumps_union` (line 325)
- [ ] `merge` (line 334)
- [ ] `jumps_unions` (line 338)
- [ ] `jumps_map` (line 344)

## Layer 2: Catch/Exit and Action Sharing (lines 442-578)

- [ ] `StoreExp` module (line 442) — action deduplication store
- [ ] `make_exit` (line 449)
- [ ] `make_catch` (line 452)
- [ ] `as_simple_exit` (line 460)
- [ ] `make_catch_delayed` (line 465)
- [ ] `raw_action` (line 479)
- [ ] `tr_raw` (line 484)
- [ ] `same_actions` (line 489)
- [ ] `up_ok_action` (line 504)
- [ ] `up_ok` (line 510)
- [ ] `simplify_or` (line 526)
- [ ] `simplify_cases` (line 546)
- [ ] `what_is_cases` (line 578)

## Layer 3: Default Environments and Or-patterns (lines 589-653)

- [ ] `as_matrix` (line 589)
- [ ] `cons_default` (line 591)
- [ ] `default_compat` (line 596)
- [ ] `extract_vars` (line 613)
- [ ] `mk_alpha_env` (line 628)
- [ ] `explode_or_pat` (line 639)
- [ ] `pm_free_variables` (line 653)

## Layer 4: Grouping and Splitting (lines 659-1090)

### Group predicates
- [ ] `pat_as_constr` (line 659)
- [ ] `group_constant` (line 663)
- [ ] `group_constructor` (line 667)
- [ ] `group_variant` (line 671)
- [ ] `group_var` (line 675)
- [ ] `group_tuple` (line 679)
- [ ] `group_record` (line 683)
- [ ] `group_array` (line 687)
- [ ] `get_group` (line 691)
- [ ] `is_or` (line 702)

### Or-pattern operations
- [ ] `conda` (line 708)
- [ ] `condb` (line 710)
- [ ] `or_ok` (line 712)
- [ ] `equiv_pat` (line 721)
- [ ] `get_equiv` (line 723)
- [ ] `insert_or_append` (line 732)

### Split functions
- [ ] `rebuild_matrix` (line 777)
- [ ] `rebuild_default` (line 783)
- [ ] `rebuild_nexts` (line 789)
- [ ] `split_or` (line 814)
- [ ] `split_naive` (line 846)
- [ ] `split_constr` (line 910)
- [ ] `precompile_var` (line 979)
- [ ] `dont_precompile_var` (line 1017)
- [ ] `precompile_or` (line 1025)
- [ ] `split_precompile` (line 1077)

## Layer 5: General Divide Functions (lines 1094-1122)

- [ ] `add_line` (line 1094)
- [ ] `add` (line 1100)
- [ ] `divide` (line 1110)
- [ ] `divide_line` (line 1122)

## Layer 6: Per-type Pattern Matchers (lines 1148-1515)

### Constants
- [ ] `matcher_const` (line 1148)
- [ ] `get_key_constant` (line 1156)
- [ ] `get_args_constant` (line 1163)
- [ ] `make_constant_matching` (line 1165)
- [ ] `divide_constant` (line 1172)

### Constructors
- [ ] `make_field_args` (line 1180)
- [ ] `get_key_constr` (line 1189)
- [ ] `get_args_constr` (line 1193)
- [ ] `matcher_constr` (line 1205)
- [ ] `make_constr_matching` (line 1249)
- [ ] `divide_constructor` (line 1287)

### Variants (polymorphic)
- [ ] `matcher_variant_const` (line 1293)
- [ ] `make_variant_matching_constant` (line 1302)
- [ ] `matcher_variant_nonconst` (line 1309)
- [ ] `make_variant_matching_nonconst` (line 1316)
- [ ] `divide_variant` (line 1334)

### Variables
- [ ] `get_args_var` (line 1370)
- [ ] `make_var_matching` (line 1372)
- [ ] `divide_var` (line 1377)

### Tuples
- [ ] `get_args_tuple` (line 1382)
- [ ] `matcher_tuple` (line 1388)
- [ ] `make_tuple_matching` (line 1395)
- [ ] `divide_tuple` (line 1410)

### Records
- [ ] `record_matching_line` (line 1417)
- [ ] `get_args_record` (line 1422)
- [ ] `matcher_record` (line 1429)
- [ ] `make_record_matching` (line 1439)
- [ ] `divide_record` (line 1472)

### Arrays
- [ ] `get_key_array` (line 1480)
- [ ] `get_args_array` (line 1484)
- [ ] `matcher_array` (line 1489)
- [ ] `make_array_matching` (line 1496)
- [ ] `divide_array` (line 1515)

## Layer 7: String Matching (lines 1532-1657)

- [ ] `strings_test_threshold` (line 1532)
- [ ] `bind_sw` (line 1534)
- [ ] `make_string_test_sequence` (line 1543)
- [ ] `split` (line 1561)
- [ ] `zero_lam` (line 1570)
- [ ] `tree_way_test` (line 1572)
- [ ] `do_make_string_test_tree` (line 1580)
- [ ] `expand_stringswitch` (line 1595)
- [ ] `handle_shared` (line 1609)
- [ ] `share_actions_tree` (line 1622)
- [ ] `uniq_lambda_list` (line 1650)
- [ ] `sort_lambda_list` (line 1657)

## Layer 8: Integer/Switch Matching (lines 1661-1941)

- [ ] `cut` (line 1661)
- [ ] `do_tests_fail` (line 1670)
- [ ] `do_tests_nofail` (line 1678)
- [ ] `make_test_sequence` (line 1687)
- [ ] `SArg` module (line 1708) — Switch module arguments
- [ ] `Switcher` module instantiation (line 1835)
- [ ] `share_actions_sw` (line 1761) — ALREADY PORTED
- [ ] `reintroduce_fail` (line 1795)
- [ ] `last` (line 1838)
- [ ] `get_edges` (line 1843)
- [ ] `as_interval_canfail` (line 1848)
- [ ] `as_interval_nofail` (line 1898)
- [ ] `sort_int_lambda_list` (line 1929)
- [ ] `as_interval` (line 1934)
- [ ] `call_switcher` (line 1941) — ALREADY PORTED (switch.rs)

## Layer 9: Combine Functions (lines 1945-2349)

- [ ] `list_as_pat` (line 1945)
- [ ] `complete_pats_constrs` (line 1950)
- [ ] `mk_failaction_neg` (line 1961)
- [ ] `mk_failaction_pos` (line 1975)
- [ ] `combine_constant` (line 2022)
- [ ] `split_cases` (line 2072)
- [ ] `split_variant_cases` (line 2087)
- [ ] `get_extension_cases` (line 2101)
- [ ] `combine_constructor` (line 2112)
- [ ] `make_test_sequence_variant_constant` (line 2213)
- [ ] `call_switcher_variant_constant` (line 2220)
- [ ] `call_switcher_variant_constr` (line 2225)
- [ ] `combine_variant` (line 2264)
- [ ] `combine_array` (line 2319)

## Layer 10: Compile Functions (lines 2351-2606)

- [ ] `compile_list` (line 2351)
- [ ] `compile_orhandlers` (line 2368)
- [ ] `compile_test` (line 2392)
- [ ] `approx_present` (line 2405)
- [ ] `lower_bind` (line 2413) — PARTIALLY PORTED (record field ordering)
- [ ] `bind_check` (line 2437)
- [ ] `comp_exit` (line 2443)
- [ ] `comp_match_handlers` (line 2448)
- [ ] `name_pattern` (line 2486)
- [ ] `arg_to_var` (line 2493)
- [ ] `names_from_construct_pattern` (line 2501)
- [ ] `compile_match` (line 2516) — THE CORE RECURSIVE COMPILER
- [ ] `do_compile_matching` (line 2554)
- [ ] `compile_no_test` (line 2606)

## Layer 11: Entry Points (lines 2631-2974)

- [ ] `find_in_pat` (line 2631)
- [ ] `have_mutable_field` (line 2647)
- [ ] `is_mutable` (line 2660)
- [ ] `check_partial` (line 2667)
- [ ] `start_ctx` (line 2685)
- [ ] `check_total` (line 2687)
- [ ] `compile_matching` (line 2691)
- [ ] `partial_function` (line 2719)
- [ ] `for_function` (line 2743)
- [ ] `for_trywith` (line 2747)
- [ ] `simple_for_let` (line 2752)
- [ ] `for_let` (line 2803)
- [ ] `for_tupled_function` (line 2817)
- [ ] `flatten_pattern` (line 2835)
- [ ] `flatten_pat_line` (line 2841)
- [ ] `flatten_cases` (line 2852)
- [ ] `flatten_matrix` (line 2860)
- [ ] `flatten_def` (line 2868)
- [ ] `flatten_pm` (line 2871)
- [ ] `flatten_precompiled` (line 2878)
- [ ] `compile_flattened` (line 2898)
- [ ] `do_for_multiple_match` (line 2906)
- [ ] `param_to_var` (line 2964)
- [ ] `bind_opt` (line 2969)
- [ ] `for_multiple_match` (line 2974)

## Already Ported (in other files)
- [x] `share_actions_sw` — in convert.rs (action key normalization)
- [x] `Switch` module — in switch.rs (comparison tree generation)
- [x] `lower_bind` ordering — in convert.rs (record field extraction order)
- [x] `*sth*` elimination — in convert.rs (optional parameter optimization)
