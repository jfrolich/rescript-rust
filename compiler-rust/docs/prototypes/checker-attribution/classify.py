#!/usr/bin/env python3
"""Attribute every instruction of a toggled callgrind profile of type checking
to one cost item and one kind of work.

  classify.py CALLGRIND_OUT BINARY SYMCACHE [--members N] [--json OUT]

An instruction address is resolved to its stack of inlined frames
(llvm-symbolizer --inlines). Its item is the innermost frame an item rule
matches; when none matches, the instruction inherits the item context of the
calls into its function (in proportion to their inclusive cost, iterated over
the call graph). Kinds work the same way but never inherit: an address with
no kind frame is "own".
"""
import sys, re, json, collections
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import cg

def norm_file(p):
    if '/compiler-rust/src/' in p: return 'src:' + p.split('/compiler-rust/src/', 1)[1]
    if '/rewatch/' in p: return 'rewatch:' + p.split('/rewatch/', 1)[1]
    if '/library/' in p: return 'std:' + p.split('/library/', 1)[1]
    m = re.search(r'(?:index\.crates\.io-[0-9a-f]+|/cargo/registry/[0-9a-f]+)/([A-Za-z0-9_\-]+?)-\d[\d\.]*/(.*)', p)
    if m: return 'crate:' + m.group(1) + '/' + m.group(2)
    return p

def base_name(fn):
    """Last named path segment of a demangled function, without generics."""
    s = fn
    # drop trailing generic argument lists
    depth = 0; out = []
    for ch in s:
        if ch == '<': depth += 1
        elif ch == '>': depth = max(0, depth - 1)
        elif depth == 0: out.append(ch)
    s = ''.join(out)
    segs = [x for x in s.split('::') if x and not x.startswith('{')]
    return segs[-1].strip() if segs else fn

# ---- item rules: (file regex, name regex, item). First match wins. ----
I = lambda f, n, item: (re.compile(f), re.compile(n), item)
ITEM_RULES = [
    # allocator proper
    I(r'^crate:libmimalloc-sys|^crate:mimalloc', r'.', 'ALLOC'),
    I(r'^src:types/ctype\.rs', r'^(mark_unified|take_unified_pairs|put_back_unified_pairs|already_unified|unified_pair_key|binding_facts|walk$|search$)', 'UNIFY'),
    # typed-tree environment recording belongs to the walk
    I(r'^src:types/context\.rs', r'^(store_typed_env)', 'WALK'),
    # loading dependency signatures: stored interfaces, views, the world
    I(r'^src:cmi/|^src:binser|^crate:serde|^src:types/(module_view|world|thread_store|unit_reads)\.rs|^src:module_registry|^src:registry', r'.', 'ENVLOAD'),
    I(r'^src:types/(typecore|typemod|ctype|context|env|env_lazy)\.rs', r'^(adopt_view|touch_store|replay_|build_in_store|poison_store|store_build|materialize|load_pervasives|import_|with_persistent|resolve_module_signature_through|find_cmi|force_entry|new_with_child_components|build_module_signature)', 'ENVLOAD'),
    # warnings and usage marking
    I(r'^src:types/usage\.rs|^src:warnings|^src:builtin_attributes|^src:types/builtin_attributes', r'.', 'WARN'),
    I(r'^src:types/(typecore|typemod|env|env_lazy|ctype|context)\.rs', r'^(mark_|check_deprecat|check_unused|unused_|warn_|add_delayed_check|record_.*_use|.*_used$|.*usage|drain_open_slot_uses|check_usage|attach_.*warning|warning_|is_warning|add_warning|prefixed_warning|warn$|report_unused)', 'WARN'),
    # error-path preparation on the success path
    I(r'^src:types/typecore\.rs', r'^(ClashSite|resolve$|TypeClashContext|clash_|with_explanation|expr_type_clash|type_clash_context|build_trace|make_clash)', 'ERRPREP'),
    I(r'^src:types/ctype\.rs', r'^(with_trace|record_trace_expansions|expand_trace)', 'ERRPREP'),
    I(r'^src:diagnostics', r'.', 'WARN'),
    I(r'^src:driver/type_clash|^src:types/errors|^src:types/printtyp', r'.', 'ERRPREP'),
    # the mutation journal (backtracking and restore on failure)
    I(r'^src:types/(context|ctype)\.rs', r'^(snapshot_type_state|TypeMutationSnapshot|TypeMutationJournal|record_type_mutation|restore_backtrack_state|snapshot_backtrack_state|backtrack|finish|TrailLogging|set_level_as_under_new_snapshot|update_logging|ActiveTypeSnapshot|log_|journal|commit_snapshot|rollback)', 'JOURNAL'),
    # abbreviations
    I(r'^src:types/(ctype|context|typecore|type_expr)\.rs', r'^(expand_head|try_expand_head|expand_abbrev|subst_with_memo|find_abbrev|read_abbrev|alloc_abbrev|write_abbrev|AbbrevMemo|safe_abbrev|full_expand|extract_concrete_typedecl|generic_abbrev|generic_private_abbrev|unroll_abbrev|proper_abbrevs|local_non_recursive_abbrev|has_cached_expansion|cyclic_abbrev|pdot_expansion|expands_to_datatype|simple_abbrev|forget_abbrev|cleanup_abbrev|memorize_abbrev|non_aliasable|is_contractive|manifest_decl|normalize_path_full|normalize_alias_target|normalize_module_path|force_normalize_path|type_expr_path_same|same_constr|a_type_path_is|module_path_exists_for)', 'EXPAND'),
    # substitution copies (Subst): signatures, looked-up items, path rewriting
    I(r'^src:', r'^(copy_lookup_|freshen|rewrite_type_expr_by_path|rewrite_type_paths|rewrite_.*path|replace_letmodule_local_paths|subst_for_saving|subst_norm|subst_type|subst_identity_copy|localize_|qualify_|strengthen_|nondep_|scrape_|subst_.*signature|substitute_|prefix_.*path|remap_label_type_to_params|record_label_param_subst)', 'SUBST'),
    I(r'^src:types/subst', r'.', 'SUBST'),
    # instantiation
    I(r'^src:types/(ctype|context|typecore)\.rs', r'^(instance|counted_instance|copy_type|copy_row|copy_sep|CopySession|begin_copy_session|end_copy_session|CopyCache|generic_instance|new_instance|instance_if_generic|copy_session|with_copy_session|fresh_instance|type_arg_nary_copy)', 'INST'),
    # levels and generalisation
    I(r'^src:types/(ctype|context|typecore|typemod)\.rs', r'^(update_level|generalize|lower$|lower_|level_update_is_plain|begin_def|end_def|closed_schema|iter_generalize|force_generalize|is_nonexpansive|nonexpansive|generalizable|enforce_constraints|try_enforce_constraints|init_def|reset_def|create_scope|raise_nongen|set_current_level|current_level|normalize_type|normalize_all_types|maybe_expansive|check_nongen|generalize_and_check|settle)', 'LEVEL'),
    # unification proper
    I(r'^src:types/(ctype|context)\.rs', r'^(unify|link_type|occur|deep_occur|surely_occur_free|surely_univar_free|reaches_quick|unified_pair_key|already_unified|moregen|moregeneral|equal|eqtype|matches|mcomp|rigidify|univars_unify|enter_poly|unify1|associate_fields|flatten_fields|merge_r|filter_method|filter_object|filter_visited|bound_conflicts|check_univars|add_univar|compute_univars|diff_bound|build_fields|sort_|object_row|component_same|is_instantiable|reify|add_gadt|set_type_desc|set_univar|filter_arrow|split_arrow|function_arity|is_function|subtype|enlarge|can_coerce|coerces_|pred_|push_subtype|force_subtype|variant_|primitive_coercion|same_record|check_record_fields|check_mutability|record_coercion|type_contains_variant|tuple_elements|extract_option|is_bool_or_unit|is_datatype|plain_type|apply$|arg_for)', 'UNIFY'),
    I(r'^src:types/typecore\.rs', r'^(unify_|filter_arrow|expand_head_for_arrow|finish_expected|unify_expression_types|unify_pat|unify_exp|type_approx|subtype_|type_coerce|coerce_)', 'UNIFY'),
    # disambiguation of constructors and labels
    I(r'^src:', r'^(disambiguate|NameChoice|wrap_disambiguate|lookup_all_|type_label_a|label_descrs|find_record|expected_.*path|extract_label|record_field_candidates|constructor_candidates|filter_.*candidates|lookup_from_type|disambiguate_label|disambiguate_constructor|typed_label_choice|constructors_of_type|labels_of_type|find_all_constructors|find_all_labels|lookup_label|lookup_constructor|lookup_all|best_label|best_constructor|unique_label|label_for|ambiguous|principal)', 'DISAMB'),
    # patterns and exhaustiveness
    I(r'^src:types/parmatch\.rs|^src:types/dict_pattern\.rs', r'.', 'PAT'),
    I(r'^src:types/typecore\.rs', r'^(type_pat|type_pattern|check_partial|check_unused_cases|iter_pattern|pattern_|pat_|add_pattern_variables|enter_variable|enter_orpat|build_or_pat|type_cases|type_match|check_absent|partial_pred|reset_pattern|sort_pattern|finalize_pattern|TypecoreParmatchOracle|TranslParmatchOracle|map_pattern|bound_idents|pattern_variables|check_scope_escape|split_cases|type_case)', 'PAT'),
    # type annotations in source
    I(r'^src:types/(typecore|typemod|typetexp)\.rs', r'^(transl_type$|transl_type_inner|transl_simple_type|transl_core_type|transl_type_scheme|transl_type_param|transl_fields|transl_.*core_type|new_pre_univar|make_fixed_univars|type_variable|globalize_used_variables|reset_type_variables|narrow|widen|TypeVariables|transl_poly|transl_object|transl_variant|transl_type_expr|approx_type)', 'TYPETEXP'),
    I(r'^src:types/typetexp', r'.', 'TYPETEXP'),
    # type and value declarations
    I(r'^src:types/(decl|variance|variant_layout|variant_runtime|record_runtime|external_ffi_types|derived|decl_loc|datarepr|typedecl|predef)\.rs|^src:frontend/|^src:ffi|^src:external', r'.', 'DECL'),
    I(r'^src:types/(typecore|typemod|ctype)\.rs', r'^(transl_type_decl|transl_declaration|transl_value_decl|transl_exception|transl_extension|transl_type_extension|transl_constructor|transl_label|check_well_founded|check_recursion|check_abbrev|check_constraints|check_coherence|compute_variance|compute_properties|update_decl|enter_type|name_recursion|check_regular|generalize_decl|type_declarations|typedecl_|approx_type_decl|check_duplicates|make_params|transl_with_constraint|compute_immediacy|marshal_|compute_unboxed|constructor_descrs|label_declaration|transl_primitive|parse_external|process_external|external_|type_external|datarepr|check_redefin|is_fixed_type|set_fixed_row|variant_runtime|instance_declaration|reified_type_decl|is_valid_hash|label_declaration_runtime_name)', 'DECL'),
    # environment, module paths, dependency signatures
    I(r'^src:types/(env|env_lazy|env_log)\.rs|^src:types/canonical_sig', r'.', 'ENV'),
    I(r'^src:types/(typecore|typemod|ctype|context)\.rs', r'^(lookup_|find_|env_|add_value|add_type|add_module|add_local|enter_value|enter_module|open_|build_module_signature|resolve_|store_typed_env|adopt_view|force_|with_env|type_open|module_path|components_of|expand_module_path|in_current_module|path_is_scoped|path_root_is_persistent|touch_store|replay_|build_in_store|poison_store|store_build|in_process_module_resolution|get_level_in_env|may_name_module|is_predef_type_name|initial_env|load_pervasives|materialize|register_|ensure_|get_components|cached_|with_persistent|import_|normalize_path_forward_only|normalize_path$)', 'ENV'),
    # modules, signatures, inclusion
    I(r'^src:types/(typemod|includemod|includecore|mtype|tast_iterator)\.rs', r'.', 'MOD'),
    I(r'^src:types/typecore\.rs', r'^(type_letmodule|type_module|type_pack|type_package|modtype_|type_letopen|type_open_|package_)', 'MOD'),
    # the walk: everything else of typecore, the typed tree
    I(r'^src:types/(typecore|typedtree|tast_arena|typeopt|sexp_typedtree)\.rs|^src:types/typecore/', r'.', 'WALK'),
    I(r'^src:types/ctype\.rs', r'.', 'UNIFY'),
    I(r'^src:driver', r'.', 'MOD'),
]
ITEMS = ['ENV', 'ENVLOAD', 'SUBST', 'INST', 'UNIFY', 'JOURNAL', 'LEVEL', 'EXPAND', 'WALK', 'PAT', 'TYPETEXP', 'DECL', 'MOD', 'DISAMB', 'WARN', 'ERRPREP', 'ALLOC', 'OTHER']

# ---- kind rules: (file regex, name regex, kind); innermost matching frame ----
KIND_RULES = [
    I(r'^crate:libmimalloc-sys|^crate:mimalloc|^std:alloc/src/alloc\.rs|^std:alloc/src/raw_vec|^std:core/src/alloc/', r'.', 'alloc'),
    I(r'^std:alloc/src/rcs/', r'.', 'rc'),
    I(r'^crate:hashbrown|^crate:ahash|^crate:im-rc|^crate:sized-chunks|^crate:bitmaps|^crate:rustc-hash|^crate:fxhash|^crate:indexmap|^std:core/src/hash/|^std:std/src/collections/hash|^src:fast_hash|^src:types/type_marks', r'.', 'hash'),
    I(r'^src:types/type_expr\.rs', r'^(TypeExprRefMap|insert|get$|record_new_key|record_item|probe|grow|rehash)', 'hash'),
    I(r'^src:types/path\.rs|^src:name\.rs|^src:ident\.rs', r'^(node_hash|mix|intern|hash|new$)', 'hash'),
    I(r'^src:types/context\.rs', r'^(snapshot_type_state|TypeMutationSnapshot|TypeMutationJournal|record_type_mutation|finish|TrailLogging|set_level_as_under_new_snapshot|update_logging|ActiveTypeSnapshot|drop$)', 'journal'),
    I(r'^src:types/context\.rs', r'^(direct|desc|get_level|repr|repr_chain|store_desc|store_level|borrow_desc|node|node_far|locate|set_desc|set_level|write_desc_raw|write_level_raw|level|eq|page|desc_indirect|level_indirect|frozen_|read_level|read_desc|type_list|type_args|slots|is_var|get_id)', 'node'),
    I(r'^src:types/shared_store\.rs|^src:types/thread_store\.rs', r'.', 'node'),
    I(r'^src:types/type_expr\.rs', r'^(is_store|untag|from_usize|slots|iter|next|locate|PoolIter|ListChunks|index|raw|is_shared|store_index|as_usize|get_slot|len)', 'node'),
    I(r'^std:core/src/cell\.rs|^std:core/src/cell/', r'.', 'cell'),
    I(r'^std:core/src/ptr/mod\.rs|^std:core/src/clone|^std:core/src/mem/mod\.rs|^std:core/src/intrinsics', r'^(copy_nonoverlapping|copy|write|read|drop_glue|drop_in_place|clone|clone_from|write_bytes|swap|replace)', 'copy'),
    I(r'^std:alloc/src/(vec|slice|string|boxed|str)', r'^(clone|to_vec|to_owned|extend_from_slice|from_iter|to_string|from|clone_from|append_elements|drop|into_boxed_slice|spec_extend|extend|collect|with_capacity|push|reserve|truncate)', 'copy'),
    I(r'^crate:smallvec|^crate:smol_str', r'.', 'copy'),
    I(r'^src:', r'^(clone|drop|drop_glue)$', 'copy'),
]
KINDS = ['alloc', 'copy', 'rc', 'hash', 'node', 'cell', 'journal', 'own']

ALLOC_INHERIT = '--alloc-inherit' in sys.argv

def libc_kind(fn):
    if re.match(r'(__)?(mem(cpy|move|set|cmp)|bcmp|str)', fn): return 'copy'
    if re.match(r'(malloc|free|calloc|realloc|_int_|sys|mmap|munmap|madvise|brk)', fn): return 'alloc'
    return 'own'

_cache_i = {}
def frame_item(fn, fl):
    k = (fn, fl)
    if k in _cache_i: return _cache_i[k]
    b = base_name(fn); r = None
    full = fn
    for fre, nre, item in ITEM_RULES:
        if item == 'ALLOC' and ALLOC_INHERIT: continue
        if fre.search(fl) and (nre.search(b) or (nre.pattern != '.' and any(nre.search(seg) for seg in re.split(r'::|<|>| ', full) if seg))):
            r = item; break
    _cache_i[k] = r
    return r

_cache_k = {}
def frame_kind(fn, fl):
    k = (fn, fl)
    if k in _cache_k: return _cache_k[k]
    b = base_name(fn); r = None
    for fre, nre, kind in KIND_RULES:
        if fre.search(fl) and nre.search(b):
            r = kind; break
    _cache_k[k] = r
    return r

def main():
    out, binary, cache = sys.argv[1:4]
    members_n = int(sys.argv[sys.argv.index('--members') + 1]) if '--members' in sys.argv else 0
    json_out = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else None
    sc, arcs, summary = cg.load(out)
    binname = binary.rsplit('/', 1)[-1]
    is_main = lambda ob: ob.rsplit('/', 1)[-1] == binname
    addrs = set()
    for (ob, fn), m in sc.items():
        if is_main(ob): addrs.update(m)
    for (caller, a, callee, c) in arcs:
        if is_main(caller[0]): addrs.add(a)
    sym = cg.symbolize(binary, addrs, cache)

    def addr_class(ob, fn, a):
        """-> (item or None, kind, member frame, outer_item or None)"""
        if not is_main(ob):
            if 'libc' in ob:
                return None, libc_kind(fn), (fn, 'libc'), None
            return None, 'own', (fn, ob.rsplit('/', 1)[-1]), None
        frames = sym.get(a) or [(fn, '', 0)]
        item = None; kind = None; member = None; outer = None
        for (f, fl, _ln) in frames:
            nf = norm_file(fl)
            if kind is None:
                kind = frame_kind(f, nf)
            it = frame_item(f, nf)
            if it is not None:
                if item is None:
                    item = it; member = (base_name(f), nf)
                elif it != item and outer is None:
                    outer = it
        if member is None:
            f, fl, _ = frames[0]
            member = (base_name(f), norm_file(fl))
        return item, kind or 'own', member, outer

    # per function: classified self cost, and inherit bucket
    fn_inherit = collections.defaultdict(lambda: collections.Counter())   # fn -> kind -> cost needing item
    cell = collections.Counter()      # (item, kind) -> cost
    members = collections.defaultdict(collections.Counter)  # item -> member -> cost
    inh_members = collections.defaultdict(collections.Counter)  # fn -> member -> cost (inherit)
    total = 0
    for (ob, fn), m in sc.items():
        for a, c in m.items():
            if not c: continue
            total += c
            item, kind, member, _ = addr_class(ob, fn, a)
            if item is None:
                fn_inherit[(ob, fn)][kind] += c
                inh_members[(ob, fn)][member] += c
            else:
                cell[(item, kind)] += c
                members[item][member] += c
    # contexts: ctx[f] = distribution over items of the call sites into f
    into = collections.defaultdict(list)   # callee -> [(caller, fixed_item or None, weight)]
    for (caller, a, callee, c) in arcs:
        if c <= 0 or caller == callee: continue
        item, _, _, _ = addr_class(caller[0], caller[1], a)
        into[callee].append((caller, item, c))
    fns = set(sc) | set(into)
    ctx = {f: {} for f in fns}
    for _ in range(60):
        new = {}
        for f in fns:
            d = collections.Counter(); w = 0
            for (caller, item, c) in into.get(f, ()):
                if item is not None:
                    d[item] += c; w += c
                else:
                    cc = ctx.get(caller) or {}
                    s = sum(cc.values())
                    if s > 0:
                        for it, v in cc.items(): d[it] += c * v / s
                        w += c
            new[f] = {it: v / w for it, v in d.items()} if w else {}
        ctx = new
    inherited = 0
    for f, kinds in fn_inherit.items():
        d = ctx.get(f) or {}
        tot_f = sum(kinds.values())
        if not d:
            d = {'OTHER': 1.0}
        inherited += tot_f
        for it, share in d.items():
            for kind, c in kinds.items():
                cell[(it, kind)] += c * share
            for mem, c in inh_members[f].items():
                members[it][('~' + mem[0], mem[1])] += c * share
    # report
    print(f'total {total}  summary {summary}  inherited by proportional rule {inherited/total*100:.1f}%')
    item_tot = collections.Counter(); kind_tot = collections.Counter()
    for (it, k), c in cell.items(): item_tot[it] += c; kind_tot[k] += c
    print('item      ' + ''.join(f'{k:>9}' for k in KINDS) + '      all        M')
    for it in ITEMS:
        print(f'{it:10}' + ''.join(f'{cell[(it,k)]/total*100:8.2f}%' for k in KINDS) + f'{item_tot[it]/total*100:8.2f}% {item_tot[it]/1e6:9.1f}')
    print(f'{"all":10}' + ''.join(f'{kind_tot[k]/total*100:8.2f}%' for k in KINDS) + f'{sum(item_tot.values())/total*100:8.2f}%')
    if members_n:
        for it in ITEMS:
            print(f'--- {it} {item_tot[it]/total*100:.2f}%')
            for (mem, fl), c in members[it].most_common(members_n):
                print(f'   {c/total*100:6.2f}%  {mem[:70]}  [{fl[-60:]}]')
    if json_out:
        json.dump({'total': total, 'cell': {f'{it}|{k}': c for (it, k), c in cell.items()},
                   'members': {it: [[m[0], m[1], c] for m, c in members[it].most_common(60)] for it in ITEMS}}, open(json_out, 'w'))

if __name__ == '__main__':
    main()
