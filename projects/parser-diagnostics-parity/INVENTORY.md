# OCaml Parser Diagnostics Inventory

Inventory date: **May 14, 2026**

Scope scanned:

- `compiler/syntax/src/res_diagnostics.ml`
- `compiler/syntax/src/res_scanner.ml`
- `compiler/syntax/src/res_parser.ml`
- `compiler/syntax/src/res_core.ml`
- `compiler/syntax/src/jsx_v4.ml`
- `compiler/syntax/src/jsx_common.ml`
- `compiler/ml/location.ml`
- `compiler/frontend/bs_ast_invariant.ml`
- `compiler/ml/typedecl.ml`
- `compiler/ml/typetexp.ml`
- `compiler/ml/typemod.ml`
- `compiler/ml/typecore.ml`
- `compiler/ml/ctype.ml`
- `compiler/ml/printtyp.ml`
- `compiler/ml/variant_coercion.ml`
- `compiler/ml/record_coercion.ml`
- `compiler/ml/ast_untagged_variants.ml`
- `compiler/frontend/bs_syntaxerr.ml`
- `compiler/frontend/ast_attributes.ml`
- `compiler/ml/ast_payload.ml`
- `compiler/frontend/bs_builtin_ppx.ml`
- `compiler/frontend/ast_exp_handle_external.ml`
- `compiler/frontend/ast_exp_extension.ml`
- `compiler/frontend/typemod_hide.ml`
- `compiler/ml/env.ml`
- `compiler/ml/transl_recmodule.ml`
- `compiler/core/lam_compile_primitive.ml`

## 1. Core Diagnostic Model

Canonical parser diagnostic categories are defined in
`compiler/syntax/src/res_diagnostics.ml:4`:

1. `Unexpected`
2. `Expected`
3. `Message`
4. `Uident`
5. `Lident`
6. `UnclosedString`
7. `UnclosedTemplate`
8. `UnclosedComment`
9. `UnknownUchar`

Formatting and message specialization pipeline:

- category-to-text logic: `compiler/syntax/src/res_diagnostics.ml:39`
- contextual special-case hints (array literal + removed `|>` guidance): `compiler/syntax/src/res_diagnostics.ml:134`
- final render entrypoint through `Location.report_error`: `compiler/syntax/src/res_diagnostics.ml:171`

## 2. Scanner Lexical Diagnostics

Primary lexical diagnostics are emitted in `compiler/syntax/src/res_scanner.ml`.

Literal scanner messages:

1. `Expected digits after exponential notation.` (`:290`)
2. `A quoted identifier can't contain line breaks.` (`:323`)
3. `Did you forget a " here?` (`:328`)
4. `A quoted identifier can't be empty string.` (`:343`)
5. `unterminated regex` (`:607`)

The unclosed quoted identifier EOF path is covered by
`tests/syntax_tests/data/parsing/errors/scanner/unclosedExoticIdentifier.res`.
That fixture has no final newline because the OCaml branch only fires when the
scanner reaches EOF before a line break.

Category-based scanner diagnostics:

1. `Diagnostics.unclosed_string` (`:463`)
2. `Diagnostics.unclosed_comment` (`:672`)
3. `Diagnostics.unclosed_template` (`:732`)
4. `Diagnostics.unknown_uchar` (`:1031`)
5. dynamic `Diagnostics.message msg` for escape-sequence problems (`:361`, `:371`, `:415`)

The escape-sequence dynamic messages are covered by
`tests/syntax_tests/data/parsing/errors/scanner/invalidEscapeSequence.res`,
which triggers both `unknown escape sequence` and
`escape sequence is invalid unicode code point`.

The OCaml scanner treats any standalone backslash as the start of exotic
identifier recovery (`scan_exotic_identifier`), not only `\"`. The recovered
JS-string escape path is covered by
`tests/error_output_parity/compiler/fixtures/parser_js_string_invalid_escape_recovery.res`.

## 3. Parser Grammar Diagnostics (`res_core.ml`)

Main parser diagnostic emission uses `Parser.err` + `Diagnostics.*`.
Observed count of diagnostics callsites in `res_core.ml`: **118**.

### 3.1 Named parser error-message catalog

`compiler/syntax/src/res_core.ml:68` (`module ErrorMessages`) defines parser-specific message templates used throughout grammar parsing.

Used catalog entries (31):

1. `array_pattern_spread`
2. `attribute_without_node`
3. `dict_expr_spread`
4. `dict_field_missing_colon`
5. `experimental_if_let`
6. `experimental_let_unwrap_rec`
7. `experimental_let_unwrap_sig`
8. `forbidden_inline_record_declaration`
9. `keyword_field_in_expr`
10. `keyword_field_in_pattern`
11. `keyword_field_in_type`
12. `labelled_argument_missing_equal`
13. `list_pattern_spread`
14. `missing_tilde_labeled_parameter`
15. `multiple_inline_record_definitions_at_same_path`
16. `object_quoted_field_name`
17. `optional_labelled_argument_missing_equal`
18. `poly_var_int_with_suffix`
19. `record_expr_spread`
20. `record_field_missing_colon`
21. `record_pattern_field_missing_colon`
22. `record_pattern_spread`
23. `record_type_field_missing_colon`
24. `spread_children_no_longer_supported`
25. `string_interpolation_in_pattern`
26. `tuple_single_element`
27. `type_declaration_name_longident`
28. `type_definition_in_function`
29. `type_param`
30. `type_var`
31. `variant_ident`

### 3.2 Direct string diagnostics (non-catalog)

Examples of direct literal parser messages in `res_core.ml`:

1. `Did you mean \`==\` here?` (`compiler/syntax/src/res_core.ml:489`)
2. `JSX identifier cannot end with a hyphen` (`compiler/syntax/src/res_core.ml:844`)
3. `expected identifier after '.' in JSX tag name` (`compiler/syntax/src/res_core.ml:894`)
4. `Did you forget a \`</\` here?` (`compiler/syntax/src/res_core.ml:2821`)
5. `JSX prop names must be lowercase` (`compiler/syntax/src/res_core.ml:2991`)
6. `Pattern matching needs at least one case` (`compiler/syntax/src/res_core.ml:3875`)
7. `A jsx name must be a lowercase or uppercase name...`
   (`compiler/syntax/src/res_core.ml:2852`)

The lower-case JSX closing-name mismatch recovery path is covered by
`tests/syntax_tests/data/parsing/errors/expressions/jsxClosingMismatch.res`.
This complements the existing uppercase/qualified mismatch cases in
`tests/syntax_tests/data/parsing/errors/expressions/jsx.res`.

The `Closing jsx name should be the same as the opening name...` fallback is
covered by
`tests/syntax_tests/data/parsing/errors/expressions/jsxClosingEmptyName.res`,
which reaches the `</` with no following identifier branch.

The invalid JSX tag-name fallback is covered through the direct compiler
fixture `tests/error_output_parity/compiler/fixtures/parser_jsx_bad_name_number.res`.
It is not a numbered parser-matrix case because OCaml's
`res_parser -recover -print ml` emits the diagnostics and then crashes while
printing the recovered raw tree for `<1 />`; the `bsc` path compares the
user-facing parser diagnostics without that recovered-printer crash.

Dynamic parser messages also exist (`"Missing " ^ closing`, keyword escapes, etc.).

Record spread recovery has two distinct branches:
`tests/syntax_tests/data/parsing/errors/expressions/recordSpreadMissingComma.res`
covers the missing comma after a spread (`{...record}`), while
`tests/error_output_parity/compiler/fixtures/parser_record_spread_no_update.res`
covers the explicit trailing comma no-update message (`{...record,}`).

The `for await`/`in` parser diagnostic is covered by
`tests/syntax_tests/data/parsing/errors/expressions/forAwaitIn.res`.
The `for...of` destructuring-pattern diagnostic is covered by
`tests/syntax_tests/data/parsing/errors/expressions/for_of_pattern.res`.

The signature-only consecutive-specification diagnostic is covered by
`tests/syntax_tests/data/parsing/errors/signature/consecutive.resi`.

The non-decimal bigint literal diagnostic from `parse_constant` is covered by
`tests/syntax_tests/data/parsing/errors/scanner/invalidBigint.res`.

## 4. JSX Warning/Error Surface

### 4.1 Warning emission

Parser-path warning emission sites in `compiler/syntax/src`: **1**

- `compiler/syntax/src/jsx_v4.ml:271`
  - `Location.prerr_warning ... (Preprocessor "...optional argument annotations must have explicit option...")`
  - This is the Warning 22 parity path currently snapshot-tested.

### 4.2 JSX parser-time errors

JSX parser/transform error raises in `compiler/syntax/src/jsx_v4.ml`: **16** sites using
`Jsx_common.raise_error` or `Location.raise_errorf`.

Representative messages:

1. `JSX component calls cannot be destructured.` (`:66`, `:80`)
2. `Key cannot be accessed inside of a component...` (`:252`)
3. `React: react.component refs only support plain arguments...` (`:334`)
4. `React: props need to be labelled arguments...` (`:461`)
5. `Components using React.forwardRef cannot use @react.componentWithProps...` (`:839`)
6. `Only one JSX component call can exist on a component at one time` (`:1001`, `:1090`)
7. `JSX: use {...p} {x: v} not {x: v} {...p} ...` (`:1160`)
8. `JSX: element name is neither upper- or lowercase...` (`:1324`, `:1349`)

Shared helper:

- `compiler/syntax/src/jsx_common.ml:45` (`raise_error`)

## 5. Compiler Type Declaration Diagnostics

The nonrecursive GADT diagnostic has two reference checks with different
messages and locations:

1. `compiler/frontend/bs_ast_invariant.ml:81-90`
   - structure-only frontend invariant
   - matches `Pstr_type (Nonrecursive, [{ptype_kind = Ptype_variant ({pcd_res = Some _} :: _)}])`
   - reports at the whole structure item with `GADTs require recursive type syntax...`
   - covered by `tests/error_output_parity/compiler/fixtures/nonrec_gadt.res`
2. `compiler/ml/typedecl.ml:80-89`
   - `Typedecl.enter_type` check for all nonrecursive variant constructors
   - raises `Typedecl.Nonrec_gadt` at the constructor declaration location
   - covered by `tests/error_output_parity/compiler/fixtures/nonrec_gadt_later_constructor.res`
   - signature path covered by `tests/error_output_parity/compiler/fixtures/nonrec_gadt_signature.resi`

Rust must preserve both checks. Broadening the frontend invariant would produce
the wrong reference output for later constructors and signatures.

`Typedecl.Unavailable_type_constructor` reachability note:

- OCaml can raise this only from defensive `Not_found` branches in
  `compiler/ml/typedecl.ml:767-785` (`check_constraints_rec`) and
  `compiler/ml/typedecl.ml:862-886` (`check_coherence`).
- Both branches run after type translation has already resolved the
  constructor path in the same environment, so ordinary ReScript source should
  report the earlier unbound-type diagnostic instead of this constructor.
- A recursive equation probe (`type rec t = u = A and u = A`) reaches the
  duplicate-constructor warning path, not `Unavailable_type_constructor`.
- No direct ReScript source fixture is currently known that reaches this
  diagnostic without constructing an inconsistent or stale typed environment.

### 5.1 Type Expression Diagnostics

`compiler/ml/typetexp.ml:28-55` defines the finite type-expression error
constructor set used by type paths, package types, polymorphic variants,
object types, and narrowed unbound identifier reporting. Coverage now includes:

1. `Typetexp.Unbound_type_variable`
   - covered by `tests/error_output_parity/compiler/fixtures/unbound_type_variable.res`
   - fixed/wildcard and nested manifest paths are covered by
     `unbound_type_variable_wildcard.res`, `unbound_type_var_alias.res`, and
     `unbound_type_var_record.res`
2. `Typetexp.Unbound_type_constructor`
   - covered by `tests/error_output_parity/compiler/fixtures/unbound_type_constructor.res`
   - spellcheck and qualified-prefix narrowing are covered by
     `unbound_type_constructor_spellcheck.res` and
     `unbound_type_constructor_parent_module.res`
3. `Typetexp.Unbound_type_constructor_2`
   - covered by
     `tests/error_output_parity/compiler/fixtures/unbound_type_constructor_incomplete.res`
4. `Typetexp.Type_arity_mismatch`
   - covered by `tests/error_output_parity/compiler/fixtures/type_arity_mismatch.res`
     and the non-generic zero-arity branch in
     `type_arity_mismatch_nongeneric.res`
5. `Typetexp.Type_mismatch`
   - covered by `tests/error_output_parity/compiler/fixtures/typetexp_type_mismatch.res`
6. `Typetexp.Alias_type_mismatch`
   - covered by
     `tests/error_output_parity/compiler/fixtures/typetexp_alias_type_mismatch.res`
7. `Typetexp.Present_has_conjunction`
   - covered by
     `tests/error_output_parity/compiler/fixtures/present_variant_has_conjunction.res`
8. `Typetexp.Present_has_no_type`
   - covered by
     `tests/error_output_parity/compiler/fixtures/present_variant_has_no_type.res`
9. `Typetexp.Constructor_mismatch`
   - covered by
     `tests/error_output_parity/compiler/fixtures/polyvariant_constructor_mismatch.res`
10. `Typetexp.Not_a_variant`
    - covered by `tests/error_output_parity/compiler/fixtures/typetexp_not_a_variant.res`
      and the type-variable hint branch in
      `typetexp_not_a_variant_type_var_hint.res`
11. `Typetexp.Variant_tags`
    - covered by `tests/error_output_parity/compiler/fixtures/variant_tags_collision.res`
12. `Typetexp.Invalid_variable_name`
    - covered by
      `tests/error_output_parity/compiler/fixtures/invalid_type_variable_name.res`
      and the type-parameter path in `invalid_type_parameter_name.res`
13. `Typetexp.Cannot_quantify`
    - covered by `cannot_quantify_alias.res`, `cannot_quantify_already_bound.res`,
      and `cannot_quantify_escapes_scope.res`
14. `Typetexp.Multiple_constraints_on_type`
    - covered by
      `tests/error_output_parity/compiler/fixtures/multiple_constraints_on_package_type.res`
15. `Typetexp.Method_mismatch`
    - covered by `tests/error_output_parity/compiler/fixtures/typetexp_method_mismatch.res`
16. `Typetexp.Unbound_value`
    - covered by `unbound_value.res`, with spellcheck/module-name suggestion
      branches covered by `unbound_value_spellcheck.res`,
      `unbound_value_module_suggestion.res`, and
      `unbound_value_spellcheck_and_module_suggestion.res`
17. `Typetexp.Unbound_constructor`
    - covered by `unbound_constructor.res`, `unbound_constructor_qualified.res`,
      `unbound_constructor_spellcheck.res`, and the payload-location branch in
      `unbound_constructor_payload_loc.res`
18. `Typetexp.Unbound_label`
    - covered by `unbound_label.res`, plus receiver-specific branches in
      `unbound_label_option_receiver.res`, `unbound_label_array_receiver.res`,
      and `unbound_label_non_record_receiver.res`
19. `Typetexp.Unbound_module`
    - covered by `unbound_module.res`, `unbound_module_spellcheck.res`,
      `unbound_module_str.res`, `module_alias_unbound_module.res`,
      `module_type_of_unbound_module.res`, `module_type_alias_unbound_module.res`,
      `with_module_unbound_module.res`, and
      `with_module_equation_unbound_module.res`
20. `Typetexp.Unbound_modtype`
    - covered by `unbound_modtype.res`, `unbound_modtype_qualified.res`,
      `unbound_modtype_spellcheck.res`, and `signature_unbound_modtype.res`
21. `Typetexp.Ill_typed_functor_application`
    - covered by
      `tests/error_output_parity/compiler/fixtures/ill_typed_functor_application_type_path.res`
22. `Typetexp.Illegal_reference_to_recursive_module`
    - covered by
      `tests/error_output_parity/compiler/fixtures/illegal_reference_to_recursive_module.res`
23. `Typetexp.Access_functor_as_structure`
    - covered by
      `tests/error_output_parity/compiler/fixtures/access_functor_as_structure.res`
24. `Typetexp.Apply_structure_as_functor`
    - covered by
      `tests/error_output_parity/compiler/fixtures/apply_structure_as_functor_type_path.res`
25. `Typetexp.Cannot_scrape_alias`
    - covered by
      `tests/error_output_parity/compiler/cases/cannot_scrape_alias_type_path.res`
    - this comes from `typetexp.ml:68-103`, where narrowed unbound identifier
      reporting checks a module prefix and finds an alias whose target `.cmi` is
      missing; the paired `Typemod.Cannot_scrape_alias` case is
      `cannot_scrape_alias_module_type_with.res`
    - focused parity check:
      `TIMEOUT_SECONDS=10 ./scripts/test_error_output_parity.sh --compiler-only cannot_scrape_alias`
      passes 2/2
26. `Typetexp.Opened_object`
    - covered by `tests/error_output_parity/compiler/fixtures/typetexp_opened_object.res`
27. `Typetexp.Not_an_object`
    - covered by `tests/error_output_parity/compiler/fixtures/typetexp_not_an_object.res`

The `Cannot_scrape_alias` coverage uses `tests/error_output_parity/compiler/cases.tsv`
because the fixture requires an intentionally missing compiled module alias
environment under `tests/error_output_parity/compiler/cases/missing_module_cmis`.

### 5.2 Module Typing Diagnostics

`compiler/ml/typemod.ml:24-47` defines the finite module-typing error
constructor set. Coverage now includes:

1. `Typemod.Cannot_apply`
   - covered by `tests/error_output_parity/compiler/fixtures/cannot_apply_module.res`
2. `Typemod.Not_included`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_value_mismatch.res`
   - functor-argument mismatch coverage is
     `tests/error_output_parity/compiler/fixtures/functor_argument_mismatch.res`
   - the nested `Includemod` and `Includecore` detail variants are mapped in
     section 5.3 below
3. `Typemod.Cannot_eliminate_dependency`
   - covered by
     `tests/error_output_parity/compiler/fixtures/cannot_eliminate_dependency.res`
4. `Typemod.Signature_expected`
   - covered by
     `tests/error_output_parity/compiler/fixtures/signature_expected_package_constraint.res`
     and
     `tests/error_output_parity/compiler/fixtures/signature_expected_include_functor.res`
5. `Typemod.Structure_expected`
   - covered by
     `tests/error_output_parity/compiler/fixtures/structure_expected_open_functor.res`
     and
     `tests/error_output_parity/compiler/fixtures/structure_expected_include_functor.res`
6. `Typemod.With_no_component`
   - covered by `tests/error_output_parity/compiler/fixtures/with_no_component_type.res`
7. `Typemod.With_mismatch`
   - covered by `tests/error_output_parity/compiler/fixtures/with_mismatch_type.res`
8. `Typemod.With_makes_applicative_functor_ill_typed`
   - covered by
     `tests/error_output_parity/compiler/fixtures/with_makes_applicative_functor_ill_typed.res`
9. `Typemod.With_changes_module_alias`
   - covered by
     `tests/error_output_parity/compiler/fixtures/with_changes_module_alias.res`
10. `Typemod.With_cannot_remove_constrained_type`
    - covered by
      `tests/error_output_parity/compiler/fixtures/with_cannot_remove_constrained_type.res`
11. `Typemod.Repeated_name`
    - covered by `tests/error_output_parity/compiler/fixtures/repeated_module_name.res`
12. `Typemod.Non_generalizable`
    - covered by
      `tests/error_output_parity/compiler/fixtures/non_generalizable_ref_none.res`
13. `Typemod.Non_generalizable_module`
    - covered by `tests/error_output_parity/compiler/fixtures/non_generalizable_module.res`
      and the `module type of` path in
      `tests/error_output_parity/compiler/fixtures/module_type_of_non_generalizable.res`
14. `Typemod.Interface_not_compiled`
    - covered by `tests/error_output_parity/compiler/cases/interface_not_compiled.res`
      through the `-bs-read-cmi` case in
      `tests/error_output_parity/compiler/cases.tsv`
15. `Typemod.Not_allowed_in_functor_body`
    - covered by
      `tests/error_output_parity/compiler/fixtures/not_allowed_in_functor_body.res`
16. `Typemod.Not_a_packed_module`
    - covered by
      `tests/error_output_parity/compiler/fixtures/unpack_not_a_packed_module.res`
17. `Typemod.Incomplete_packed_module`
    - covered by
      `tests/error_output_parity/compiler/fixtures/incomplete_packed_module.res`
18. `Typemod.Scoping_pack`
    - covered by
      `tests/error_output_parity/compiler/fixtures/package_scoping_pack_local_type.res`
19. `Typemod.Recursive_module_require_explicit_type`
    - covered by
      `tests/error_output_parity/compiler/fixtures/recursive_module_requires_explicit_type.res`
20. `Typemod.Apply_generative`
    - covered by `tests/error_output_parity/compiler/fixtures/apply_generative_functor.res`
21. `Typemod.Cannot_scrape_alias`
    - covered by
      `tests/error_output_parity/compiler/cases/cannot_scrape_alias_module_type_with.res`
    - this case requires the missing-alias environment from
      `tests/error_output_parity/compiler/cases/missing_module_cmis`

The latest focused and broad evidence for this family is:

- `TIMEOUT_SECONDS=10 ./scripts/test_error_output_parity.sh --compiler-only cannot_scrape_alias`
  passes 2/2
- `TIMEOUT_SECONDS=10 ./scripts/test_error_output_parity.sh --compiler-only`
  passes 1013/1013

### 5.3 Expression and Pattern Typing Diagnostics

`compiler/ml/typecore.ml:27-100` defines the finite expression/pattern typing
error constructor set. Coverage now includes:

1. `Typecore.Polymorphic_label`
   - covered by `tests/error_output_parity/compiler/fixtures/polymorphic_label.res`
2. `Typecore.Constructor_arity_mismatch`
   - covered by
     `tests/error_output_parity/compiler/fixtures/constructor_arity_mismatch.res`
   - inline-record branches are covered by
     `constructor_arity_inline_record_missing.res` and
     `constructor_arity_inline_record_extra.res`
3. `Typecore.Label_mismatch`
   - covered by `tests/error_output_parity/compiler/fixtures/label_mismatch.res`
4. `Typecore.Pattern_type_clash`
   - covered by `tests/error_output_parity/compiler/fixtures/pattern_type_clash.res`
5. `Typecore.Or_pattern_type_clash`
   - covered by `tests/error_output_parity/compiler/fixtures/or_pattern_type_clash.res`
6. `Typecore.Multiply_bound_variable`
   - covered by `tests/error_output_parity/compiler/fixtures/multiply_bound_variable.res`
7. `Typecore.Orpat_vars`
   - covered by `tests/error_output_parity/compiler/fixtures/orpat_vars.res`
     and the spellcheck branch in `orpat_vars_spellcheck.res`
8. `Typecore.Expr_type_clash`
   - covered by `tests/error_output_parity/compiler/fixtures/expr_type_clash.res`
   - function-kind branches are covered by
     `expr_type_clash_curried_expected_uncurried.res`,
     `expr_type_clash_uncurried_expected_curried.res`, and
     `expr_type_clash_curried_value_expected_uncurried.res`
   - local-module escape contexts are covered by the `let_module_escape_*`
     fixtures and `package_local_type_escape.res`
9. `Typecore.Apply_non_function`
   - covered by `tests/error_output_parity/compiler/fixtures/apply_non_function.res`
     and the arrow/too-many-curried-args branch in
     `apply_non_function_too_many_curried_args.res`
10. `Typecore.Apply_wrong_label`
    - covered by `apply_wrong_label.res`, `apply_wrong_label_optional.res`,
      and `apply_wrong_label_unlabeled.res`
11. `Typecore.Label_multiply_defined`
    - covered by `label_multiply_defined.res` and the JSX component branch in
      `jsx_duplicate_prop_call.res`
12. `Typecore.Labels_missing`
    - covered by `labels_missing.res` and the JSX component branch in
      `jsx_missing_required_prop_call.res`
13. `Typecore.Label_not_mutable`
    - covered by `tests/error_output_parity/compiler/fixtures/label_not_mutable.res`
14. `Typecore.Wrong_name`
    - covered by `wrong_name.res`, `wrong_name_spellcheck.res`,
      `wrong_name_inline_record_constructor.res`, `jsx_unknown_prop_call.res`,
      and `jsx_children_not_allowed.res`
15. `Typecore.Name_type_mismatch`
    - covered by `name_type_mismatch.res` and
      `name_type_mismatch_multiple.res`
16. `Typecore.Undefined_method`
    - covered by `undefined_method.res`, `undefined_method_spellcheck.res`,
      and `undefined_method_no_alternatives.res`
17. `Typecore.Private_type`
    - covered by `tests/error_output_parity/compiler/fixtures/private_type.res`
18. `Typecore.Private_label`
    - covered by `tests/error_output_parity/compiler/fixtures/private_label.res`
19. `Typecore.Not_subtype`
    - covered by
      `tests/error_output_parity/compiler/fixtures/not_subtype_variant_spread.res`
20. `Typecore.Too_many_arguments`
    - covered by `too_many_arguments.res` and
      `too_many_function_parameters.res`
21. `Typecore.Abstract_wrong_label`
    - covered by `abstract_wrong_label.res`, `abstract_wrong_label_optional.res`,
      and `abstract_wrong_label_unlabeled.res`
22. `Typecore.Scoping_let_module`
    - covered by `tests/error_output_parity/compiler/fixtures/let_module_escape_result.res`
23. `Typecore.Not_a_variant_type`
    - covered by
      `tests/error_output_parity/compiler/fixtures/not_a_variant_type_spread.res`
24. `Typecore.Incoherent_label_order`
    - covered by `tests/error_output_parity/compiler/fixtures/incoherent_label_order.res`
25. `Typecore.Less_general`
    - covered by `less_general_field_value.res` and
      `less_general_definition.res`
26. `Typecore.Modules_not_allowed`
    - covered by
      `tests/error_output_parity/compiler/fixtures/modules_not_allowed_toplevel_unpack.res`
27. `Typecore.Cannot_infer_signature`
    - covered by
      `tests/error_output_parity/compiler/fixtures/cannot_infer_pack_signature.res`
28. `Typecore.Not_a_packed_module`
    - covered by `tests/error_output_parity/compiler/fixtures/not_a_packed_module.res`
29. `Typecore.Recursive_local_constraint`
    - covered by
      `tests/error_output_parity/compiler/fixtures/recursive_local_constraint.res`
30. `Typecore.Unexpected_existential`
    - covered by `tests/error_output_parity/compiler/fixtures/unexpected_existential.res`
31. `Typecore.Unqualified_gadt_pattern`
    - covered by
      `tests/error_output_parity/compiler/fixtures/unqualified_gadt_pattern.res`
32. `Typecore.Invalid_interval`
    - covered by
      `tests/error_output_parity/compiler/fixtures/invalid_interval_pattern.res`
33. `Typecore.Invalid_for_loop_index`
    - covered by
      `tests/error_output_parity/compiler/fixtures/invalid_for_loop_index.res`
34. `Typecore.Invalid_for_of_pattern`
    - covered by
      `tests/error_output_parity/compiler/fixtures/invalid_for_of_pattern.res`
35. `Typecore.No_value_clauses`
    - covered by `tests/error_output_parity/compiler/fixtures/no_value_clauses.res`
36. `Typecore.Exception_pattern_below_toplevel`
    - covered by
      `tests/error_output_parity/compiler/fixtures/exception_pattern_below_toplevel.res`
37. `Typecore.Inlined_record_escape`
    - covered by
      `tests/error_output_parity/compiler/fixtures/inlined_record_escape.res`
38. `Typecore.Inlined_record_expected`
    - covered by
      `tests/error_output_parity/compiler/fixtures/inlined_record_expected.res`
39. `Typecore.Invalid_extension_constructor_payload`
    - covered by
      `tests/error_output_parity/compiler/fixtures/invalid_extension_constructor_payload.res`
40. `Typecore.Not_an_extension_constructor`
    - covered by
      `tests/error_output_parity/compiler/fixtures/not_an_extension_constructor.res`
41. `Typecore.Break_outside_loop`
    - covered by `tests/error_output_parity/compiler/fixtures/break_outside_loop.res`
42. `Typecore.Continue_outside_loop`
    - covered by
      `tests/error_output_parity/compiler/fixtures/continue_outside_loop.res`
43. `Typecore.Literal_overflow`
    - covered by `tests/error_output_parity/compiler/fixtures/literal_overflow.res`
44. `Typecore.Unknown_literal`
    - covered by `unknown_integer_literal_modifier.res` and
      `unknown_float_literal_modifier.res`
45. `Typecore.Illegal_letrec_pat`
    - covered by
      `tests/error_output_parity/compiler/fixtures/illegal_letrec_pattern.res`
46. `Typecore.Empty_record_literal`
    - covered by `tests/error_output_parity/compiler/fixtures/empty_record_literal.res`
47. `Typecore.Uncurried_arity_mismatch`
    - covered by `unlabelled_arity_mismatch.res`,
      `uncurried_arity_missing_required_label.res`,
      `uncurried_arity_superfluous_label.res`,
      `uncurried_arity_suggestion.res`, and
      `uncurried_arity_method_annotated.res`
48. `Typecore.Field_not_optional`
    - covered by `field_not_optional_pattern.res` and
      `field_not_optional_inline_record.res`
49. `Typecore.Type_params_not_supported`
    - covered by
      `tests/error_output_parity/compiler/fixtures/type_params_not_supported_variant_spread.res`
50. `Typecore.Field_access_on_dict_type`
    - covered by
      `tests/error_output_parity/compiler/fixtures/field_access_on_dict_type.res`
51. `Typecore.Jsx_not_enabled`
    - covered by `tests/error_output_parity/compiler/cases/jsx_not_enabled.res`
      through the no-`-bs-jsx` case in
      `tests/error_output_parity/compiler/cases.tsv`

Broad evidence for this family:

- `TIMEOUT_SECONDS=10 ./scripts/test_error_output_parity.sh --compiler-only`
  passes 1013/1013 with the debug Rust compiler

### 5.4 Coercion Subtype Context Diagnostics

`compiler/ml/ctype.ml:73-103` defines `subtype_context`, which is printed by
`compiler/ml/printtyp.ml:1748-1812` through `Typecore.Not_subtype`. Coverage
now includes:

1. `Ctype.Coercion_target_variant_not_unboxed`
   - covered by
     `tests/error_output_parity/compiler/fixtures/coerce_primitive_to_variant_not_unboxed.res`
2. `Ctype.Coercion_target_variant_does_not_cover_type`
   - covered by
     `tests/error_output_parity/compiler/fixtures/coerce_primitive_to_variant_no_catchall.res`
3. `Ctype.Variant_constructor_runtime_representation_mismatch`
   - nested issue variants from `compiler/ml/variant_coercion.ml:1-20` are
     covered by:
     `coerce_variant_to_primitive_unboxed_payload_mismatch.res`
     (`Mismatched_unboxed_payload`),
     `coerce_variant_to_primitive_missing_as.res`
     (`Mismatched_as_payload None`),
     `coerce_variant_to_primitive_mismatched_as.res`
     (`Mismatched_as_payload Some`),
     `coerce_variant_to_primitive_null_as.res`
     (`As_payload_not_elgible_for_coercion`),
     `coerce_variant_to_primitive_inline_record.res`
     (`Inline_record_cannot_be_coerced`), and
     `coerce_variant_to_primitive_payload_not_unboxed.res`
     (`Cannot_coerce_non_unboxed_with_payload`)
4. `Ctype.Variant_configurations_mismatch`
   - nested issue variants from `compiler/ml/variant_coercion.ml:176-179`
     are covered by:
     `coerce_variant_unboxed_configuration_mismatch.res`
     (`Unboxed_config_not_matching`),
     `coerce_variant_tag_configuration_mismatch.res`
     (`Tag_name_not_matching`), and
     `coerce_variant_constructor_count_mismatch.res`
     (`Incompatible_constructor_count`)
5. `Ctype.Different_type_kinds`
   - covered by
     `tests/error_output_parity/compiler/fixtures/coerce_different_type_kinds.res`
6. `Ctype.Record_fields_mismatch`
   - nested issue variants from `compiler/ml/record_coercion.ml:1-12` are
     covered by:
     `coerce_record_optional_to_required.res`,
     `coerce_record_required_to_optional.res`,
     `coerce_record_left_as_runtime_mismatch.res`,
     `coerce_record_right_as_runtime_mismatch.res`, and
     `coerce_record_missing_field.res`

`Ctype.Generic {errorCode = "VCPMMVD"}` reachability note:

- The only construction site is `compiler/ml/ctype.ml:3754-3757`.
- That arm is inside a branch guarded by
  `extract_concrete_typedecl_opt env t2 |> Variant_coercion.can_try_coerce_variant_to_primitive_opt |> Option.is_some`,
  then immediately re-runs the same pure query and matches on `None`.
- No direct ReScript source fixture is currently known that can reach this
  defensive fallback without an inconsistent typed environment.

Focused evidence:

- `TIMEOUT_SECONDS=10 ./scripts/test_error_output_parity.sh --compiler-only coerce_`
  passes 17/17

### 5.5 Untagged Variant Diagnostics

`compiler/ml/ast_untagged_variants.ml:52-69` defines the finite untagged
variant error set. Coverage now includes:

1. `Ast_untagged_variants.InvalidVariantAsAnnotation`
   - covered by
     `tests/error_output_parity/compiler/fixtures/untagged_invalid_as_annotation.res`
2. `Ast_untagged_variants.Duplicated_bs_as`
   - covered by
     `tests/error_output_parity/compiler/fixtures/untagged_duplicate_as.res`
3. `Ast_untagged_variants.InvalidVariantTagAnnotation`
   - covered by
     `tests/error_output_parity/compiler/fixtures/untagged_invalid_tag_annotation.res`
4. `Ast_untagged_variants.TagFieldNameConflict`
   - covered by
     `tests/error_output_parity/compiler/fixtures/untagged_tag_field_conflict.res`
5. `Ast_untagged_variants.InvalidUntaggedVariantDefinition`
   - `OnlyOneUnknown` is covered by `untagged_only_one_unknown.res`
   - `AtMostOneObject` is covered by `untagged_at_most_one_object.res`
   - `AtMostOneFunction` is covered by `untagged_at_most_one_function.res`
   - `AtMostOneString` is covered by `untagged_at_most_one_string.res`
   - `AtMostOneNumber` is covered by `untagged_at_most_one_number.res`
   - `AtMostOneBigint` is covered by `untagged_at_most_one_bigint.res`
   - `AtMostOneBoolean` is covered by `untagged_at_most_one_boolean.res`
   - `DuplicateLiteral` string and non-string payloads are covered by
     `untagged_duplicate_string_literal.res` and
     `untagged_duplicate_nonstring_literal.res`
   - `ConstructorMoreThanOneArg` is covered by
     `untagged_constructor_more_than_one_arg.res`
   - every `AtMostOneInstance` display name from
     `ast_untagged_variants.ml:1-50` is now covered by a dedicated fixture:
     `untagged_at_most_one_array.res`,
     `untagged_at_most_one_arraybuffer.res`,
     `untagged_at_most_one_bigint64array.res`,
     `untagged_at_most_one_biguint64array.res`,
     `untagged_at_most_one_blob.res`,
     `untagged_at_most_one_dataview.res`,
     `untagged_at_most_one_date.res`,
     `untagged_at_most_one_file.res`,
     `untagged_at_most_one_float32array.res`,
     `untagged_at_most_one_float64array.res`,
     `untagged_at_most_one_int16array.res`,
     `untagged_at_most_one_int32array.res`,
     `untagged_at_most_one_int8array.res`,
     `untagged_at_most_one_map.res`,
     `untagged_at_most_one_promise.res`,
     `untagged_at_most_one_regexp.res`,
     `untagged_at_most_one_set.res`,
     `untagged_at_most_one_uint16array.res`,
     `untagged_at_most_one_uint32array.res`,
     `untagged_at_most_one_uint8array.res`,
     `untagged_at_most_one_uint8clampedarray.res`,
     `untagged_at_most_one_weakmap.res`, and
     `untagged_at_most_one_weakset.res`

The post-env recursive type group path is covered in both implementation and
signature contexts by `untagged_recursive_promise_alias_collision.res` and
`untagged_recursive_promise_alias_collision.resi`.

Focused evidence:

- `TIMEOUT_SECONDS=10 ./scripts/test_error_output_parity.sh --compiler-only untagged_at_most_one_`
  passes 29/29
- `TIMEOUT_SECONDS=10 ./scripts/test_error_output_parity.sh --compiler-only untagged_`
  passes 40/40

### 5.6 Module Inclusion Type Mismatch Diagnostics

`compiler/ml/includecore.ml:159-177` defines the type-declaration mismatch
details printed through `Typemod.Not_included` and related signature-mismatch
paths. Record-field mismatch coverage now includes:

1. `Includecore.Field_optional`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_record_field_optional.res`
2. `Includecore.Field_mutable`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_record_field_mutable.res`
   - this verifies the signature/type-declaration pretty-printer preserves the
     `mutable` field prefix.
3. `Includecore.Field_missing`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_record_field_missing.res`
4. `Includecore.Field_names`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_record_field_names.res`
   - this verifies OCaml's one-based field numbering in the diagnostic text.
5. `Includecore.Field_type`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_record_field_type.res`

Top-level type-declaration mismatch coverage now includes:

1. `Includecore.Arity`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_arity.res`
2. `Includecore.Privacy`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_privacy.res`
3. `Includecore.Kind`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_kind.res`
4. `Includecore.Constraint`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_constraint_param.res`
5. `Includecore.Manifest`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_manifest.res`
6. `Includecore.Variance`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_variance.res`
7. `Includecore.Unboxed_representation`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_unboxed_representation.res`
8. `Includecore.Immediate`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_immediate.res`
9. `Includecore.Tag_name`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_type_tag_name.res`

Variant-constructor mismatch coverage now includes:

1. `Includecore.Field_names`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_variant_constructor_names.res`
   - this verifies OCaml's one-based constructor numbering in the diagnostic text.
2. `Includecore.Field_missing`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_variant_constructor_missing.res`
3. `Includecore.Field_arity`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_variant_constructor_arity.res`
4. `Includecore.Field_type`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_variant_constructor_type.res`
5. `Includecore.Variant_representation`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_variant_representation.res`

`Includecore.Record_representation` reachability note:

- OCaml top-level record declarations are produced in `compiler/ml/typedecl.ml:647-656`
  as either `Record_regular` or `Record_unboxed false`.
- Inline record constructor payloads use `Record_inlined` or `Record_unboxed true`
  in `compiler/ml/datarepr.ml:132-135`, but those are constructor payload
  records, not top-level `Type_record` declarations compared by
  `Includecore.type_declarations`.
- Rust mirrors this split in `compiler-rust/src/types/typemod.rs:21141-21145`
  for top-level records and `compiler-rust/src/types/typemod.rs:20833-20838`
  for inline constructor records.
- No direct ReScript source fixture is currently known that reaches
  `Record_representation`; the other `Includecore.type_mismatch` constructors
  above are covered by byte-for-byte OCaml/Rust fixtures.

`compiler/ml/includemod.ml:23-39` defines the higher-level module inclusion
symptoms. Coverage now includes:

1. `Includemod.Missing_field`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_missing_value.res`
2. `Includemod.Value_descriptions`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_value_mismatch.res`
3. `Includemod.Type_declarations`
   - covered by the `not_included_type_*`, `not_included_record_*`, and
     `not_included_variant_*` fixtures above.
4. `Includemod.Extension_constructors`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_extension_mismatch.res`
5. `Includemod.Module_types`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_module_mismatch.res`
   - functor-body alias formatting is covered by
     `tests/error_output_parity/compiler/fixtures/not_included_functor_arg_module_alias_mismatch.res`
6. `Includemod.Modtype_infos`
   - covered by `tests/error_output_parity/compiler/fixtures/not_included_modtype_mismatch.res`
7. `Includemod.Modtype_permutation`
   - covered by `tests/error_output_parity/compiler/fixtures/modtype_permutation.res`
8. `Includemod.Interface_mismatch`
   - covered by `tests/error_output_parity/compiler/cases/compunit_value_mismatch.res`
9. `Includemod.Unbound_module_path`
   - covered by `tests/error_output_parity/compiler/cases/include_unbound_module_path.res`

`Includemod.Unbound_modtype_path` and `Includemod.Invalid_module_alias`
reachability notes:

- `Unbound_modtype_path` is raised from
  `compiler/ml/includemod.ml:92-95` only after the same environment has already
  indicated that the module-type path may expand. Ordinary ReScript source
  probes with an unbound module type reach `Typetexp.Unbound_modtype` before
  inclusion.
- `Invalid_module_alias` is guarded by `Env.is_functor_arg` in
  `compiler/ml/includemod.ml:209-211`. Source probes with functor-argument
  aliases currently report the surrounding `Module_types` mismatch; no direct
  ReScript source fixture is currently known that prints
  `Module <path> cannot be aliased`.

### 5.7 Compiled Interface Format Diagnostics

`compiler/ml/cmi_format.ml:18-21` defines compiled-interface reader errors.
These are covered through direct `.cmi` cases in
`tests/error_output_parity/compiler/cases.tsv`:

1. `Cmi_format.Not_an_interface`
   - covered by `tests/error_output_parity/compiler/cases/cmi_not_an_interface.cmi`
2. `Cmi_format.Wrong_version_interface`
   - covered by `tests/error_output_parity/compiler/cases/cmi_wrong_version.cmi`
3. `Cmi_format.Corrupted_interface`
   - covered by `tests/error_output_parity/compiler/cases/cmi_corrupted.cmi`

`compiler/ml/cmt_format.ml:69-70` defines `Cmt_format.Not_a_typedtree`.
It is covered by `tests/error_output_parity/compiler/cases/gentype_stale_cmti.res`,
where `-bs-gentype` selects a stale `.cmti` containing only CMI data and both
compilers print `Fatal error: exception Cmt_format.Error(_)`.

### 5.8 Frontend Direct `raise_errorf` Diagnostics

Several frontend rewrites raise plain `Location.raise_errorf` diagnostics
instead of typed `type error` constructors. Coverage includes:

1. `compiler/frontend/ast_tuple_pattern_flatten.ml:67-81`
   - qualified record labels while destructuring packed modules are rejected with
     `Not supported pattern match on modules`
   - covered by
     `tests/error_output_parity/compiler/fixtures/module_pattern_match_qualified.res`
2. `compiler/core/lam_compile.ml:1765-1818`
   - `%import` is rejected for missing arguments and for exactly one argument
     that is not a module or module value
   - missing/extra-argument arity is covered by
     `tests/error_output_parity/compiler/fixtures/dynamic_import_no_argument_external.res`
     and
     `tests/error_output_parity/compiler/fixtures/dynamic_import_too_many_arguments_external.res`
   - unsupported single value argument is covered by
     `tests/error_output_parity/compiler/fixtures/dynamic_import_value_argument.res`
     and the raw external primitive path by
     `tests/error_output_parity/compiler/fixtures/dynamic_import_value_external.res`
3. `compiler/frontend/ast_utf8_string.ml:25-30` and
   `compiler/frontend/ast_utf8_string.ml:190-197`
   - JS-delimited string transformation reports `Offset: ...` diagnostics for
     invalid escape payloads after parsing has produced `Pconst_string (_, Some "js")`
   - invalid `\x` payload is covered by
     `tests/error_output_parity/compiler/fixtures/template_pattern_invalid_hex_escape.res`
   - invalid fixed-width `\u` payload is covered by
     `tests/error_output_parity/compiler/fixtures/template_pattern_invalid_unicode_escape.res`
   - invalid `\u{...}` codepoint payload is covered by
     `tests/error_output_parity/compiler/fixtures/template_pattern_utf8_codepoint_escape.res`
     and
     `tests/error_output_parity/compiler/fixtures/string_escape_codepoint_overflow.res`
   - ordinary quoted-string malformed escapes such as `"\x"` and `"\u12"`
     are rejected by the scanner before the frontend transform; those earlier
     scanner diagnostics are covered by the `string_escape_*` fixtures
   - the trailing-backslash transform branch is parser-masked for direct
     ReScript source: a template-pattern probe with `` `\` `` reaches
     `Diagnostics.unclosed_template` before `Ast_utf8_string.transform`
   - no direct ReScript source fixture is currently known that reaches
     `Invalid_code_point` in this frontend transform; raw source invalid
     codepoints are owned by scanner diagnostics before the PPX transform
4. `compiler/frontend/ast_external_process.ml:207-215`
   - payload-bearing external attributes `@val`, `@send`, `@set`, `@get`,
     and `@new` accept either no payload or a single string payload
   - invalid payload coverage now mirrors that attribute list:
     `tests/error_output_parity/compiler/fixtures/bs_external_val_invalid_payload.res`,
     `tests/error_output_parity/compiler/fixtures/bs_external_send_invalid_payload.res`,
     `tests/error_output_parity/compiler/fixtures/bs_external_set_invalid_payload.res`,
     `tests/error_output_parity/compiler/fixtures/bs_external_get_invalid_payload.res`,
     and
     `tests/error_output_parity/compiler/fixtures/bs_external_new_invalid_payload.res`
5. `compiler/frontend/ast_external_process.ml:379-384`
   - `@return` accepts only a single punned directive action
   - unsupported return directives are covered by
     `tests/error_output_parity/compiler/fixtures/bs_return_unknown_directive.res`
   - a config-record field with an explicit payload is covered by
     `tests/error_output_parity/compiler/fixtures/bs_return_record_value_payload.res`
6. `compiler/frontend/ast_exp_handle_external.ml:69-172`
   - `%debugger` payload rejection is covered by
     `tests/error_output_parity/compiler/fixtures/raw_debugger_payload.res`
   - `%raw`, `%re`, and `%%raw` non-string payloads are covered by
     `raw_expr_non_string.res`, `raw_re_non_string.res`, and
     `raw_structure_non_string.res`
   - `%ffi` non-string and non-function payloads are covered by
     `ffi_non_string.res` and `ffi_non_function_string.res`
   - Flow warning/error variants for raw and ffi payload parsing are covered by
     the `raw_expr_*`, `raw_structure_*`, and `ffi_*_warning` fixtures
7. `compiler/frontend/ast_exp_extension.ml:79`
   - `%obj` accepts only record-expression payloads
   - covered by
     `tests/error_output_parity/compiler/fixtures/obj_extension_non_record.res`
8. `compiler/frontend/typemod_hide.ml:54-58`
   - `%%private(...)` local extensions reject structures that define types
   - covered by
     `tests/error_output_parity/compiler/fixtures/private_type_in_local_extension.res`

### 5.9 Recursive Value Diagnostics

`compiler/ml/rec_check.ml:453-475` defines the backend recursive-value
right-hand-side check:

1. `Rec_check.Illegal_letrec_expr`
   - covered by `tests/error_output_parity/compiler/fixtures/illegal_letrec_expr.res`

### 5.10 Backend and Environment Diagnostics

`compiler/ml/env.ml:57-62` defines environment-loading and value-name errors.
Coverage now includes:

1. `Env.Illegal_renaming`
   - covered by `tests/error_output_parity/compiler/cases/illegal_renaming.res`
2. `Env.Inconsistent_import`
   - covered by
     `tests/error_output_parity/compiler/cases/inconsistent_import.res`
3. `Env.Missing_module`
   - covered by `tests/error_output_parity/compiler/cases/missing_module.res`
4. `Env.Illegal_value_name`
   - covered by
     `tests/error_output_parity/compiler/cases/illegal_value_name.res`
5. `Warnings.No_cmi_file`
   - covered by
     `tests/error_output_parity/compiler/cases/no_cmi_file_warning.res`
   - the current-unit `-no-alias-deps` branch is covered by
     `tests/error_output_parity/compiler/cases/module_alias_current_unit_no_alias_deps.res`

`compiler/ml/transl_recmodule.ml:5-7` defines the recursive-module translation
error:

1. `Transl_recmodule.Circular_dependency`
   - covered by
     `tests/error_output_parity/compiler/fixtures/circular_recursive_module.res`
     and the `module type of` approximation path in
     `tests/error_output_parity/compiler/fixtures/module_type_of_structure_recursive_module.res`

`compiler/core/lam_compile_primitive.ml` has direct backend diagnostics for
primitive lowering:

1. `Pimport` module/file argument rejection
   - covered by `dynamic_import_global_value.res`,
     `dynamic_import_value_argument.res`,
     `dynamic_import_local_value.res`, and
     `dynamic_import_no_argument_external.res`
2. `Pimport` primitive arity guard
   - source-unreachable from ordinary ReScript because `Lam_compile` handles
     `%import` arity before calling `Lam_compile_primitive.translate`; the
     lower primitive helper keeps the same diagnostic for invalid lambda input
3. `Pdict_has` invalid external signature
   - covered by
     `tests/error_output_parity/compiler/fixtures/dict_has_bad_arity.res`

### 5.11 Frontend Helper Diagnostics

`compiler/frontend/bs_syntaxerr.ml:27-51` defines the finite frontend syntax
error constructor set. Coverage now includes:

1. `Unsupported_predicates`
   - covered by `bs_get_unsupported_predicate.res` and
     `bs_set_unsupported_predicate.res`
2. `Duplicated_bs_deriving`
   - covered by `bs_duplicate_deriving.res`
3. `Conflict_attributes`
   - covered by `bs_conflict_type_ffi_attrs.res`
4. `Expect_int_literal`
   - covered by `bs_int_as_expect_int_literal.res`
5. `Expect_string_literal`
   - covered by `bs_string_as_expect_string_literal.res` and the config
     action path in `config_flags_non_array.res`
6. `Expect_int_or_string_or_json_literal`
   - covered by `bs_as_expect_int_string_json_literal.res`
7. `Unhandled_poly_type`
   - covered by `bs_external_unhandled_poly_type.res`
8. `Invalid_underscore_type_in_external`
   - covered by `bs_invalid_underscore_external.res`
9. `Invalid_bs_string_type`
   - covered by `bs_invalid_string_external_arg.res`
10. `Invalid_bs_int_type`
    - covered by `bs_invalid_int_external_arg.res`
11. `Invalid_bs_unwrap_type`
    - covered by `bs_invalid_unwrap_external_arg.res`
12. `Conflict_ffi_attribute`
    - covered by `bs_conflict_get_index_module.res`,
      `bs_conflict_set_index_module.res`, `bs_conflict_module_val.res`,
      `bs_conflict_module_send.res`, `bs_conflict_module_value_new.res`,
      `bs_conflict_val_call_send.res`, `bs_conflict_val_value_new.res`, and
      `bs_conflict_new_get.res`
13. `Illegal_attribute`
    - covered by `bs_external_illegal_module_many_strings.res` and
      `bs_external_illegal_scope_empty.res`
14. `Not_supported_directive_in_bs_return`
    - covered by `bs_return_unknown_directive.res`
15. `Expect_opt_in_bs_return_to_opt`
    - covered by `bs_return_to_opt_non_option.res`
16. `Misplaced_label_syntax`
    - covered by `bs_misplaced_label_syntax.res`
17. `Optional_in_uncurried_bs_attribute`
    - covered by `bs_this_optional_arg.res`
18. `Bs_this_simple_pattern`
    - covered by `bs_this_simple_pattern.res`
19. `Experimental_feature_not_enabled LetUnwrap`
    - covered through included super-error fixtures
      `tests/build_tests/super_errors/fixtures/feature_letunwrap_not_enabled.res`
      and `let_unwrap_on_top_level_not_enabled.res`
20. `LetUnwrap_not_supported_in_position`
    - `Toplevel` is covered by
      `tests/build_tests/super_errors/fixtures/let_unwrap_on_top_level.res`
    - `Unsupported_type` is covered by
      `tests/build_tests/super_errors/fixtures/let_unwrap_on_not_supported_variant.res`

`Conflict_bs_bs_this_bs_meth` is still a dead constructor in the current OCaml
source: `rg Conflict_bs_bs_this_bs_meth compiler` finds only the type
definition and formatter branches.

`compiler/frontend/ast_attributes.ml` and `compiler/ml/ast_payload.ml` provide
the helper checks used by many of the frontend diagnostics above. Source-level
coverage includes:

1. `Ast_payload.raw_as_string_exp_exn`
   - `%re` non-regex payload is covered by `raw_re_non_regex.res`
   - Flow parser warning/error branches are covered by the `raw_expr_*`,
     `raw_structure_*`, `ffi_invalid_js_warning.res`, and
     `raw_re_invalid_regex_warning.res` fixtures
2. `Ast_payload.ident_or_record_as_config`
   - qualified config labels are covered by `bs_get_predicate_qualified_label.res`,
     `bs_return_qualified_label.res`, and `bs_return_qualified_ident.res`
   - unsupported `with` records and invalid payload warnings are covered by
     `config_invalid_payload_warning.res` and `bs_return_record_with_payload.res`
3. `Ast_payload.assert_strings`
   - string, tuple, and non-string tuple branches are covered by
     `bs_external_scope_ident_payload.res`,
     `bs_external_module_ident_payload.res`,
     `bs_external_scope_tuple_non_string.res`, and
     `bs_external_module_tuple_non_string.res`
4. `Ast_payload.assert_bool_lit`
   - covered by `bs_get_predicate_non_bool.res`,
     `bs_set_predicate_non_bool.res`, and `config_no_export_non_bool.res`
5. `Ast_payload.table_dispatch`
   - covered by `deriving_unsupported.res` and `config_unknown.res`
6. `Ast_attributes.iter_process_bs_string_as`,
   `iter_process_bs_int_as`, and `iter_process_bs_string_or_int_as`
   - wrong-payload, duplicate, overflow, and JSON-object branches are covered by
     the `bs_string_as_*`, `bs_int_as_*`, `bs_as_*`, and `untagged_as_*`
     fixtures

`Ast_payload.as_core_type` is currently not reachable from ordinary source:
`rg "Ast_payload\\.as_core_type|as_core_type\\b" compiler` finds only the
definition and `.mli` declaration.

`compiler/frontend/bs_builtin_ppx.ml` owns the OCaml reference placement for
`let?` feature, top-level, and unsupported-pattern checks. Rust currently
matches the user-facing output but the check placement is not 1:1: the normal
compiler path still preflights these cases in `compiler-rust/src/driver.rs`,
while `compiler-rust/src/binary_ast/ppx.rs` performs the rewrite. This is a
source-alignment note, not a byte-output gap; the full error-output harness
includes the `super_errors` fixtures listed above.

Latest broad evidence after the untagged-instance expansion:

- `TIMEOUT_SECONDS=10 ./scripts/test_error_output_parity.sh`
  passes 1144/1144 with the debug Rust compiler

### 5.12 Frontend Reachability Notes

`compiler/frontend/ast_exp_apply.ml` has defensive diagnostics for malformed
rewritten pipe/property applications:

- `invalid ## syntax`
- `Invalid pipe syntax...`
- `Js object ## expect syntax like obj##(paint (a,b))`
- fallback `invalid %s syntax`

Direct ReScript probes for malformed `##`/`->` applications are rejected by the
parser first, before the builtin PPX mapper reaches these branches. Current
coverage therefore lives on the parser diagnostics that mask them, plus the
reachable `#=` branch:
`tests/error_output_parity/compiler/fixtures/invalid_hash_set_assignment.res`.

`compiler/frontend/ast_external.ml` has defensive checks for `pval_prim = []`
and `pval_prim` with more than one primitive string. Ordinary ReScript external
syntax requires exactly one primitive string and parser probes such as
`external x: int = ("a", "b")` report the earlier external-syntax diagnostic
instead of reaching `Ast_external`.

`compiler/frontend/bs_syntaxerr.ml` still defines and formats
`Conflict_bs_bs_this_bs_meth`, but the current OCaml source has no raise site
for that constructor. `rg Conflict_bs_bs_this_bs_meth compiler` only finds the
type definition and formatter branches, so there is no direct ReScript fixture
for this dead diagnostic.

## 6. Formatting and Presentation Contract

`compiler/ml/location.ml` defines the warning/error output contract consumed by parser diagnostics:

1. Warning/error intro tags and color classes (`compiler/ml/location.ml:95`)
2. Code-frame rendering with highlight range (`compiler/ml/location.ml:143`)
3. Warning header format (`Warning number N`) (`compiler/ml/location.ml:151`)
4. Warning printer entrypoint used by parser warning path (`compiler/ml/location.ml:169`)

This file is part of diagnostics parity scope because output style differences
are user-visible regressions even when semantic warning/error detection matches.

## 7. Coverage Implications

To claim parser diagnostics parity, tests must cover:

1. Each `Res_diagnostics.category` class.
2. Scanner-specific lexical diagnostics and category wrappers.
3. `ErrorMessages` catalog representatives across grammar areas.
4. Warning 22 emission and formatting parity.
5. JSX parser-time error text and location parity.
6. Location/code-frame formatting parity for warnings and syntax errors.
7. Crash-hardening cases where malformed input stresses code-frame slicing.

## 8. Fixture Completeness Target

Required fixture policy for this project:

1. Every in-scope parser warning/error emitter must map to at least one minimal fixture.
2. Fixtures should be as small as possible and isolated to one primary diagnostic.
3. Use both `.res` and `.resi` fixtures when an emitter is interface-relevant.
4. Maintain an explicit emitter-to-fixture matrix so coverage is auditable.

Numbered matrix + checker:

1. Matrix file: `tests/syntax_tests/data/parsing/diagnostics_numbers.csv`
2. Checker: `scripts/check_parser_diagnostics_numbers.sh`
3. The checker iterates each numbered parser error/warning entry and validates:
   - source fixture exists
   - expected output exists
   - expected output contains `Syntax error!` (errors) or `Warning number N` (warnings)
   - parser error numbering is contiguous (no missing numbers in `1..max`)
