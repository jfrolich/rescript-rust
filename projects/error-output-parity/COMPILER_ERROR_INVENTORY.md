# Compiler Error Inventory

Starting source inventory for compiler/typechecker diagnostic parity.

The fixture suite should eventually map each reachable variant below to at least
one `.res` or `.resi` file. Internal or unreachable variants should be marked
with a reason after checking raise sites.

## `compiler/ml/typecore.ml`

- `Polymorphic_label`
- `Constructor_arity_mismatch`
- `Label_mismatch`
- `Pattern_type_clash`
- `Or_pattern_type_clash`
- `Multiply_bound_variable`
- `Orpat_vars`
- `Expr_type_clash`
- `Apply_non_function`
- `Apply_wrong_label`
- `Label_multiply_defined`
- `Labels_missing`
- `Label_not_mutable`
- `Wrong_name`
- `Name_type_mismatch`
- `Undefined_method`
- `Private_type`
- `Private_label`
- `Not_subtype`
- `Too_many_arguments`
- `Abstract_wrong_label`
- `Scoping_let_module`
- `Not_a_variant_type`
- `Incoherent_label_order`
- `Less_general`
- `Modules_not_allowed`
- `Cannot_infer_signature`
- `Not_a_packed_module`
- `Recursive_local_constraint`
- `Unexpected_existential`
- `Unqualified_gadt_pattern`
- `Invalid_interval`
- `Invalid_for_loop_index`
- `Invalid_for_of_pattern`
- `No_value_clauses`
- `Exception_pattern_below_toplevel`
- `Inlined_record_escape`
- `Inlined_record_expected`
- `Invalid_extension_constructor_payload`
- `Not_an_extension_constructor`
- `Break_outside_loop`
- `Continue_outside_loop`
- `Literal_overflow`
- `Unknown_literal`
- `Illegal_letrec_pat`
- `Empty_record_literal`
- `Uncurried_arity_mismatch`
- `Field_not_optional`
- `Type_params_not_supported`
- `Field_access_on_dict_type`
- `Jsx_not_enabled`

### Typecore Coverage Notes

- `Polymorphic_label`: covered by
  `tests/error_output_parity/compiler/fixtures/polymorphic_label.res`.
- `Empty_record_literal`: covered by
  `tests/error_output_parity/compiler/fixtures/empty_record_literal.res`.
- `Constructor_arity_mismatch`: covered for positional payloads and both
  inline-record no-payload and nonzero wrong-payload branches by
  `tests/error_output_parity/compiler/fixtures/constructor_arity_mismatch.res` and
  `tests/error_output_parity/compiler/fixtures/constructor_arity_inline_record_missing.res`
  and
  `tests/error_output_parity/compiler/fixtures/constructor_arity_inline_record_extra.res`.
- `Label_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/label_mismatch.res`.
- `Pattern_type_clash`: covered by
  `tests/error_output_parity/compiler/fixtures/pattern_type_clash.res`
  and the local GADT constraint expansion subcase in
  `tests/error_output_parity/compiler/fixtures/recursive_local_constraint.res`,
  plus the local let-module function parameter escape subcase in
  `tests/error_output_parity/compiler/fixtures/let_module_escape_function_param.res`.
- `Or_pattern_type_clash`: covered by
  `tests/error_output_parity/compiler/fixtures/or_pattern_type_clash.res`.
- `Expr_type_clash`: covered by
  `tests/error_output_parity/compiler/fixtures/expr_type_clash.res`
  and the function label mismatch subcase in
  `tests/error_output_parity/compiler/fixtures/function_label_mismatch.res`,
  plus the local module escape note subcase in
  `tests/error_output_parity/compiler/fixtures/let_module_escape_type_clash.res`
  and the unannotated local module result escape subcase in
  `tests/error_output_parity/compiler/fixtures/let_module_escape_value.res`
  and the nested function return escape subcase in
  `tests/error_output_parity/compiler/fixtures/let_module_escape_function_return.res`,
  and the constrained expression local module escape subcase in
  `tests/error_output_parity/compiler/fixtures/let_module_escape_expr_constraint.res`,
  and the generic tuple-element expected-type subcase in
  `tests/error_output_parity/compiler/fixtures/let_module_escape_tuple_element.res`,
  and the package local type escape/coercion subcase in
  `tests/error_output_parity/compiler/fixtures/package_local_type_escape.res`,
  and the optional arrow argument hidden-type printer subcase in
  `tests/error_output_parity/compiler/fixtures/expr_type_clash_optional_hidden_arg.res`,
  and curried/uncurried function arity-shape subcases in
  `tests/error_output_parity/compiler/fixtures/expr_type_clash_curried_expected_uncurried.res`,
  `tests/error_output_parity/compiler/fixtures/expr_type_clash_uncurried_expected_curried.res`,
  and
  `tests/error_output_parity/compiler/fixtures/expr_type_clash_curried_value_expected_uncurried.res`,
  and the field-access option-receiver branch in
  `tests/error_output_parity/compiler/fixtures/field_access_option_receiver_type_clash.res`.
- `Ctype.Tags` / `Typetexp.Variant_tags` hash-collision diagnostics from row
  type translation and expression/pattern unification are covered by
  `tests/error_output_parity/compiler/fixtures/polyvariant_hash_collision_type.res`,
  `tests/error_output_parity/compiler/fixtures/polyvariant_hash_collision.res`
  and
  `tests/error_output_parity/compiler/fixtures/polyvariant_hash_collision_pattern.res`.
- `Multiply_bound_variable`: covered by
  `tests/error_output_parity/compiler/fixtures/multiply_bound_variable.res`.
- `Orpat_vars`: covered by
  `tests/error_output_parity/compiler/fixtures/orpat_vars.res` and the
  spellcheck hint branch in
  `tests/error_output_parity/compiler/fixtures/orpat_vars_spellcheck.res`.
- `Label_multiply_defined`: covered for plain records and JSX component calls by
  `tests/error_output_parity/compiler/fixtures/label_multiply_defined.res` and
  `tests/error_output_parity/compiler/fixtures/jsx_duplicate_prop_call.res`.
- `Labels_missing`: covered for plain records and JSX component calls by
  `tests/error_output_parity/compiler/fixtures/labels_missing.res` and
  `tests/error_output_parity/compiler/fixtures/jsx_missing_required_prop_call.res`.
- `Label_not_mutable`: covered by
  `tests/error_output_parity/compiler/fixtures/label_not_mutable.res`.
- `Wrong_name`: covered by
  `tests/error_output_parity/compiler/fixtures/wrong_name.res` and the
  spellcheck hint branch in
  `tests/error_output_parity/compiler/fixtures/wrong_name_spellcheck.res`,
  plus the inline-record constructor payload branch in
  `tests/error_output_parity/compiler/fixtures/wrong_name_inline_record_constructor.res`,
  plus the JSX component unknown-prop and children-prop branches in
  `tests/error_output_parity/compiler/fixtures/jsx_unknown_prop_call.res` and
  `tests/error_output_parity/compiler/fixtures/jsx_children_not_allowed.res`.
- `Name_type_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/name_type_mismatch.res` and the
  multiple-alternative branch in
  `tests/error_output_parity/compiler/fixtures/name_type_mismatch_multiple.res`.
- `Undefined_method`: covered for object receivers with alternatives,
  non-object receivers without alternatives, and the spellcheck hint branch by
  `tests/error_output_parity/compiler/fixtures/undefined_method.res`,
  `tests/error_output_parity/compiler/fixtures/undefined_method_no_alternatives.res`,
  and
  `tests/error_output_parity/compiler/fixtures/undefined_method_spellcheck.res`.
- `Private_type`: covered by
  `tests/error_output_parity/compiler/fixtures/private_type.res`.
- `Private_label`: covered by
  `tests/error_output_parity/compiler/fixtures/private_label.res`.
- `Apply_non_function`: covered by
  `tests/error_output_parity/compiler/fixtures/apply_non_function.res` and the
  arrow-result branch in
  `tests/error_output_parity/compiler/fixtures/apply_non_function_too_many_curried_args.res`.
- `Apply_wrong_label`: covered for labelled, unlabelled, and optional call-site
  labels by `tests/error_output_parity/compiler/fixtures/apply_wrong_label.res`,
  `tests/error_output_parity/compiler/fixtures/apply_wrong_label_unlabeled.res`,
  and
  `tests/error_output_parity/compiler/fixtures/apply_wrong_label_optional.res`.
- `Incoherent_label_order`: covered by
  `tests/error_output_parity/compiler/fixtures/incoherent_label_order.res`.
- `Less_general`: covered for field values and explicitly polymorphic
  definitions by
  `tests/error_output_parity/compiler/fixtures/less_general_field_value.res`
  and
  `tests/error_output_parity/compiler/fixtures/less_general_definition.res`.
- `Unqualified_gadt_pattern`: covered by
  `tests/error_output_parity/compiler/fixtures/unqualified_gadt_pattern.res`.
- `Unexpected_existential`: covered by
  `tests/error_output_parity/compiler/fixtures/unexpected_existential.res`.
- `Too_many_arguments`: covered by
  `tests/error_output_parity/compiler/fixtures/too_many_arguments.res` and the
  inside-function branch in
  `tests/error_output_parity/compiler/fixtures/too_many_function_parameters.res`.
- `Abstract_wrong_label`: covered for labelled, optional, and unlabelled inner
  function parameters by
  `tests/error_output_parity/compiler/fixtures/abstract_wrong_label.res`,
  `tests/error_output_parity/compiler/fixtures/abstract_wrong_label_optional.res`,
  and
  `tests/error_output_parity/compiler/fixtures/abstract_wrong_label_unlabeled.res`.
- `Scoping_let_module`: source-unreachable from normal ReScript. The
  `Pexp_letmodule` raise site in `compiler/ml/typecore.ml` is after typing the
  local module body with `type_expect`; source-level probes that make the local
  module type escape are rejected during that body expectation as
  `Expr_type_clash` or `Pattern_type_clash` before the later `unify_var` can
  raise `Scoping_let_module`. The observable earlier reporters are covered by
  `tests/error_output_parity/compiler/fixtures/scoping_let_module.res`,
  `tests/error_output_parity/compiler/fixtures/scoping_let_module_value.res`,
  `tests/error_output_parity/compiler/fixtures/let_module_escape_value.res`,
  `tests/error_output_parity/compiler/fixtures/let_module_escape_expr_constraint.res`,
  `tests/error_output_parity/compiler/fixtures/let_module_escape_function_param.res`,
  `tests/error_output_parity/compiler/fixtures/let_module_escape_function_return.res`,
  `tests/error_output_parity/compiler/fixtures/let_module_escape_tuple_element.res`,
  and
  `tests/error_output_parity/compiler/fixtures/let_module_escape_type_clash.res`.
- `Uncurried_arity_mismatch`: covered for unlabelled count mismatch, missing
  required labelled arguments, superfluous labelled arguments, annotated
  method-send application arity, inferred method-send fallback arity, and
  related arity-suffixed function suggestions by
  `tests/error_output_parity/compiler/fixtures/unlabelled_arity_mismatch.res`,
  `tests/error_output_parity/compiler/fixtures/uncurried_arity_missing_required_label.res`,
  `tests/error_output_parity/compiler/fixtures/uncurried_arity_superfluous_label.res`,
  `tests/error_output_parity/compiler/fixtures/uncurried_arity_method_annotated.res`,
  `tests/build_tests/super_errors/fixtures/method_arity_mismatch.res`,
  and
  `tests/error_output_parity/compiler/fixtures/uncurried_arity_suggestion.res`.
- `Field_not_optional`: covered for pattern and expression raise sites by
  `tests/error_output_parity/compiler/fixtures/field_not_optional_pattern.res`
  and
  `tests/error_output_parity/compiler/fixtures/field_not_optional_inline_record.res`.
- `Illegal_letrec_pat`: covered by
  `tests/error_output_parity/compiler/fixtures/illegal_letrec_pattern.res`.
- `Modules_not_allowed`: covered by
  `tests/error_output_parity/compiler/fixtures/modules_not_allowed_toplevel_unpack.res`.
  The allowed match-case module-pattern path is guarded by
  `tests/error_output_parity/compiler/fixtures/module_unpack_pattern_allowed.res`.
- `Invalid_for_loop_index`: covered by
  `tests/error_output_parity/compiler/fixtures/invalid_for_loop_index.res`.
- `Invalid_for_of_pattern`: covered by
  `tests/error_output_parity/compiler/fixtures/invalid_for_of_pattern.res`
  and the parser-normalized destructuring-pattern location case in
  `tests/error_output_parity/compiler/fixtures/for_of_destructuring_pattern.res`.
- `Invalid_interval`: covered by
  `tests/error_output_parity/compiler/fixtures/invalid_interval_pattern.res`.
- `No_value_clauses`: covered by
  `tests/error_output_parity/compiler/fixtures/no_value_clauses.res`.
- `Exception_pattern_below_toplevel`: covered by
  `tests/error_output_parity/compiler/fixtures/exception_pattern_below_toplevel.res`.
- `Literal_overflow`: covered by
  `tests/error_output_parity/compiler/fixtures/literal_overflow.res`.
- `Unknown_literal`: covered for both integer and float modifier raise sites by
  `tests/error_output_parity/compiler/fixtures/unknown_integer_literal_modifier.res`
  and
  `tests/error_output_parity/compiler/fixtures/unknown_float_literal_modifier.res`.
- `Cannot_infer_signature`: covered by
  `tests/error_output_parity/compiler/fixtures/cannot_infer_pack_signature.res`.
- `Not_a_packed_module`: covered by
  `tests/error_output_parity/compiler/fixtures/not_a_packed_module.res`.
- `Recursive_local_constraint`: checked against the `unify_pat_types_gadt`
  raise site in `compiler/ml/typecore.ml`. Local GADT constraint cycle probes
  found so far surface as `Pattern_type_clash`; an additional OCaml-only
  generated probe over 4,992 one- and two-parameter GADT result/payload/scrutinee
  shapes found no `Recursive local constraint` reporter. Keep this variant
  listed until a direct `Unification_recursive_abbrev` source-level repro is
  found or the raise site is proven unreachable for ReScript syntax. Rust now
  mirrors the OCaml check location: `unify_pattern_types_gadt` maps recursive
  abbreviation failures to `RecursiveLocalConstraint`, and
  `add_gadt_equation` uses a `local_non_recursive_abbrev` walk before
  installing a local constraint.
- `Not_a_variant_type`: covered by
  `tests/error_output_parity/compiler/fixtures/not_a_variant_type_spread.res`.
- `Not_subtype`: covered by
  `tests/error_output_parity/compiler/fixtures/not_subtype_variant_spread.res`.
  `Ctype.subtype_context` diagnostic subcases are covered by
  `tests/error_output_parity/compiler/fixtures/coerce_primitive_to_variant_not_unboxed.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_primitive_to_variant_no_catchall.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_to_primitive_payload_not_unboxed.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_to_primitive_inline_record.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_to_primitive_null_as.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_to_primitive_missing_as.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_to_primitive_mismatched_as.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_to_primitive_unboxed_payload_mismatch.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_unboxed_configuration_mismatch.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_tag_configuration_mismatch.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_variant_constructor_count_mismatch.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_record_optional_to_required.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_record_required_to_optional.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_record_left_as_runtime_mismatch.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_record_right_as_runtime_mismatch.res`,
  `tests/error_output_parity/compiler/fixtures/coerce_record_missing_field.res`,
  and
  `tests/error_output_parity/compiler/fixtures/coerce_different_type_kinds.res`.
  `Ctype.Generic {errorCode = "VCPMMVD"}` is marked unreachable: the only
  OCaml construction site is inside the primitive-to-variant coercion branch
  guarded by `can_try_coerce_variant_to_primitive_opt (...) |> Option.is_some`,
  then immediately matching the same expression; the `None` arm cannot be
  selected without mutation between the guard and match.
- `Inlined_record_expected`: covered by
  `tests/error_output_parity/compiler/fixtures/inlined_record_expected.res`.
- `Invalid_extension_constructor_payload`: covered by
  `tests/error_output_parity/compiler/fixtures/invalid_extension_constructor_payload.res`.
- `Not_an_extension_constructor`: covered by
  `tests/error_output_parity/compiler/fixtures/not_an_extension_constructor.res`.
- `Inlined_record_escape`: covered by
  `tests/error_output_parity/compiler/fixtures/inlined_record_escape.res`.
- `Type_params_not_supported`: covered by
  `tests/error_output_parity/compiler/fixtures/type_params_not_supported_variant_spread.res`.
- `Field_access_on_dict_type`: covered by
  `tests/error_output_parity/compiler/fixtures/field_access_on_dict_type.res`.
- `Typemod.Not_a_packed_module`: covered by
  `tests/error_output_parity/compiler/fixtures/unpack_not_a_packed_module.res`.
- `Break_outside_loop`: covered by
  `tests/error_output_parity/compiler/fixtures/break_outside_loop.res`.
- `Continue_outside_loop`: covered by
  `tests/error_output_parity/compiler/fixtures/continue_outside_loop.res`.
- `Jsx_not_enabled`: covered by
  `tests/error_output_parity/compiler/cases/jsx_not_enabled.res` through the
  explicit no-`-bs-jsx` compiler case in
  `tests/error_output_parity/compiler/cases.tsv`.
- Typecore statement-position type errors are covered by
  `tests/error_output_parity/compiler/fixtures/typecore_error_statement_type_clash.res`.
- Typecore warning 5 (`Partial_application`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_partial_application.res`.
- Typecore warning 9 (`Non_closed_record_pattern`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_non_closed_record_pattern.res`.
- Typecore warning 20 (`Unused_argument`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_unused_argument.res`.
- Typecore warning 21 (`Nonreturning_statement`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_nonreturning_statement.res`.
- Typecore warning 23 (`Useless_record_with`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_useless_record_with.res`.
- Typecore warning 26 (`Unused_var`) and warning 27 (`Unused_var_strict`) are
  covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_unused_function_param.res`,
  `tests/error_output_parity/compiler/fixtures/typecore_warning_unused_variable.res`
  and
  `tests/error_output_parity/compiler/fixtures/typecore_warning_unused_variable_strict.res`.
- Typecore warning 28 (`Wildcard_arg_to_constant_constr`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_wildcard_constant_constructor.res`.
- Typecore warning 35 (`Unused_for_index`) is covered for `for`, `for of`, and
  `for await of` by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_unused_for_index.res`,
  `tests/error_output_parity/compiler/fixtures/typecore_warning_unused_for_of_index.res`,
  and
  `tests/error_output_parity/compiler/fixtures/typecore_warning_unused_for_await_index.res`.
- Typecore warning 39 (`Unused_rec_flag`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_unused_rec_flag.res`.
- Typecore warning 41 (`Ambiguous_name`) is covered for record labels and
  constructors by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_ambiguous_record_name.res`
  and
  `tests/error_output_parity/compiler/fixtures/constructor_warning_ambiguous_name.res`;
  ordering with open-shadow warning 45 is covered by
  `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_constructor_with_ambiguous_name.res`.
- Typecore warning 43 (`Nonoptional_label`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_nonoptional_label.res`.
- Typecore warning 52 (`Fragile_literal_pattern`) is covered by
  `tests/error_output_parity/compiler/fixtures/typecore_warning_fragile_literal_pattern.res`.

## Typetexp Coverage Notes

- `Unbound_module`: covered for the generated JSX `ReactDOM` lookup by
  `tests/error_output_parity/compiler/fixtures/jsx_generated_unbound_reactdom.res`
  and for direct module access by `tests/error_output_parity/compiler/fixtures/unbound_module.res`.
  Additional coverage includes the qualified type-constructor parent lookup path
  in
  `tests/error_output_parity/compiler/fixtures/unbound_type_constructor_parent_module.res`,
  the `Str` special message branch in
  `tests/error_output_parity/compiler/fixtures/unbound_module_str.res`,
  the module spellcheck branch in
  `tests/error_output_parity/compiler/fixtures/unbound_module_spellcheck.res`,
  the `module type of` lookup paths in
  `tests/error_output_parity/compiler/fixtures/module_type_of_unbound_module.res`
  and
  `tests/error_output_parity/compiler/fixtures/module_type_of_unbound_qualified_module.res`,
  the module-type alias lookup path in
  `tests/error_output_parity/compiler/fixtures/module_type_alias_unbound_module.res`,
  the extension-rebind lookup path in
  `tests/error_output_parity/compiler/fixtures/rebind_unbound_qualified_module.res`,
  and the `with module` right-hand side lookup paths in
  `tests/error_output_parity/compiler/fixtures/with_module_equation_unbound_module.res`
  and
  `tests/error_output_parity/compiler/fixtures/with_module_unbound_module.res`.
- `Unbound_value`: covered by
  `tests/error_output_parity/compiler/fixtures/unbound_value.res`, the
  qualified value branch in
  `tests/error_output_parity/compiler/fixtures/unbound_value_in_module.res`,
  the spellcheck branch in
  `tests/error_output_parity/compiler/fixtures/unbound_value_spellcheck.res`,
  the module-name suggestion branch in
  `tests/error_output_parity/compiler/fixtures/unbound_value_module_suggestion.res`,
  and the combined spellcheck/module-name suggestion branch in
  `tests/error_output_parity/compiler/fixtures/unbound_value_spellcheck_and_module_suggestion.res`.
- `Unbound_constructor`: covered by
  `tests/error_output_parity/compiler/fixtures/unbound_constructor.res`, the
  qualified constructor branch in
  `tests/error_output_parity/compiler/fixtures/unbound_constructor_qualified.res`,
  the spellcheck branch in
  `tests/error_output_parity/compiler/fixtures/unbound_constructor_spellcheck.res`,
  the constructor-expression payload location branch in
  `tests/error_output_parity/compiler/fixtures/unbound_constructor_payload_loc.res`,
  and the extension-rebind lookup paths in
  `tests/error_output_parity/compiler/fixtures/rebind_unbound_constructor.res`
  and
  `tests/error_output_parity/compiler/fixtures/rebind_unbound_qualified_constructor.res`.
- `Unbound_type_constructor`: covered by
  `tests/error_output_parity/compiler/fixtures/unbound_type_constructor.res`
  and the type spellcheck hint in
  `tests/error_output_parity/compiler/fixtures/unbound_type_constructor_spellcheck.res`.
- `Unbound_type_constructor_2`: covered for a recursive polyvariant
  inheritance before the type is fully defined by
  `tests/error_output_parity/compiler/fixtures/unbound_type_constructor_incomplete.res`.
- `Unbound_type_variable`: covered through direct and nested type declaration
  manifests, wildcard variables, variant constructor payloads, and record
  fields by
  `tests/error_output_parity/compiler/fixtures/unbound_type_variable.res`,
  `tests/error_output_parity/compiler/fixtures/unbound_type_var_alias.res`,
  `tests/error_output_parity/compiler/fixtures/unbound_type_variable_wildcard.res`,
  `tests/error_output_parity/compiler/fixtures/unbound_type_var_decl.res`,
  and
  `tests/error_output_parity/compiler/fixtures/unbound_type_var_record.res`.
- `Type_arity_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/type_arity_mismatch.res`
  and
  `tests/error_output_parity/compiler/fixtures/type_arity_mismatch_nongeneric.res`.
- `Type_mismatch`: covered for constrained type constructor arguments by
  `tests/error_output_parity/compiler/fixtures/typetexp_type_mismatch.res`.
- `Alias_type_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/typetexp_alias_type_mismatch.res`.
- `Invalid_variable_name`: covered for type parameters and type expressions by
  `tests/error_output_parity/compiler/fixtures/invalid_type_parameter_name.res`
  and
  `tests/error_output_parity/compiler/fixtures/invalid_type_variable_name.res`.
- `Cannot_quantify`: covered for the non-variable alias branch and the
  already-bound universal branch, and the `Tvar`/`it escapes its scope` branch
  by `tests/error_output_parity/compiler/fixtures/cannot_quantify_alias.res`,
  `tests/error_output_parity/compiler/fixtures/cannot_quantify_already_bound.res`,
  and
  `tests/error_output_parity/compiler/fixtures/cannot_quantify_escapes_scope.res`.
  The escape branch depends on the locally abstract type sugar using
  `Ast_helper.Typ.varify_constructors` for the pattern-side type scheme while
  leaving the expression-side constraint as a local abstract type constructor.
- `Multiple_constraints_on_type`: covered for package type constraints by
  `tests/error_output_parity/compiler/fixtures/multiple_constraints_on_package_type.res`.
- `Present_has_conjunction`: covered by
  `tests/error_output_parity/compiler/fixtures/present_variant_has_conjunction.res`.
- `Present_has_no_type`: covered by
  `tests/error_output_parity/compiler/fixtures/present_variant_has_no_type.res`.
- `Constructor_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/polyvariant_constructor_mismatch.res`.
- `Not_a_variant`: covered for non-variant constructors and the type-variable
  hint branch by
  `tests/error_output_parity/compiler/fixtures/typetexp_not_a_variant.res` and
  `tests/error_output_parity/compiler/fixtures/typetexp_not_a_variant_type_var_hint.res`.
- `Variant_tags`: covered by polymorphic variant hash collisions in row type
  translation, expression unification, and pattern unification by
  `tests/error_output_parity/compiler/fixtures/polyvariant_hash_collision_type.res`,
  `tests/error_output_parity/compiler/fixtures/variant_tags_collision.res`,
  and
  `tests/error_output_parity/compiler/fixtures/polyvariant_hash_collision_pattern.res`.
- `Opened_object`: covered by
  `tests/error_output_parity/compiler/fixtures/typetexp_opened_object.res`.
- `Not_an_object`: covered by
  `tests/error_output_parity/compiler/fixtures/typetexp_not_an_object.res`.
- `Method_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/typetexp_method_mismatch.res`.
- `Unbound_label`: covered for an untyped record literal with no label in
  scope by `tests/error_output_parity/compiler/fixtures/unbound_label.res`,
  receiver-specific option/array/non-record messages by
  `tests/error_output_parity/compiler/fixtures/unbound_label_option_receiver.res`,
  `tests/error_output_parity/compiler/fixtures/unbound_label_array_receiver.res`
  and
  `tests/error_output_parity/compiler/fixtures/unbound_label_non_record_receiver.res`,
  and the label spellcheck hint by
  `tests/error_output_parity/compiler/fixtures/unbound_label_spellcheck.res`.
- `Unbound_modtype`: covered by
  `tests/error_output_parity/compiler/fixtures/unbound_modtype.res`, the
  qualified module-type path in
  `tests/error_output_parity/compiler/fixtures/unbound_modtype_qualified.res`,
  the spellcheck branch in
  `tests/error_output_parity/compiler/fixtures/unbound_modtype_spellcheck.res`,
  and the signature-item lookup path in
  `tests/error_output_parity/compiler/fixtures/signature_unbound_modtype.res`.
- `Access_functor_as_structure`: covered by
  `tests/error_output_parity/compiler/fixtures/access_functor_as_structure.res`.
- `Ill_typed_functor_application`: covered by
  `tests/error_output_parity/compiler/fixtures/ill_typed_functor_application_type_path.res`.
- `Apply_structure_as_functor`: covered by
  `tests/error_output_parity/compiler/fixtures/apply_structure_as_functor_type_path.res`.
- `Illegal_reference_to_recursive_module`: covered by
  `tests/error_output_parity/compiler/fixtures/illegal_reference_to_recursive_module.res`.
  A non-error parity guard for OCaml's recursive-module inclusion unrolling is
  also covered by
  `tests/error_output_parity/compiler/fixtures/recursive_module_sibling_type_alias.res`.
- `Cannot_scrape_alias`: covered for type paths by
  `tests/error_output_parity/compiler/cases/cannot_scrape_alias_type_path.res`
  and for `module type of ... with ...` constraints by
  `tests/error_output_parity/compiler/cases/cannot_scrape_alias_module_type_with.res`.

## `compiler/ml/typetexp.ml`

- `Unbound_type_variable`
- `Unbound_type_constructor`
- `Unbound_type_constructor_2`
- `Type_arity_mismatch`
- `Type_mismatch`
- `Alias_type_mismatch`
- `Present_has_conjunction`
- `Present_has_no_type`
- `Constructor_mismatch`
- `Not_a_variant`
- `Variant_tags`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/polyvariant_hash_collision_type.res`,
    `tests/error_output_parity/compiler/fixtures/variant_tags_collision.res`,
    and
    `tests/error_output_parity/compiler/fixtures/polyvariant_hash_collision_pattern.res`.
- `Invalid_variable_name`
- `Cannot_quantify`
- `Multiple_constraints_on_type`
- `Method_mismatch`
- `Unbound_value`
- `Unbound_constructor`
- `Unbound_label`
- `Unbound_module`
- `Unbound_modtype`
- `Ill_typed_functor_application`
- `Illegal_reference_to_recursive_module`
- `Access_functor_as_structure`
- `Apply_structure_as_functor`
- `Cannot_scrape_alias`
- `Opened_object`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/typetexp_opened_object.res`.
- `Not_an_object`

## `compiler/ml/typedecl.ml`

- `Repeated_parameter`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/repeated_type_parameter.res`.
- `Duplicate_constructor`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/duplicate_constructor.res`.
- `Duplicate_label`
  - Covered for direct duplicate fields and duplicate fields introduced by
    record type spread by
    `tests/error_output_parity/compiler/fixtures/duplicate_label.res` and
    `tests/error_output_parity/compiler/fixtures/duplicate_label_record_spread.res`.
- `Warnings.Duplicate_definitions`
  - Covered for duplicate constructor and record label names across recursive
    type declarations by
    `tests/error_output_parity/compiler/fixtures/typedecl_warning_duplicate_constructor_definition.res`
    and
    `tests/error_output_parity/compiler/fixtures/typedecl_warning_duplicate_label_definition.res`;
    the signature translation path is covered by
    `tests/error_output_parity/compiler/fixtures/typedecl_warning_duplicate_constructor_definition_signature.resi`.
- `Warnings.Constraint_on_gadt`
  - Covered for implementation and signature declarations by
    `tests/error_output_parity/compiler/fixtures/typedecl_warning_constraint_on_gadt.res`
    and
    `tests/error_output_parity/compiler/fixtures/typedecl_warning_constraint_on_gadt_signature.resi`.
- `Object_spread_with_record_field`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/object_spread_with_record_field.res`.
- `Recursive_abbrev`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/recursive_abbrev.res`
    and recursive-module constraint paths in
    `tests/error_output_parity/compiler/fixtures/recursive_module_self_type_abbrev.res`
    and
    `tests/error_output_parity/compiler/fixtures/recursive_module_container_type_abbrev.res`.
- `Cycle_in_def`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/cycle_in_def.res`,
    `tests/error_output_parity/compiler/fixtures/parameters_differ.res`,
    and the recursive-module constraint path in
    `tests/error_output_parity/compiler/fixtures/recursive_module_indirect_type_abbrev.res`.
- `Definition_mismatch`
  - Covered for constructor-name and constructor-payload mismatches in an
    equation plus variant representation by
    `tests/error_output_parity/compiler/fixtures/definition_mismatch.res` and
    `tests/error_output_parity/compiler/fixtures/definition_mismatch_payload.res`.
- `Constraint_failed`
  - Covered for GADT constructor return-type validation and recursive
    abbreviation expansion parameter validation by
    `tests/error_output_parity/compiler/fixtures/constraint_failed_constructor_return.res`
    and
    `tests/error_output_parity/compiler/fixtures/constraint_failed_recursion.res`.
- `Inconsistent_constraint`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/inconsistent_type_constraint.res`.
- `Type_clash`
  - Covered for recursive manifest stub update failure by
    `tests/error_output_parity/compiler/fixtures/type_clash_recursive_manifest.res`.
- `Parameters_differ`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/parameters_differ_object_poly_recursion.res`.
- `Null_arity_external`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/null_arity_external.res`.
- `Unbound_type_var`
  - Checked: normal `.res`/`.resi` unbound type-parameter positions found so
    far are rejected earlier by `Typetexp.Unbound_type_variable`, before the
    later `Typedecl.closed_type_decl` check can report this verbose internal
    variant. The observable type-expression paths are covered in the
    `Typetexp.Unbound_type_variable` section.
- `Cannot_extend_private_type`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/cannot_extend_private_type.res`.
- `Not_extensible_type`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/not_extensible_type.res`.
- `Extension_mismatch`
  - Covered by arity and variance cases:
    `tests/error_output_parity/compiler/fixtures/extension_mismatch_arity.res`,
    `tests/error_output_parity/compiler/fixtures/extension_mismatch_variance.res`.
- `Rebind_wrong_type`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/rebind_wrong_type.res`.
- `Rebind_mismatch`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/rebind_mismatch.res`.
- `Rebind_private`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/rebind_private.res`.
- `Bad_variance`
  - Covered for direct annotated parameter variance mismatch, including
    `1st`, `2nd`, `3rd`, and default ordinal suffix wording, by
    `tests/error_output_parity/compiler/fixtures/bad_variance.res`,
    `tests/error_output_parity/compiler/fixtures/bad_variance_second_parameter.res`,
    `tests/error_output_parity/compiler/fixtures/bad_variance_third_parameter.res`,
    and
    `tests/error_output_parity/compiler/fixtures/bad_variance_fourth_parameter.res`.
  - Covered for constrained-parameter propagation code `-1` by
    `tests/error_output_parity/compiler/fixtures/bad_variance_constrained_parameter_propagation.res`.
  - Covered for constrained-parameter propagation report codes `-2` and `-3` by
    `tests/error_output_parity/compiler/fixtures/bad_variance_constrained_parameter_nondeducible.res`
    and
    `tests/error_output_parity/compiler/fixtures/bad_variance_constrained_parameter_undeduced_variance.res`.
- `Unavailable_type_constructor`
  - Not reachable from normal `.res`/`.resi` source found so far. The OCaml
    raise sites are second-pass checks over already translated `Tconstr` nodes
    in `check_constraints_rec` and `check_coherence`; missing source-level type
    constructors are rejected earlier by type expression translation, while
    recursive placeholders are all installed in the final declaration env before
    these checks run.
- `Bad_fixed_type`
  - Covered for fixed polymorphic variant rows without a row variable and
    private manifests that are not object or variant types by
    `tests/error_output_parity/compiler/fixtures/bad_fixed_type_no_row.res` and
    `tests/error_output_parity/compiler/fixtures/bad_fixed_type_not_object_or_variant.res`.
- `Unbound_type_var_ext`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/unbound_type_var_ext.res`.
- `Varying_anonymous`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/varying_anonymous.res`.
- `Val_in_structure`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/val_in_structure.res`.
    ReScript parses a bare annotated value declaration in implementation syntax
    to `Pstr_primitive` with no primitive, which reaches
    `Typedecl.transl_value_decl` and reports `Val_in_structure`.
- `Invalid_attribute`
  - Covered for `@notUndefined` misuse by
    `tests/error_output_parity/compiler/fixtures/invalid_not_undefined_attribute.res`.
- `Bad_immediate_attribute`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bad_immediate_attribute.res`.
- `Bad_unboxed_attribute`
  - Covered for abstract, mutable record, multi-field record, and extensible
    variant declarations by
    `tests/error_output_parity/compiler/fixtures/bad_unboxed_abstract.res`,
    `tests/error_output_parity/compiler/fixtures/bad_unboxed_mutable_record.res`,
    `tests/error_output_parity/compiler/fixtures/bad_unboxed_multi_field_record.res`,
    and
    `tests/error_output_parity/compiler/fixtures/bad_unboxed_extensible_variant.res`.
- `Boxed_and_unboxed`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/boxed_and_unboxed.res`.
- `Nonrec_gadt`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/nonrec_gadt.res`.
- `Variant_runtime_representation_mismatch`
  - Covered for spread-time unboxed and `@tag` mismatches by
    `tests/error_output_parity/compiler/fixtures/variant_spread_unboxed_mismatch.res`
    and
    `tests/error_output_parity/compiler/fixtures/variant_spread_tag_mismatch.res`.
- `Variant_spread_fail`
  - Covered for `CouldNotFindType`, `InvalidType`, `HasTypeParams`, and
    `DuplicateConstructor` by
    `tests/error_output_parity/compiler/fixtures/variant_spread_could_not_find_type.res`,
    `tests/error_output_parity/compiler/fixtures/variant_spread_invalid_type.res`,
    `tests/error_output_parity/compiler/fixtures/variant_spread_has_type_params.res`,
    and
    `tests/error_output_parity/compiler/fixtures/variant_spread_duplicate_constructor.res`.

## `compiler/ml/typemod.ml`

- `Cannot_apply`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/cannot_apply_module.res`.
- `Not_included`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/not_included_value_mismatch.res`
    and the functor-argument inclusion path in
    `tests/error_output_parity/compiler/fixtures/functor_argument_mismatch.res`.
- `Cannot_eliminate_dependency`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/cannot_eliminate_dependency.res`.
- `Signature_expected`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/signature_expected_package_constraint.res`
    and the signature `include` functor branch in
    `tests/error_output_parity/compiler/fixtures/signature_expected_include_functor.res`.
- `Structure_expected`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/structure_expected_open_functor.res`
    and the include path in
    `tests/error_output_parity/compiler/fixtures/structure_expected_include_functor.res`.
- `With_no_component`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/with_no_component_type.res`.
- `With_mismatch`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/with_mismatch_type.res`.
- `With_makes_applicative_functor_ill_typed`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/with_makes_applicative_functor_ill_typed.res`.
- `With_changes_module_alias`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/with_changes_module_alias.res`.
- `With_cannot_remove_constrained_type`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/with_cannot_remove_constrained_type.res`.
- `Repeated_name`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/repeated_module_name.res`.
- `Non_generalizable`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/non_generalizable_ref_none.res`.
- `Non_generalizable_module`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/non_generalizable_module.res`
    and the `module type of` branch in
    `tests/error_output_parity/compiler/fixtures/module_type_of_non_generalizable.res`.
- `Interface_not_compiled`
  - Covered by
    `tests/error_output_parity/compiler/cases/interface_not_compiled.res`.
- `Not_allowed_in_functor_body`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/not_allowed_in_functor_body.res`.
- `Not_a_packed_module`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/unpack_not_a_packed_module.res`.
- `Incomplete_packed_module`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/incomplete_packed_module.res`.
- `Scoping_pack`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/package_scoping_pack_local_type.res`.
- `Recursive_module_require_explicit_type`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/recursive_module_requires_explicit_type.res`.
- `Apply_generative`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/apply_generative_functor.res`.
- `Cannot_scrape_alias`
  - Covered by
    `tests/error_output_parity/compiler/cases/cannot_scrape_alias_module_type_with.res`.

## `compiler/frontend/bs_syntaxerr.ml`

- `Unsupported_predicates`
  - Covered for method `@get` and `@set` payload predicates by
    `tests/error_output_parity/compiler/fixtures/bs_get_unsupported_predicate.res`
    and
    `tests/error_output_parity/compiler/fixtures/bs_set_unsupported_predicate.res`.
- `Conflict_bs_bs_this_bs_meth`
  - No active raise site found in the current source; keep listed so the
    variant is rechecked if frontend attribute handling changes.
- `Duplicated_bs_deriving`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_duplicate_deriving.res`.
- `Conflict_attributes`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_conflict_type_ffi_attrs.res`.
- `Expect_int_literal`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_int_as_expect_int_literal.res`.
- `Expect_string_literal`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_string_as_expect_string_literal.res`.
- `Expect_int_or_string_or_json_literal`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_as_expect_int_string_json_literal.res`.
- Duplicate `@as` handling in `iter_process_bs_string_as`,
  `iter_process_bs_int_as`, and `iter_process_bs_string_or_int_as`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_string_as_duplicate.res`,
    `tests/error_output_parity/compiler/fixtures/bs_int_as_duplicate.res`,
    and
    `tests/error_output_parity/compiler/fixtures/bs_as_duplicate.res`.
- `Unhandled_poly_type`
  - Checked: raised by `Ast_core_type.list_of_arrow` when an external type
    contains `Ptyp_poly` in the arrow spine, but normal `.res` external syntax
    is rejected by the OCaml parser before this frontend raise site is
    observable. The source-level guard is covered by
    `tests/error_output_parity/compiler/fixtures/bs_external_unhandled_poly_type.res`;
    it verifies Rust follows OCaml's parser entry-point split and rejects the
    attempted nested polytype before frontend external processing.
- `Invalid_underscore_type_in_external`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_invalid_underscore_external.res`.
- `Invalid_bs_string_type`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_invalid_string_external_arg.res`.
- `Invalid_bs_int_type`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_invalid_int_external_arg.res`.
- `Invalid_bs_unwrap_type`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_invalid_unwrap_external_arg.res`.
- `Invalid_bs_string_type` / `Invalid_bs_int_type` `@as` payload subcases
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_string_as_expect_string_literal.res`
    and
    `tests/error_output_parity/compiler/fixtures/bs_int_as_expect_int_literal.res`.
- `Conflict_ffi_attribute`
  - Covered for `@get_index` and `@set_index` conflicts by
    `tests/error_output_parity/compiler/fixtures/bs_conflict_get_index_module.res`
    and
    `tests/error_output_parity/compiler/fixtures/bs_conflict_set_index_module.res`.
    Covered for the remaining observable `compiler/frontend/ast_external_process.ml`
    conflict-message branches by
    `tests/error_output_parity/compiler/fixtures/bs_conflict_module_send.res`,
    `tests/error_output_parity/compiler/fixtures/bs_conflict_module_val.res`,
    `tests/error_output_parity/compiler/fixtures/bs_conflict_module_value_new.res`,
    `tests/error_output_parity/compiler/fixtures/bs_conflict_new_get.res`,
    `tests/error_output_parity/compiler/fixtures/bs_conflict_val_call_send.res`,
    and
    `tests/error_output_parity/compiler/fixtures/bs_conflict_val_value_new.res`.
- `Illegal_attribute`
  - Covered for `@module` arity and empty `@scope` by
    `tests/error_output_parity/compiler/fixtures/bs_external_illegal_module_many_strings.res`
    and
    `tests/error_output_parity/compiler/fixtures/bs_external_illegal_scope_empty.res`.
- `Not_supported_directive_in_bs_return`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_return_unknown_directive.res`.
- `Expect_opt_in_bs_return_to_opt`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_return_to_opt_non_option.res`.
  - FFI name validation preempts this return-result validation in
    `Ast_external_process.handle_attributes`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_return_empty_global_name.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_module_return_empty_module_name.res`.
- `Misplaced_label_syntax`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_misplaced_label_syntax.res`.
- `Optional_in_uncurried_bs_attribute`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_this_optional_arg.res`.
- `Bs_this_simple_pattern`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/bs_this_simple_pattern.res`.
- `Experimental_feature_not_enabled`
  - Covered through the included super error fixture
    `tests/build_tests/super_errors/fixtures/feature_letunwrap_not_enabled.res`.
- `LetUnwrap_not_supported_in_position`
  - Covered through the included super error fixtures
    `tests/build_tests/super_errors/fixtures/let_unwrap_on_top_level.res`
    and
    `tests/build_tests/super_errors/fixtures/let_unwrap_on_not_supported_variant.res`.

## Ast_untagged_variants Coverage Notes

- `InvalidVariantAsAnnotation`: covered by
  `tests/error_output_parity/compiler/fixtures/untagged_invalid_as_annotation.res`.
- `Duplicated_bs_as`: covered by
  `tests/error_output_parity/compiler/fixtures/untagged_duplicate_as.res`.
- `Ast_payload.is_single_int` overflow through `@as(...)`: covered by
  `tests/error_output_parity/compiler/fixtures/untagged_as_int_overflow.res`.
- `InvalidVariantTagAnnotation`: covered by
  `tests/error_output_parity/compiler/fixtures/untagged_invalid_tag_annotation.res`.
- `TagFieldNameConflict`: covered by
  `tests/error_output_parity/compiler/fixtures/untagged_tag_field_conflict.res`.
- `InvalidUntaggedVariantDefinition`: covered across the reachable subcases by
  `tests/error_output_parity/compiler/fixtures/untagged_constructor_more_than_one_arg.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_duplicate_string_literal.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_duplicate_nonstring_literal.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_only_one_unknown.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_object.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_array.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_promise.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_date.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_recursive_promise_alias_collision.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_recursive_promise_alias_collision.resi`,
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_function.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_string.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_number.res`,
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_bigint.res`,
  and
  `tests/error_output_parity/compiler/fixtures/untagged_at_most_one_boolean.res`.

## Other Compiler Error Surfaces

- `compiler/ml/env.ml`
  - `Illegal_renaming`
    - Covered by
      `tests/error_output_parity/compiler/cases/illegal_renaming.res`.
  - `Inconsistent_import`
    - Covered by
      `tests/error_output_parity/compiler/cases/inconsistent_import.res`.
  - `Missing_module`
    - Covered by
      `tests/error_output_parity/compiler/cases/missing_module.res`.
  - `Illegal_value_name`
    - Covered by
      `tests/error_output_parity/compiler/cases/illegal_value_name.res`.
  - Delayed unused value/type/module warnings for implementation bindings
    hidden by an explicit module constraint
    - Covered by
      `tests/error_output_parity/compiler/fixtures/unused_value_hidden_by_module_constraint.res`,
      `tests/error_output_parity/compiler/fixtures/unused_type_hidden_by_module_constraint.res`,
      and
      `tests/error_output_parity/compiler/fixtures/unused_module_hidden_by_module_constraint.res`.
  - `Warnings.Open_shadow_identifier` value, type, module, and module-type
    shadowing from an `open`, reported only when the opened item is later used
    - Covered by
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_identifier.res`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_type.res`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_module.res`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_modtype.res`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_same_value_reopen.res`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_same_type_reopen.res`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_same_module_reopen.res`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_signature_type.resi`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_signature_module.resi`,
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_signature_modtype.resi`,
      and
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_same_modtype_reopen.res`.
  - `Warnings.Open_shadow_label_constructor` constructor and label shadowing from
    an `open`, reported only when the opened constructor or label is later used
    - Covered by
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_constructor.res`
      and
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_label.res`.
    - Ordering with constructor warning 41 is covered by
      `tests/error_output_parity/compiler/fixtures/env_warning_open_shadow_constructor_with_ambiguous_name.res`.
- `compiler/ml/rec_check.ml`
  - `Illegal_letrec_expr`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/illegal_letrec_expr.res`.
- `compiler/ml/syntaxerr.ml`
  - `Variable_in_scope`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/variable_in_scope.res`.
- `compiler/ml/ast_mapper.ml`
  - `PpxContext.restore` malformed `[@@@ocaml.ppx.context]` diagnostics are
    not reached from normal `.res`/`.resi` source in the current compiler
    pipeline. A source-level `@@ocaml.ppx.context(1)` probe compiles without
    invoking the restore path; external PPX process failures are covered
    separately under `Ast_exp_handle_external`.
- `bsc -bs-ast` parser entrypoint
  - Structure and signature parse diagnostics are rendered through the compiler
    binary, not only through `res_parser`
    - Covered by
      `tests/error_output_parity/compiler/cases/bs_ast_parse_error.res`
      and
      `tests/error_output_parity/compiler/cases/bs_iast_parse_error.resi`.
- `bsc -warn-error` CLI handling
  - Warning-as-error specifications use OCaml's `Warnings.parse_options true`
    semantics, so `-warn-error +A` sets the error flags rather than merely
    activating warnings
    - Covered by
      `tests/error_output_parity/compiler/cases/warn_error_unused_variable.res`.
- `compiler/syntax/src/res_core.ml`
  - `parse_external_def` requires the `=` before an external primitive name
    - Covered through `res_parser` by
      `tests/syntax_tests/data/parsing/errors/structure/externalMissingPrimitive.res`
      and through `bsc` by
      `tests/error_output_parity/compiler/fixtures/external_missing_primitive.res`.
  - `parse_type_constructor_declaration` reports `Diagnostics.uident` for
    non-uppercase variant constructor names and preserves OCaml's dummy `_`
    recovery constructor in `-recover -print ml` output
    - Covered through `res_parser` by
      `tests/syntax_tests/data/parsing/errors/typeDef/variantConstructorName.res`
      and through `bsc` by
      `tests/error_output_parity/compiler/fixtures/variant_constructor_lowercase_name.res`
      and
      `tests/error_output_parity/compiler/fixtures/variant_constructor_reserved_keyword.res`.
  - Constructor payload type expressions reject uppercase type names and keep
    the same follow-on recovery diagnostics for angle and paren arguments
    - Covered by
      `tests/error_output_parity/compiler/fixtures/parser_uppercase_constructor_payload_type.res`,
      `tests/error_output_parity/compiler/fixtures/parser_uppercase_constructor_payload_type_angle_args.res`,
      and
      `tests/error_output_parity/compiler/fixtures/parser_uppercase_constructor_payload_type_paren_args.res`.
  - Uppercase type arguments in functor-tail type paths avoid a cascading dot
    diagnostic after the primary lowercase-name diagnostic
    - Covered by
      `tests/error_output_parity/compiler/fixtures/parser_uppercase_type_arg_functor_tail.res`.
  - Type-parameter constraints inside module-type `with type` constraints
    reject the `constraint` reserved keyword at the parser layer
    - Covered by
      `tests/error_output_parity/compiler/fixtures/with_type_constraint_keyword.res`.
  - `parse_payload` stops attribute payload structure parsing at a comma before
    `Parser.expect Rparen`, preserving the reference parser diagnostic and
    recovery AST for unsupported comma-separated payloads
    - Covered through `res_parser` by
      `tests/syntax_tests/data/parsing/errors/structure/attributePayloadComma.res`
      and through `bsc` by
      `tests/error_output_parity/compiler/fixtures/attribute_payload_comma.res`.
  - `is_es6_arrow_expression` classifies parenthesized parameters followed by
    a non-ternary `:` as arrow candidates before parsing the return type, which
    preserves OCaml's missing-`=>` recovery for polymorphic return annotations
    - Covered through `res_parser` by
      `tests/syntax_tests/data/parsing/errors/expressions/arrowReturnPolytype.res`
      and through `bsc` by
      `tests/error_output_parity/compiler/fixtures/arrow_return_polytype_recovery.res`.
  - `parse_jsx_prop` rejects uppercase JSX prop names before JSX PPX/type
    checking
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_jsx_uppercase_prop.res`.
  - `parse_jsx_children` rejects the removed spread-child syntax before JSX
    PPX expansion
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_jsx_spread_children.res`.
  - `parse_record_expr` rejects both non-initial record spreads and spreads
    without any updated fields
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_record_spread_second.res`
      and
      `tests/error_output_parity/compiler/fixtures/parser_record_spread_no_update.res`.
  - Tuple parsing rejects singleton tuples in expression and type contexts
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_tuple_single_expression.res`
      and
      `tests/error_output_parity/compiler/fixtures/parser_tuple_single_type.res`.
  - Type declaration parsing rejects record fields written with `=`, unquoted
    object fields, and local type definitions inside functions
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_record_type_field_equal.res`,
      `tests/error_output_parity/compiler/fixtures/parser_object_unquoted_field_type.res`,
      and
      `tests/error_output_parity/compiler/fixtures/parser_type_definition_in_function.res`.
  - Structure and signature item parsers reject single-`@` attributes with no
    attached node, preserving the standalone-attribute suggestion
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_standalone_attribute_structure.res`
      and
      `tests/error_output_parity/compiler/fixtures/parser_standalone_attribute_signature.resi`.
  - Expression parsing rejects unparenthesized type constraints, non-identifier
    tagged-template receivers, and labelled call arguments written with `:` or
    `:?`
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_expression_constraint_needs_parens.res`,
      `tests/error_output_parity/compiler/fixtures/parser_tagged_template_limited_receiver.res`,
      `tests/error_output_parity/compiler/fixtures/parser_labelled_argument_missing_equal.res`,
      and
      `tests/error_output_parity/compiler/fixtures/parser_optional_labelled_argument_missing_equal.res`.
  - `for` parsing rejects missing `in`/`of`, and rejects `for await ... in`
    before type checking
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_for_loop_missing_in_or_of.res`
      and
      `tests/error_output_parity/compiler/fixtures/parser_for_await_in.res`.
  - `let?` parser diagnostics reject recursive bindings and signature items
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_let_unwrap_rec.res`
      and
      `tests/error_output_parity/compiler/fixtures/parser_let_unwrap_signature.resi`.
  - Type declaration parsing rejects module-qualified declaration names,
    misplaced record field doc comments, and multiple inline records at the
    same generated field path
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_type_declaration_longident.res`,
      `tests/error_output_parity/compiler/fixtures/parser_record_doc_comment_field_position.res`,
      and
      `tests/error_output_parity/compiler/fixtures/parser_multiple_inline_record_definitions.res`.
  - Pattern parsing rejects array/list/record spread forms and string
    interpolation inside template literal patterns
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_array_pattern_spread.res`,
      `tests/error_output_parity/compiler/fixtures/parser_list_pattern_spread.res`,
      `tests/error_output_parity/compiler/fixtures/parser_record_pattern_spread.res`,
      and
      `tests/error_output_parity/compiler/fixtures/parser_string_interpolation_pattern.res`.
  - Switch parsing rejects empty case lists, and if-let emits the experimental
    parser diagnostic before type checking
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_pattern_matching_no_cases.res`
      and
      `tests/error_output_parity/compiler/fixtures/parser_if_let_experimental.res`.
  - Function and function-type parameters reject defaulted/labelled arguments
    missing the leading `~`
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_missing_tilde_function_parameter.res`
      and
      `tests/error_output_parity/compiler/fixtures/parser_missing_tilde_type_parameter.res`.
  - Numeric polymorphic variants reject identifier suffixes, and old Reason
    array syntax preserves the array-literal suggestion
    - Covered through `bsc` by
      `tests/error_output_parity/compiler/fixtures/parser_numeric_polyvariant_suffix.res`
      and
      `tests/error_output_parity/compiler/fixtures/parser_old_array_syntax.res`.
- `compiler/syntax/src/jsx_v4.ml`
  - `check_multiple_components` rejects more than one `@react.component`
    definition in the same module before generated React type lookups can mask
    the PPX error
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_multiple_definitions.res`
      and
      `tests/error_output_parity/compiler/fixtures/jsx_signature_multiple_definitions.resi`.
  - `@react.componentWithProps` value bindings do not call
    `check_multiple_components` or update `has_component`, so mixing
    `@react.component` and `@react.componentWithProps` keeps the later OCaml
    diagnostic as the source of truth
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_with_props_after_component.res`.
  - `transform_structure_item` rejects `@react.componentWithProps` on externals,
    and `map_binding` rejects `React.forwardRef` under
    `@react.componentWithProps`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_with_props_external.res`
      and
      `tests/error_output_parity/compiler/fixtures/jsx_component_with_props_forward_ref.res`.
  - `mk_record_from_props` rejects JSX spread props unless the spread appears
    before named props, and also rejects multiple spreads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_spread_after_prop.res`
      and the top-level-expression PPX traversal case in
      `tests/error_output_parity/compiler/fixtures/jsx_spread_after_prop_toplevel_expr.res`.
  - `transform_expr` rejects invalid JSX tag names before generated React type
    lookups can mask the PPX error
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_invalid_tag_trailing_dot.res`.
  - `transform_structure_item` and `transform_signature_item` reject duplicate
    `@react.component` attributes on externals and signatures
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_external_duplicate_component_attr.res`
      and
      `tests/error_output_parity/compiler/fixtures/jsx_signature_duplicate_component_attr.resi`.
  - `transform_structure_item` and `transform_signature_item` reject mixing
    `@react.component` with `@react.componentWithProps` on one external or
    signature item
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_external_mixed_component_attrs.res`
      and
      `tests/error_output_parity/compiler/fixtures/jsx_signature_mixed_component_attrs.resi`.
  - `modified_binding` rejects unlabelled props on plain component functions,
    and `modified_binding_old` rejects `@react.component` on non-functions
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_unlabelled_prop.res`
      and
      `tests/error_output_parity/compiler/fixtures/jsx_component_non_function.res`.
  - `check_string_int_attribute_iter` rejects `@string` and `@int`
    attributes inside `@react.component` external and signature types
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_external_string_attr.res`
      and
      `tests/error_output_parity/compiler/fixtures/jsx_component_signature_int_attr.resi`.
  - `recursively_transform_named_args_for_make` rejects non-plain ref
    argument patterns inside `React.forwardRef` components
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_forward_ref_bad_ref_arg.res`.
  - `get_fn_name` rejects destructuring bindings annotated as JSX components
    before generated React type lookups can mask the PPX error
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_destructure.res`.
  - `recursively_transform_named_args_for_make` rejects the reserved `key`
    prop inside `@react.component` definitions before generated React type
    lookups can mask the PPX error
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_key_prop.res`
      and the included-structure traversal case in
      `tests/error_output_parity/compiler/fixtures/jsx_component_key_prop_include.res`.
  - `make_label_decls` rejects duplicate `@react.component` prop names before
    the generated props type can mask the PPX error
    - Covered by
      `tests/error_output_parity/compiler/fixtures/jsx_component_duplicate_prop.res`,
      `tests/error_output_parity/compiler/fixtures/jsx_component_duplicate_prop_include.res`,
      `tests/error_output_parity/compiler/fixtures/jsx_component_duplicate_prop_external.res`,
      and
      `tests/error_output_parity/compiler/fixtures/jsx_component_duplicate_prop_signature.resi`.
- `compiler/syntax/src/res_scanner.ml`
  - Fixed-width string escape diagnostics for short decimal, incomplete hex,
    incomplete unicode, decimal overflow, and surrogate unicode escapes
    - Covered by
      `tests/error_output_parity/compiler/fixtures/string_escape_short_decimal.res`,
      `tests/error_output_parity/compiler/fixtures/string_escape_invalid_hex.res`,
      `tests/error_output_parity/compiler/fixtures/string_escape_invalid_unicode.res`,
      `tests/error_output_parity/compiler/fixtures/string_escape_decimal_overflow.res`,
      and
      `tests/error_output_parity/compiler/fixtures/string_escape_unicode_surrogate.res`.
- `compiler/frontend/ast_utf8_string.ml`
  - JavaScript string `\u{...}` codepoint escape validation after parsing
    - Covered by
      `tests/error_output_parity/compiler/fixtures/string_escape_codepoint_overflow.res`.
  - JavaScript string fixed-width escape validation reached through template
    literal patterns, which bypass the normal string scanner and call
    `Ast_utf8_string.transform` from `Ast_utf8_string_interp.transform_pat`
    - Covered for invalid `\x`, invalid `\u`, and UTF-8 codepoint-offset
      reporting by
      `tests/error_output_parity/compiler/fixtures/template_pattern_invalid_hex_escape.res`,
      `tests/error_output_parity/compiler/fixtures/template_pattern_invalid_unicode_escape.res`,
      and
      `tests/error_output_parity/compiler/fixtures/template_pattern_utf8_codepoint_escape.res`.
  - `Unterminated_backslash` is source-unreachable from normal `.res`/`.resi`
    compilation. A trailing backslash before a closing template backtick escapes
    the backtick in `compiler/syntax/src/res_scanner.ml:scan_template_literal_token`,
    so the parser emits the unclosed-template diagnostic before
    `Ast_utf8_string.transform` can see a string ending in `\`.
- `compiler/frontend/ast_utf8_string_interp.ml`
  - Internal interpolation segment errors such as `Unterminated_variable`,
    `Unmatched_paren`, and `Invalid_syntax_of_var` are source-unreachable from
    normal `.res`/`.resi` compilation. The compiler entry points are
    `transform_exp` and `transform_pat`; for recognized user delimiters they
    either preserve backquoted template text or delegate validation to
    `Ast_utf8_string.transform`. The segment-splitting `transform_test` path is
    only exercised by `tests/ounit_tests/ounit_unicode_tests.ml`.
- `compiler/ml/builtin_attributes.ml`
  - `error_of_extension` rejects uninterpreted expression, type, pattern,
    module expression, structure, and signature extension points
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_extension_expr_uninterpreted.res`,
      `tests/error_output_parity/compiler/fixtures/builtin_extension_type_uninterpreted.res`,
      `tests/error_output_parity/compiler/fixtures/builtin_extension_pattern_uninterpreted.res`,
      `tests/error_output_parity/compiler/fixtures/builtin_extension_module_uninterpreted.res`,
      `tests/error_output_parity/compiler/fixtures/builtin_extension_structure_uninterpreted.res`,
      and
      `tests/error_output_parity/compiler/fixtures/builtin_extension_signature_uninterpreted.resi`.
  - `error_of_extension` reports string payloads for explicit `%%error`
    extension points
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_extension_error_message.res`.
  - `error_of_extension` accepts a second string payload item as
    `if_highlight`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_extension_error_if_highlight.res`.
  - `error_of_extension` maps empty `%%error` payloads to
    `Location.Already_displayed_error`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_extension_error_already_displayed.res`
      and
      `tests/error_output_parity/compiler/fixtures/builtin_extension_error_nested_already_displayed.res`.
  - `error_of_extension` rejects invalid `%%error` payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_extension_error_invalid_payload.res`.
  - `error_of_extension` reports nested `%%error` payload items as
    sub-errors
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_extension_error_sub_message.res`.
  - `error_of_extension` rejects non-extension nested `%%error` payload
    items as invalid sub-errors
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_extension_error_invalid_sub.res`.
  - `warning_attribute` reports preprocessor warnings from `@@ppwarning`
    and illegal `@@warning` payloads/lists, and applies OCaml
    warning-as-error semantics for `@@warnerror`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_ppwarning.res`,
      `tests/error_output_parity/compiler/fixtures/builtin_warning_non_string.res`,
      `tests/error_output_parity/compiler/fixtures/builtin_warning_bad_list.res`,
      and
      `tests/error_output_parity/compiler/fixtures/builtin_warnerror_attribute.res`.
- `compiler/ml/translattribute.ml`
  - `find_attribute` reports duplicate `inline` and `inlined` attributes
    at the second attribute location
    - Covered by
      `tests/error_output_parity/compiler/fixtures/translattribute_inline_duplicate.res`
      and
      `tests/error_output_parity/compiler/fixtures/translattribute_inlined_duplicate.res`.
  - `parse_inline_attribute` reports invalid payloads for `inline` and
    `inlined`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/translattribute_inline_invalid_payload.res`
      and
      `tests/error_output_parity/compiler/fixtures/translattribute_inlined_invalid_payload.res`.
  - `check_attribute` reports misplaced expression attributes for non-function
    `inline` and non-call-target `inlined`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/translattribute_inline_misplaced_expr.res`
      and
      `tests/error_output_parity/compiler/fixtures/translattribute_inlined_misplaced_expr.res`.
  - `check_attribute_on_module` reports misplaced module attributes for
    non-functor `inline` and non-apply-target `inlined`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/translattribute_module_inline_misplaced_expr.res`
      and
      `tests/error_output_parity/compiler/fixtures/translattribute_module_inlined_misplaced_expr.res`.
  - `get_and_remove_inlined_attribute_on_module` reports invalid and duplicate
    `inlined` payloads on module apply targets
    - Covered by
      `tests/error_output_parity/compiler/fixtures/translattribute_module_inlined_invalid_payload.res`
      and
      `tests/error_output_parity/compiler/fixtures/translattribute_module_inlined_duplicate.res`.
  - `parse_inline_attribute` reports invalid module functor `inline` payloads,
    and `find_attribute` reports duplicate module functor `inline` attributes
    - Covered by
      `tests/error_output_parity/compiler/fixtures/translattribute_module_inline_invalid_payload.res`
      and
      `tests/error_output_parity/compiler/fixtures/translattribute_module_inline_duplicate.res`.
  - `add_inline_attribute` reports duplicate `inline` when binding attributes
    are applied to a function expression that already has an inline attribute
    - Covered by
      `tests/error_output_parity/compiler/fixtures/translattribute_inline_duplicate_function_expr.res`.
  - `add_inline_attribute` reports `inline1`/`inline2` when binding attributes
    cannot apply to the translated lambda
    - Covered for value bindings whose translated lambda is a non-wrapper
      `Lprim` by
      `tests/error_output_parity/compiler/fixtures/translattribute_inline_binding_lprim_misplaced_always.res`
      and
      `tests/error_output_parity/compiler/fixtures/translattribute_inline_binding_lprim_misplaced_never.res`,
      and for a module-body binding by
      `tests/error_output_parity/compiler/fixtures/translattribute_module_inline_binding_misplaced.res`.
- `compiler/ml/translcore.ml`
  - `Unknown_builtin_primitive`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/unknown_builtin_primitive.res`.
- `compiler/core/lam_convert.ml`
  - `Ffi_normal` rejects normal external primitives in the JavaScript backend
    - Covered by
      `tests/error_output_parity/compiler/cases/no_builtin_normal_external.res`.
- `compiler/ml/translmod.ml`
  - `Fragile_pattern_in_toplevel`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/fragile_pattern_in_toplevel.res`.
- `compiler/ml/transl_recmodule.ml`
  - `Circular_dependency`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/circular_recursive_module.res`
      and the `module type of` recursive-module approximation path in
      `tests/error_output_parity/compiler/fixtures/module_type_of_structure_recursive_module.res`.
- `compiler/core/lam_compile.ml`
  - Dynamic import missing/extra module argument
    - Covered by
      `tests/error_output_parity/compiler/fixtures/dynamic_import_too_many_arguments_external.res`.
      A `unit => "%import"` external reaches the unsupported-argument branch
      after unit lowering, not the empty-argument branch.
  - Dynamic import unsupported argument shape
    - Covered by
      `tests/error_output_parity/compiler/fixtures/dynamic_import_value_argument.res`,
      `tests/error_output_parity/compiler/fixtures/dynamic_import_local_value.res`,
      and
      `tests/error_output_parity/compiler/fixtures/dynamic_import_no_argument_external.res`.
- `compiler/core/lam_compile_primitive.ml`
  - `Pimport` module/file argument rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/dynamic_import_global_value.res`.
  - `Pimport` primitive arity guard
    - Documented as source-unreachable from normal ReScript: `Lam_compile`
      handles `Pimport` arity before calling `Lam_compile_primitive.translate`.
      The Rust backend still carries the same diagnostic in its lower primitive
      helper for 1:1 behavior if an invalid lambda reaches it.
  - `Pdict_has` invalid external signature
    - Covered by
      `tests/error_output_parity/compiler/fixtures/dict_has_bad_arity.res`.
  - `Warnings.Bs_polymorphic_comparison` for object comparison, ordering,
    `min`, and `max`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/polymorphic_comparison_warning.res`,
      `tests/error_output_parity/compiler/fixtures/polymorphic_comparison_less_warning.res`,
      `tests/error_output_parity/compiler/fixtures/polymorphic_comparison_order_warning.res`,
      `tests/error_output_parity/compiler/fixtures/polymorphic_comparison_min_warning.res`,
      and
      `tests/error_output_parity/compiler/fixtures/polymorphic_comparison_max_warning.res`.
- `compiler/ml/ast_payload.ml`
  - `as_core_type` / `"except a core type"` is source-unreachable from normal
    `.res`/`.resi` compilation in the current source. `rg as_core_type`
    finds no call sites outside its definition in `ast_payload.ml`.
  - `is_single_int` lets `int_of_string` overflow escape for oversized
    integer payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_int_as_overflow.res`.
  - `%re` JavaScript regex literal validation
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_re_non_regex.res`.
  - `assert_bool_lit` for method `@get`/`@set` predicate payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_get_predicate_non_bool.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_set_predicate_non_bool.res`.
  - `ident_or_record_as_config` qualified-label rejection for method
    predicate payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_get_predicate_qualified_label.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_return_qualified_label.res`.
  - `ident_or_record_as_config` invalid config-record warning before
    `@return` rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_return_qualified_ident.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_return_record_with_payload.res`.
- `compiler/frontend/ast_config.ml`
  - `Ast_payload.table_dispatch` unsupported `@@config` action
    - Covered by
      `tests/error_output_parity/compiler/fixtures/config_unknown.res`.
  - `no_export` uses `Ast_payload.assert_bool_lit`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/config_no_export_non_bool.res`.
  - Signature config table only supports file-level `flags`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/config_signature_no_export_unsupported.resi`.
  - `file_level_flags_handler` payload shape validation
    - Covered for non-array and non-string array-element cases by
      `tests/error_output_parity/compiler/fixtures/config_flags_non_array.res`
      and
      `tests/error_output_parity/compiler/fixtures/config_flags_non_string.res`.
  - `file_level_flags_handler` invalid bsc flags warning
    - Covered by
      `tests/error_output_parity/compiler/fixtures/config_bad_flags_warning.res`.
  - `file_level_flags_handler` applies warning options from `flags` with the
    same semantics as top-level bsc flags, including later type warnings and
    frontend PPX warnings
    - Covered by
      `tests/error_output_parity/compiler/fixtures/config_warn_error_unused_variable.res`
      and
      `tests/error_output_parity/compiler/fixtures/config_warn_error_raw_warning.res`.
  - `process_directives` rejects non-string file-level `@@directive` payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/directive_non_string.res`.
  - `Ast_payload.ident_or_record_as_config` invalid payload warning
    - Covered by
      `tests/error_output_parity/compiler/fixtures/config_invalid_payload_warning.res`.
- `compiler/frontend/ast_polyvar.ml`
  - `@string` redundant FFI warning for nullary polymorphic variants without
    `@as`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_string_redundant_warning.res`.
- `compiler/frontend/ast_derive*.ml`
  - `Ast_payload.table_dispatch` unsupported `@deriving` action
    - Covered by
      `tests/error_output_parity/compiler/fixtures/deriving_unsupported.res`.
  - `Ast_derive_projector.invalid_config`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/deriving_accessors_invalid_config.res`.
  - `Ast_derive_projector.raise_unsupported_vaiant_record_arg` for
    `@deriving(accessors)` on variant inline-record constructor payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/deriving_accessors_inline_record.res`
      and
      `tests/error_output_parity/compiler/fixtures/deriving_accessors_inline_record_signature.resi`.
  - `Ast_derive_js_mapper.handle_config` invalid config
    - Covered by
      `tests/error_output_parity/compiler/fixtures/deriving_jsconverter_invalid_config.res`.
  - `Ast_derive_abstract.is_abstract` invalid config
    - Covered by
      `tests/error_output_parity/compiler/fixtures/deriving_abstract_invalid_config.res`.
  - `Ast_derive_abstract.is_abstract` rejects combining `abstract` with any
    other deriving action
    - Covered by
      `tests/error_output_parity/compiler/fixtures/deriving_abstract_conflict.res`.
  - `Ast_derive_util.not_applicable` warnings for `accessors`
    - Covered for abstract and open types by
      `tests/error_output_parity/compiler/fixtures/deriving_accessors_not_applicable_abstract.res`,
      `tests/error_output_parity/compiler/fixtures/deriving_accessors_not_applicable_open.res`,
      `tests/error_output_parity/compiler/fixtures/deriving_accessors_not_applicable_abstract_signature.resi`,
      and
      `tests/error_output_parity/compiler/fixtures/deriving_accessors_not_applicable_open_signature.resi`.
  - `Ast_derive_util.not_applicable` warnings for `jsConverter`
    - Covered for regular variants, non-polyvariant abstract types, and open
      types by
      `tests/error_output_parity/compiler/fixtures/deriving_jsconverter_not_applicable_variant.res`,
      `tests/error_output_parity/compiler/fixtures/deriving_jsconverter_not_applicable_abstract.res`,
      `tests/error_output_parity/compiler/fixtures/deriving_jsconverter_not_applicable_open.res`,
      `tests/error_output_parity/compiler/fixtures/deriving_jsconverter_not_applicable_variant_signature.resi`,
      `tests/error_output_parity/compiler/fixtures/deriving_jsconverter_not_applicable_abstract_signature.resi`,
      and
      `tests/error_output_parity/compiler/fixtures/deriving_jsconverter_not_applicable_open_signature.resi`.
- `compiler/frontend/ast_exp_handle_external.ml`
  - `%debugger` payload rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_debugger_payload.res`.
  - `%raw`, `%re`, and `%%raw` non-string payload rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_expr_non_string.res`,
      `tests/error_output_parity/compiler/fixtures/raw_re_non_string.res`,
      and
      `tests/error_output_parity/compiler/fixtures/raw_structure_non_string.res`.
  - `Ast_payload.raw_as_string_exp_exn` Flow parser warning for invalid `%raw`
    expression JavaScript
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_expr_invalid_js_warning.res`.
  - `Ast_payload.raw_as_string_exp_exn` Flow parser warning for invalid
    `%%raw` program JavaScript
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_structure_invalid_js_warning.res`.
  - `Ast_payload.raw_as_string_exp_exn` Flow parser warning for invalid regex
    literals in `%raw` and `%re`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_expr_invalid_regex_warning.res`
      and
      `tests/error_output_parity/compiler/fixtures/raw_re_invalid_regex_warning.res`.
  - Additional `Ast_payload.raw_as_string_exp_exn` Flow parser warning message
    branches for `%raw` expression payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_expr_keyword_warning.res`,
      `tests/error_output_parity/compiler/fixtures/raw_expr_function_identifier_warning.res`,
      `tests/error_output_parity/compiler/fixtures/raw_expr_import_paren_warning.res`,
      and
      `tests/error_output_parity/compiler/fixtures/raw_expr_class_eof_warning.res`.
  - Additional `Ast_payload.raw_as_string_exp_exn` Flow parser warning message
    branches for `%%raw` program payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_structure_invalid_regex_warning.res`,
      `tests/error_output_parity/compiler/fixtures/raw_structure_function_identifier_warning.res`,
      `tests/error_output_parity/compiler/fixtures/raw_structure_import_eof_warning.res`,
      and
      `tests/error_output_parity/compiler/fixtures/raw_structure_return_warning.res`.
  - `%ffi` non-string and non-function-string payload rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/ffi_non_string.res`
      and
      `tests/error_output_parity/compiler/fixtures/ffi_non_function_string.res`.
  - `Ast_payload.raw_as_string_exp_exn` Flow parser warning before `%ffi`
    rejects a non-function JavaScript payload
    - Covered by
      `tests/error_output_parity/compiler/fixtures/ffi_invalid_js_warning.res`.
  - `Ast_payload.raw_as_string_exp_exn` warning-only Flow recovery for `%ffi`
    function and non-async arrow payloads, matching
    `Classify_function.classify_exp` over the recovered AST
    - Covered by
      `tests/error_output_parity/compiler/fixtures/ffi_function_identifier_warning.res`,
      `tests/error_output_parity/compiler/fixtures/ffi_function_name_paren_warning.res`,
      `tests/error_output_parity/compiler/fixtures/ffi_function_body_warning.res`,
      `tests/error_output_parity/compiler/fixtures/ffi_function_unclosed_body_warning.res`,
      `tests/error_output_parity/compiler/fixtures/ffi_arrow_expression_warning.res`,
      and
      `tests/error_output_parity/compiler/fixtures/ffi_arrow_block_warning.res`.
  - `%ffi` async arrow payloads remain rejected even when Flow emits a warning
    - Covered by
      `tests/error_output_parity/compiler/fixtures/ffi_async_arrow_warning_error.res`.
- `compiler/frontend/ppx_entry.ml`
  - `-bs-no-builtin-ppx` returns after config/JSX preprocessing and skips
    `Bs_builtin_ppx.mapper`, leaving `%raw` uninterpreted for
    `Builtin_attributes.error_of_extension`
    - Covered by
      `tests/error_output_parity/compiler/cases/no_builtin_raw_extension.res`.
- `compiler/core/cmd_ppx_apply.ml`
  - `Cmd_ast_exception.WrongMagic` when an external `-ppx` exits successfully
    but writes an output file whose leading bytes do not match the expected
    binary AST magic
    - Covered by
      `tests/error_output_parity/compiler/cases/external_ppx_wrong_magic.res`.
  - `Cmd_ast_exception.CannotRun` when an external `-ppx` exits non-zero or
    removes its output file
    - Source-reachable, but not suitable for the byte-for-byte harness as-is:
      OCaml includes `Filename.temp_file` paths in the printed command line,
      and those paths are intentionally nondeterministic across compiler runs.
- `compiler/frontend/bs_builtin_ppx.ml`
  - `await` outside an async context is rejected by the frontend mapper
    - Covered by
      `tests/error_output_parity/compiler/fixtures/await_outside_async.res`.
  - `module M = await (X: module type of X)` does not take the dynamic-import
    rewrite path in the OCaml frontend and must remain accepted
    - Covered by
      `tests/error_output_parity/compiler/fixtures/await_module_constraint_typeof_success.res`.
  - `%%private` empty structure payload rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_private_extension_empty.res`.
  - `%%private` non-structure payload rejection for `PTyp`, `PSig`, and `PPat`
    payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_private_extension_type_payload.res`,
      `tests/error_output_parity/compiler/fixtures/builtin_private_extension_signature_payload.res`,
      and
      `tests/error_output_parity/compiler/fixtures/builtin_private_extension_pattern_payload.res`.
- `compiler/frontend/typemod_hide.ml`
  - `%%private` local-extension structure item validation rejects unsupported
    items such as type declarations
    - Covered by
      `tests/error_output_parity/compiler/fixtures/private_type_in_local_extension.res`.
- `compiler/frontend/ast_exp_extension.ml`
  - `%todo` emits `Warnings.Bs_todo` for missing and string payloads
    - Covered by
      `tests/error_output_parity/compiler/fixtures/todo_warning_no_payload.res`
      and
      `tests/error_output_parity/compiler/fixtures/todo_warning_with_payload.res`.
  - `%obj` non-record payload rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/obj_extension_non_record.res`.
- `compiler/frontend/ast_util.ml`
  - `%obj` qualified-label rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/obj_extension_qualified_label.res`.
- `compiler/frontend/ast_external.ml`
  - Empty and multiple primitive string rejection
    - Source-unreachable from normal `.res`/`.resi`. Probes for
      `external x: int` and `external x: int = "a" "b"` are rejected by parser
      diagnostics before `Ast_external.handle_external_in_stru` or
      `Ast_external.handle_external_in_sig` can inspect `pval_prim`.
- `compiler/frontend/ast_exp_apply.ml`
  - `property name (...) can not contain speical character #`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/invalid_hash_property_assignment.res`.
  - `invalid #= assignment`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/invalid_hash_set_assignment.res`.
  - Legacy direct `##`, `#=`, and `->` operator shape errors
    - Checked against source-level probes. Normal `.res` source is rejected by
      parser diagnostics before these frontend branches are observable through
      the current ReScript syntax.
- `compiler/frontend/ast_tuple_pattern_flatten.ml`
  - Qualified record fields while destructuring a packed module raise
    `Not supported pattern match on modules`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/module_record_pattern_qualified.res`.
- `compiler/frontend/bs_ast_invariant.ml`
  - `Bs_unused_attribute` warning 101 for unused built-in ReScript
    attributes on values
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_unused_string_value_arg.res`
      and the signature value case
      `tests/error_output_parity/compiler/fixtures/bs_unused_string_signature_value.resi`,
      and the JSX post-transform value-prop case
      `tests/error_output_parity/compiler/fixtures/jsx_component_value_string_attr.res`.
      The full warning-name set (`@as`, `@config`, `@ignore`, `@int`,
      `@optional`, `@string`, `@unwrap`) is covered by those plus
      `tests/error_output_parity/compiler/fixtures/bs_unused_builtin_attrs_value.res`.
  - Built-in rank-0 type redefinition is rejected in structures, nested
    module structures, and signatures
    - Covered by
      `tests/error_output_parity/compiler/fixtures/builtin_type_redefinition.res`,
      `tests/error_output_parity/compiler/fixtures/builtin_type_redefinition_nested.res`,
      and
      `tests/error_output_parity/compiler/fixtures/builtin_type_redefinition_signature.resi`.
  - GADT constructor result syntax without `type rec`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/gadt_requires_type_rec.res`.
  - Numeric polymorphic variant literals outside the int32 range
    - Covered by
      `tests/error_output_parity/compiler/fixtures/polyvariant_numeric_overflow.res`.
  - `%identity` primitive arity validation
    - Covered by
      `tests/error_output_parity/compiler/fixtures/identity_wrong_type.res`
      and
      `tests/error_output_parity/compiler/fixtures/identity_wrong_type_signature.resi`,
      plus the expression-contained local module traversal case in
      `tests/error_output_parity/compiler/fixtures/identity_wrong_type_let_module.res`
      and the packed-module expression traversal case in
      `tests/error_output_parity/compiler/fixtures/identity_wrong_type_packed_module.res`.
  - Built-in constructor redefinition (`false`, `true`, `()`) is
    source-unreachable from normal ReScript. `parse_type_constructor_declaration`
    only creates ordinary constructor declarations from `Uident` tokens;
    `false`/`true` are rejected earlier as invalid constructor names, while
    `()` parses as a unit type payload rather than a constructor declaration.
- `compiler/ml/parmatch.ml`
  - `Warnings.Partial_match` for ordinary exhaustiveness
    - Covered by `tests/build_tests/super_errors/fixtures/warnings5.res`.
  - `Warnings.Fragile_match`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/parmatch_fragile_match.res`.
  - `Warnings.All_clauses_guarded`
    - Covered under `-warn-error +8` by
      `tests/error_output_parity/compiler/cases/parmatch_all_guarded.res`.
  - `Warnings.Unused_match`
    - Covered for duplicate cases and a GADT catch-all after exhaustive
      constructor coverage by
      `tests/error_output_parity/compiler/fixtures/parmatch_unused_match.res`
      and
      `tests/error_output_parity/compiler/fixtures/parmatch_gadt_unused_catchall.res`.
  - `Warnings.Unreachable_case`
    - Covered for a GADT-indexed catch-all whose remaining constructor space is
      impossible by
      `tests/error_output_parity/compiler/fixtures/parmatch_unreachable_case.res`.
  - `Warnings.Unused_pat`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/parmatch_unused_subpattern.res`.
  - `Warnings.Ambiguous_pattern`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/parmatch_ambiguous_guarded_or.res`.
- `compiler/ml/cmi_format.ml`
  - `Not_an_interface`
    - Covered by
      `tests/error_output_parity/compiler/cases/cmi_not_an_interface.cmi`.
  - `Wrong_version_interface`
    - Covered by
      `tests/error_output_parity/compiler/cases/cmi_wrong_version.cmi`.
  - `Corrupted_interface`
    - Covered by
      `tests/error_output_parity/compiler/cases/cmi_corrupted.cmi`.
- `compiler/ml/cmt_format.ml`
  - `Not_a_typedtree`
    - Covered through `-bs-gentype` with a stale `.cmti` containing only CMI
      data. OCaml writes `output.cmt`, then `GenTypeMain.process_cmt_file`
      chooses the stale `output.cmti`; `Cmt_format.read_cmt` raises
      `Cmt_format.Error(Not_a_typedtree _)`.
    - Fixture:
      `tests/error_output_parity/compiler/cases/gentype_stale_cmti.res`.
  - `Cmi_format.Error` while `GenTypeMain.read_cmt` loads the selected
    typedtree file
    - Covered through `-bs-gentype` with a stale `.cmti` whose magic is not CMI
      or CMT. The harness compares combined stdout/stderr for this case because
      OCaml emits the stale-artifact note through `Log_.item` before the fatal
      assertion.
    - Virtual fixture prepared under
      `.parity-cache/error-output/compiler/gentype_bad_magic.res`.
- `compiler/frontend/ast_external_process.ml`
  - `Invalid payload` from `name_from_payload_or_prim`
    - Covered for the shared `@val`/`@send`/`@set`/`@get`/`@new`
      payload path by
      `tests/error_output_parity/compiler/fixtures/bs_external_val_invalid_payload.res`.
  - `Ast_payload.assert_strings` for `@module` and `@scope`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_module_ident_payload.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_scope_ident_payload.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_module_tuple_non_string.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_scope_tuple_non_string.res`.
  - `@module({from, with})` import-attributes payload validation
    - Covered for missing `from`, missing `with`, non-string import
      attribute values, and non-regular import attribute keys by
      `tests/error_output_parity/compiler/fixtures/bs_external_module_import_missing_from.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_module_import_missing_with.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_module_import_non_string_value.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_module_import_qualified_key.res`.
  - `@get_index`/`@set_index` non-empty primitive-name validation
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_get_index_named_primitive.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_set_index_named_primitive.res`.
  - `@get_index`/`@set_index` arity validation
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_get_index_wrong_arity.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_set_index_wrong_arity.res`.
  - `@send` plain external argument-shape validation
    - Covered for no-argument, const first-argument, and later conflict-catch
      cases by
      `tests/error_output_parity/compiler/fixtures/bs_external_send_no_args.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_send_const_first_arg.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_send_new_conflict.res`.
  - `@set`/`@get` plain external arity and unit-argument validation
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_set_wrong_arity.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_get_wrong_arity.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_get_unit_arg.res`.
  - `@set`/`@get` conflict catches and earlier `@variadic` last-argument
    validation
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_set_get_conflict.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_set_variadic_conflict.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_get_module_conflict.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_get_variadic_conflict.res`.
  - `process_obj` argument-shape and unsupported argument-attribute validation
    - Covered for non-empty primitive names, unlabeled non-`unit`, payload
      `@string`, `@unwrap`
      labeled/optional arguments, unused optional and non-underscore type
      `@as` attributes, and the final `@obj` conflict catch by
      `tests/error_output_parity/compiler/fixtures/bs_obj_nonempty_external_name.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_unlabelled_non_unit.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_label_string_payload.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_label_unwrap.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_optional_string_payload.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_optional_unwrap.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_optional_as_payload.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_label_duplicate_as.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_get_index_conflict.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_set_index_conflict.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_obj_val_conflict.res`.
    - Checked: the later `Arg_cst _` branch that would report
      `%@as is not supported with optional yet` is not reachable from normal
      `.res` syntax. Optional `_` arguments are rejected first by
      `get_opt_arg_type`, and non-underscore optional `@as` attributes fall
      through `spec_of_ptyp` as unused attributes.
  - `@module` with payload-bearing `@new`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_module_new_payload.res`.
  - Duplicate/bare-plus-payload `@module` state is preserved until the
    non-object conflict catch
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_duplicate_module_attr.res`.
  - Bare `@module` value imports allow value-style `@val` without reporting a
    `%@val` conflict
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_module_val_as_var.res`.
  - Non-object optional argument validation in `handle_attributes`
    - Covered for underscore optional arguments, payload `@string` optionals,
      and all `@variadic` last-argument validations (optional, underscore,
      FFI-attributed, and non-array) by
      `tests/error_output_parity/compiler/fixtures/bs_optional_underscore_external.res`,
      `tests/error_output_parity/compiler/fixtures/bs_optional_string_payload.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_variadic_optional_last_arg.res`,
      `tests/error_output_parity/compiler/fixtures/bs_variadic_underscore_last_arg.res`,
      `tests/error_output_parity/compiler/fixtures/bs_variadic_attr_last_arg.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_variadic_non_array_last_arg.res`.
- `compiler/frontend/external_ffi_types.ml`
  - `valid_global_name` rejects invalid global/call/constructor names
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_invalid_global_name.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_empty_global_name.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_invalid_call_name.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_invalid_new_name.res`.
  - `check_external_module_name` rejects empty module bundles and bind names
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_empty_module_as_var.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_empty_module_as_fn.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_empty_module_as_class.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_empty_module_bind_name.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_empty_module_name.res`.
- `compiler/frontend/ast_attributes.ml`
  - `iter_process_bs_string_or_int_as` rejects json-delimited `@as` payloads
    that are not literal JavaScript expressions, after first reporting Flow
    parse warnings for malformed JavaScript
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_as_json_non_literal.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_as_json_invalid_js.res`.

## Include Mismatch Surfaces

`compiler/ml/includemod.ml` and `compiler/ml/includecore.ml` are reported
through higher-level errors such as `Typemod.Not_included`,
`Typemod.With_mismatch`, `Typedecl.Definition_mismatch`, and
`Typedecl.Extension_mismatch`.

Coverage should include representative include mismatch symptoms rather than
only the wrapper variant:

- missing values (covered by
  `tests/error_output_parity/compiler/fixtures/not_included_missing_value.res`)
- value description mismatch (covered by
  `tests/error_output_parity/compiler/fixtures/not_included_value_mismatch.res`)
- type declaration mismatch (covered by
  `tests/error_output_parity/compiler/fixtures/not_included_type_mismatch.res`)
- extension constructor mismatch (covered by
  `tests/error_output_parity/compiler/fixtures/not_included_extension_mismatch.res`)
- module mismatch (covered by
  `tests/error_output_parity/compiler/fixtures/not_included_module_mismatch.res`)
- module type mismatch (covered by
  `tests/error_output_parity/compiler/fixtures/not_included_modtype_mismatch.res`)
- module type declaration permutation mismatch (covered by
  `tests/error_output_parity/compiler/fixtures/modtype_permutation.res`)
- invalid module alias / functor-argument alias requirement (covered by
  `tests/error_output_parity/compiler/fixtures/not_included_functor_arg_module_alias.res`)
- lax module alias normalization through persistent components (covered by
  `tests/error_output_parity/compiler/cases/include_alias_lax_normalization.res`)
- strict module alias normalization through flattened runtime units has a
  success guard in
  `tests/error_output_parity/compiler/fixtures/include_alias_strict_flattened_runtime_success.res`
- unbound module path (covered by
  `tests/error_output_parity/compiler/cases/include_unbound_module_path.res`)
- unbound module type path is not reachable from normal `.res`/`.resi` source
  found so far. `compiler/ml/includemod.ml` only calls `expand_module_path`
  after `may_expand_module_path` has just succeeded against the same
  `Env.find_modtype_expansion` lookup, and normal source references to missing
  module types are rejected earlier as `Typetexp.Unbound_modtype`. Probes for
  abstract structure module-type declarations also hit parser diagnostics before
  inclusion.
