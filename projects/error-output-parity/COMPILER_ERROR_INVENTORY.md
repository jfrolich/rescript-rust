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
- `Constructor_arity_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/constructor_arity_mismatch.res`.
- `Label_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/label_mismatch.res`.
- `Pattern_type_clash`: covered by
  `tests/error_output_parity/compiler/fixtures/pattern_type_clash.res`
  and the local GADT constraint expansion subcase in
  `tests/error_output_parity/compiler/fixtures/recursive_local_constraint.res`.
- `Or_pattern_type_clash`: covered by
  `tests/error_output_parity/compiler/fixtures/or_pattern_type_clash.res`.
- `Expr_type_clash`: covered by
  `tests/error_output_parity/compiler/fixtures/expr_type_clash.res`
  and the function label mismatch subcase in
  `tests/error_output_parity/compiler/fixtures/function_label_mismatch.res`,
  plus the local module escape note subcase in
  `tests/error_output_parity/compiler/fixtures/let_module_escape_type_clash.res`
  and the nested function return escape subcase in
  `tests/error_output_parity/compiler/fixtures/let_module_escape_function_return.res`,
  and the package local type escape/coercion subcase in
  `tests/error_output_parity/compiler/fixtures/package_local_type_escape.res`.
- `Multiply_bound_variable`: covered by
  `tests/error_output_parity/compiler/fixtures/multiply_bound_variable.res`.
- `Orpat_vars`: covered by
  `tests/error_output_parity/compiler/fixtures/orpat_vars.res`.
- `Label_multiply_defined`: covered by
  `tests/error_output_parity/compiler/fixtures/label_multiply_defined.res`.
- `Labels_missing`: covered by
  `tests/error_output_parity/compiler/fixtures/labels_missing.res`.
- `Label_not_mutable`: covered by
  `tests/error_output_parity/compiler/fixtures/label_not_mutable.res`.
- `Wrong_name`: covered by
  `tests/error_output_parity/compiler/fixtures/wrong_name.res`.
- `Name_type_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/name_type_mismatch.res`.
- `Undefined_method`: covered by
  `tests/error_output_parity/compiler/fixtures/undefined_method.res`.
- `Private_type`: covered by
  `tests/error_output_parity/compiler/fixtures/private_type.res`.
- `Private_label`: covered by
  `tests/error_output_parity/compiler/fixtures/private_label.res`.
- `Apply_non_function`: covered by
  `tests/error_output_parity/compiler/fixtures/apply_non_function.res`.
- `Apply_wrong_label`: covered by
  `tests/error_output_parity/compiler/fixtures/apply_wrong_label.res`.
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
  `tests/error_output_parity/compiler/fixtures/too_many_arguments.res`.
- `Abstract_wrong_label`: covered by
  `tests/error_output_parity/compiler/fixtures/abstract_wrong_label.res`.
- `Uncurried_arity_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/unlabelled_arity_mismatch.res`.
- `Field_not_optional`: covered for pattern and expression raise sites by
  `tests/error_output_parity/compiler/fixtures/field_not_optional_pattern.res`
  and
  `tests/error_output_parity/compiler/fixtures/field_not_optional_inline_record.res`.
- `Illegal_letrec_pat`: covered by
  `tests/error_output_parity/compiler/fixtures/illegal_letrec_pattern.res`.
- `Modules_not_allowed`: covered by
  `tests/error_output_parity/compiler/fixtures/modules_not_allowed_toplevel_unpack.res`.
- `Invalid_for_loop_index`: covered by
  `tests/error_output_parity/compiler/fixtures/invalid_for_loop_index.res`.
- `Invalid_for_of_pattern`: covered by
  `tests/error_output_parity/compiler/fixtures/invalid_for_of_pattern.res`.
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
- `Not_a_variant_type`: covered by
  `tests/error_output_parity/compiler/fixtures/not_a_variant_type_spread.res`.
- `Not_subtype`: covered by
  `tests/error_output_parity/compiler/fixtures/not_subtype_variant_spread.res`.
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

## Typetexp Coverage Notes

- `Unbound_module`: covered for the generated JSX `ReactDOM` lookup by
  `tests/error_output_parity/compiler/fixtures/jsx_generated_unbound_reactdom.res`
  and for direct module access by
  `tests/error_output_parity/compiler/fixtures/unbound_module.res`, plus the
  module-type alias lookup path in
  `tests/error_output_parity/compiler/fixtures/module_type_alias_unbound_module.res`
  and the `with module` right-hand side lookup paths in
  `tests/error_output_parity/compiler/fixtures/with_module_equation_unbound_module.res`
  and
  `tests/error_output_parity/compiler/fixtures/with_module_unbound_module.res`.
- `Unbound_value`: covered by
  `tests/error_output_parity/compiler/fixtures/unbound_value.res`.
- `Unbound_constructor`: covered by
  `tests/error_output_parity/compiler/fixtures/unbound_constructor.res`.
- `Unbound_type_constructor`: covered by
  `tests/error_output_parity/compiler/fixtures/unbound_type_constructor.res`.
- `Unbound_type_constructor_2`: covered for a recursive polyvariant
  inheritance before the type is fully defined by
  `tests/error_output_parity/compiler/fixtures/unbound_type_constructor_incomplete.res`.
- `Unbound_type_variable`: covered through a type declaration manifest by
  `tests/error_output_parity/compiler/fixtures/unbound_type_variable.res`
  and
  `tests/error_output_parity/compiler/fixtures/unbound_type_variable_wildcard.res`.
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
- `Cannot_quantify`: covered for Ptyp_poly alias reuse by
  `tests/error_output_parity/compiler/fixtures/cannot_quantify_alias.res`.
- `Multiple_constraints_on_type`: covered for package type constraints by
  `tests/error_output_parity/compiler/fixtures/multiple_constraints_on_package_type.res`.
- `Present_has_conjunction`: covered by
  `tests/error_output_parity/compiler/fixtures/present_variant_has_conjunction.res`.
- `Present_has_no_type`: covered by
  `tests/error_output_parity/compiler/fixtures/present_variant_has_no_type.res`.
- `Constructor_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/polyvariant_constructor_mismatch.res`.
- `Not_a_variant`: covered by
  `tests/error_output_parity/compiler/fixtures/typetexp_not_a_variant.res`.
- `Variant_tags`: covered by a polymorphic variant hash collision in
  `tests/error_output_parity/compiler/fixtures/variant_tags_collision.res`.
- `Opened_object`: covered by
  `tests/error_output_parity/compiler/fixtures/typetexp_opened_object.res`.
- `Not_an_object`: covered by
  `tests/error_output_parity/compiler/fixtures/typetexp_not_an_object.res`.
- `Method_mismatch`: covered by
  `tests/error_output_parity/compiler/fixtures/typetexp_method_mismatch.res`.
- `Unbound_label`: covered for an untyped record literal with no label in
  scope by `tests/error_output_parity/compiler/fixtures/unbound_label.res`.
- `Unbound_modtype`: covered by
  `tests/error_output_parity/compiler/fixtures/unbound_modtype.res` and the
  signature-item lookup path in
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
    `tests/error_output_parity/compiler/fixtures/variant_tags_collision.res`.
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
  - Covered by
    `tests/error_output_parity/compiler/fixtures/duplicate_label.res`.
- `Object_spread_with_record_field`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/object_spread_with_record_field.res`.
- `Recursive_abbrev`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/recursive_abbrev.res`.
- `Cycle_in_def`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/cycle_in_def.res`.
- `Definition_mismatch`
  - Covered for constructor-name and constructor-payload mismatches in an
    equation plus variant representation by
    `tests/error_output_parity/compiler/fixtures/definition_mismatch.res` and
    `tests/error_output_parity/compiler/fixtures/definition_mismatch_payload.res`.
- `Constraint_failed`
  - Covered for GADT constructor return-type validation by
    `tests/error_output_parity/compiler/fixtures/constraint_failed_constructor_return.res`.
- `Inconsistent_constraint`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/inconsistent_type_constraint.res`.
- `Type_clash`
  - Covered for recursive manifest stub update failure by
    `tests/error_output_parity/compiler/fixtures/type_clash_recursive_manifest.res`.
- `Parameters_differ`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/parameters_differ.res`.
- `Null_arity_external`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/null_arity_external.res`.
- `Unbound_type_var`
  - Covered for variant constructor payloads by
    `tests/error_output_parity/compiler/fixtures/unbound_type_var_decl.res`.
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
  - Covered for direct annotated parameter variance mismatch by
    `tests/error_output_parity/compiler/fixtures/bad_variance.res`.
- `Unavailable_type_constructor`
  - Not reachable from normal `.res`/`.resi` source found so far. The OCaml
    raise sites are second-pass checks over already translated `Tconstr` nodes
    in `check_constraints_rec` and `check_coherence`; missing source-level type
    constructors are rejected earlier by type expression translation, while
    recursive placeholders are all installed in the final declaration env before
    these checks run.
- `Bad_fixed_type`
  - Covered for fixed polymorphic variant rows without a row variable by
    `tests/error_output_parity/compiler/fixtures/bad_fixed_type_no_row.res`.
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
    `tests/error_output_parity/compiler/fixtures/not_included_value_mismatch.res`.
- `Cannot_eliminate_dependency`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/cannot_eliminate_dependency.res`.
- `Signature_expected`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/signature_expected_package_constraint.res`.
- `Structure_expected`
  - Covered by
    `tests/error_output_parity/compiler/fixtures/structure_expected_open_functor.res`.
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
    `tests/error_output_parity/compiler/fixtures/non_generalizable_module.res`.
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
- `compiler/ml/rec_check.ml`
  - `Illegal_letrec_expr`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/illegal_letrec_expr.res`.
- `compiler/ml/syntaxerr.ml`
  - `Variable_in_scope`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/variable_in_scope.res`.
- `compiler/ml/translcore.ml`
  - `Unknown_builtin_primitive`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/unknown_builtin_primitive.res`.
- `compiler/ml/translmod.ml`
  - `Fragile_pattern_in_toplevel`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/fragile_pattern_in_toplevel.res`.
- `compiler/ml/transl_recmodule.ml`
  - `Circular_dependency`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/circular_recursive_module.res`.
- `compiler/ml/ast_payload.ml`
  - `%re` JavaScript regex literal validation
    - Covered by
      `tests/error_output_parity/compiler/fixtures/raw_re_non_regex.res`.
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
  - `%ffi` non-string and non-function-string payload rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/ffi_non_string.res`
      and
      `tests/error_output_parity/compiler/fixtures/ffi_non_function_string.res`.
- `compiler/frontend/ast_exp_extension.ml`
  - `%obj` non-record payload rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/obj_extension_non_record.res`.
- `compiler/frontend/ast_util.ml`
  - `%obj` qualified-label rejection
    - Covered by
      `tests/error_output_parity/compiler/fixtures/obj_extension_qualified_label.res`.
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
- `compiler/frontend/bs_ast_invariant.ml`
  - `%identity` primitive arity validation
    - Covered by
      `tests/error_output_parity/compiler/fixtures/identity_wrong_type.res`
      and
      `tests/error_output_parity/compiler/fixtures/identity_wrong_type_signature.resi`.
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
- `compiler/frontend/ast_external_process.ml`
  - `Invalid payload` from `name_from_payload_or_prim`
    - Covered for the shared `@val`/`@send`/`@set`/`@get`/`@new`
      payload path by
      `tests/error_output_parity/compiler/fixtures/bs_external_val_invalid_payload.res`.
  - `Ast_payload.assert_strings` for `@module` and `@scope`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_external_module_ident_payload.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_scope_ident_payload.res`.
  - `@module({from, with})` import-attributes payload validation
    - Covered for missing `from`, missing `with`, and non-string import
      attribute values by
      `tests/error_output_parity/compiler/fixtures/bs_external_module_import_missing_from.res`,
      `tests/error_output_parity/compiler/fixtures/bs_external_module_import_missing_with.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_module_import_non_string_value.res`.
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
      and
      `tests/error_output_parity/compiler/fixtures/bs_external_get_variadic_conflict.res`.
  - `process_obj` argument-shape and unsupported argument-attribute validation
    - Covered for unlabeled non-`unit`, payload `@string`, `@unwrap`
      labeled/optional arguments, and the final `@obj` conflict catch by
      `tests/error_output_parity/compiler/fixtures/bs_obj_unlabelled_non_unit.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_label_string_payload.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_label_unwrap.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_optional_string_payload.res`,
      `tests/error_output_parity/compiler/fixtures/bs_obj_optional_unwrap.res`,
      and
      `tests/error_output_parity/compiler/fixtures/bs_obj_val_conflict.res`.
  - `@module` with payload-bearing `@new`
    - Covered by
      `tests/error_output_parity/compiler/fixtures/bs_module_new_payload.res`.
  - Non-object optional argument validation in `handle_attributes`
    - Covered for payload `@string` optionals and `@variadic` optional last
      argument ordering by
      `tests/error_output_parity/compiler/fixtures/bs_optional_string_payload.res`
      and
      `tests/error_output_parity/compiler/fixtures/bs_variadic_optional_last_arg.res`.

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
- invalid module alias / functor-argument alias requirement (covered by
  `tests/error_output_parity/compiler/fixtures/not_included_functor_arg_module_alias.res`)
- lax module alias normalization through persistent components (covered by
  `tests/error_output_parity/compiler/cases/include_alias_lax_normalization.res`)
- unbound module path (covered by
  `tests/error_output_parity/compiler/cases/include_unbound_module_path.res`)
- unbound module type path is not reachable from normal `.res`/`.resi` source
  found so far. `compiler/ml/includemod.ml` only calls `expand_module_path`
  after `may_expand_module_path` has just succeeded against the same
  `Env.find_modtype_expansion` lookup, and normal source references to missing
  module types are rejected earlier as `Typetexp.Unbound_modtype`. Probes for
  abstract structure module-type declarations also hit parser diagnostics before
  inclusion.
