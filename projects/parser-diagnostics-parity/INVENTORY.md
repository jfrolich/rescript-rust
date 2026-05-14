# OCaml Parser Diagnostics Inventory

Inventory date: **February 10, 2026**

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

### 5.1 Module Inclusion Type Mismatch Diagnostics

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
