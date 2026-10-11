// error-output-parity: Ast_untagged_variants.check_well_formed runs after recursive type group env creation.
@unboxed
type rec t =
  | A(a)
  | B(b)
and a = promise<int>
and b = promise<string>
