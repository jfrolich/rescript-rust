// error-output-parity: Signature declarations also run Ast_untagged_variants.check_well_formed after env creation.
@unboxed
type rec t =
  | A(a)
  | B(b)
and a = promise<int>
and b = promise<string>
