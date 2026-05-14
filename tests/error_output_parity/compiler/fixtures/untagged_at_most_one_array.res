// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Array)
@unboxed
type t =
  | A(array<int>)
  | B((int, int))
