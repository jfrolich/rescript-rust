// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(OnlyOneUnknown)
@unboxed
type t =
  | A(list<int>)
  | B(float)
