// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Date)
@unboxed
type t =
  | A(Date.t)
  | B(Date.t)
