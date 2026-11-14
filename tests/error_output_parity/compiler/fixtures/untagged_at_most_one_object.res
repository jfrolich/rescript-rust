// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneObject)
@unboxed
type t =
  | A({x: int})
  | B({x: int})
