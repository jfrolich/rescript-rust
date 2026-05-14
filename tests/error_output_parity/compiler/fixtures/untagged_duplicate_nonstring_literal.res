// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(DuplicateLiteral non-string)
type t =
  | @as(3) A(int)
  | @as(3) B(int)
