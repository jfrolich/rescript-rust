// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(DuplicateLiteral string)
type t =
  | @as("x") A(int)
  | @as("x") B(int)
