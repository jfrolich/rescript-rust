// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance RegExp)
@unboxed
type t =
  | A(RegExp.t)
  | B(RegExp.t)
