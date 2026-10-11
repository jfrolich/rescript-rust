// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance File)
@unboxed
type t =
  | A(Js.File.t)
  | B(Js.File.t)
