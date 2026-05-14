// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Blob)
@unboxed
type t =
  | A(Js.Blob.t)
  | B(Js.Blob.t)
