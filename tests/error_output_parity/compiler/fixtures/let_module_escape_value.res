// error-output-parity: Typecore.Expr_type_clash for an unannotated let-module result escape.
let value = {
  module M = {
    type t
    external make: int => t = "%identity"
  }
  M.make(0)
}
