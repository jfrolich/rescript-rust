// error-output-parity: Typecore.Expr_type_clash let-module escape
let test = {
  module M = {
    type t
    external value: t = "value"
  }

  M.value
}
