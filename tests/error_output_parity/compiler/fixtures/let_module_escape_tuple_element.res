// error-output-parity: Typecore.Expr_type_clash local let-module tuple element escape
let x = ({
  module M = {
    type t
    external value: t = "value"
  }
  M.value
}, 1)
