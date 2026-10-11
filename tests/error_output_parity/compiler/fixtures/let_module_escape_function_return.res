// error-output-parity: Typecore.Expr_type_clash let-module function return escape
let test = {
  module M = {
    type t
    external make: unit => t = "make"
  }

  () => M.make()
}
