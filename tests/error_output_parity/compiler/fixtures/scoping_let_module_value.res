// error-output-parity: local let-module type escape reported through Expr_type_clash.
let value = {
  module M: {
    type t
    let x: t
  } = {
    type t = int
    let x = 1
  }

  M.x
}
