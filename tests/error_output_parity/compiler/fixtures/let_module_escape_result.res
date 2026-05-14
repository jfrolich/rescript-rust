// error-output-parity: Typecore.Scoping_let_module local module result escape
let x = {
  module M: {
    type t
    let v: t
  } = {
    type t = int
    let v = 1
  }
  M.v
}
