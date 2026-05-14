// error-output-parity: Typecore.Pattern_type_clash local let-module parameter escape
let f = {
  module M = {
    type t
  }
  (x: M.t) => x
}
