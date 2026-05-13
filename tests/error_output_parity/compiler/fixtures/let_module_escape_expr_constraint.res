// error-output-parity: Typecore.Expr_type_clash local let-module constrained expression escape
external magic: 'a => 'b = "%identity"

let f: 'a => 'a = _x => {
  module M = {
    type t
  }
  (magic(0): M.t)
}
