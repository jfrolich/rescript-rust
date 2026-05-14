// error-output-parity: Typecore.Expr_type_clash package local type escape
module type S = {
  type t
}

let value = {
  module M = {
    type t
  }
  let packed: module(S with type t = M.t) = module({
    type t = M.t
  }: S with type t = M.t)
  packed
}
