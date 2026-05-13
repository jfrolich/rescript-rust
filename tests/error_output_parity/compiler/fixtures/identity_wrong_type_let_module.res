// error-output-parity: Bs_ast_invariant %identity arity validation inside local modules.
let value = {
  module M = {
    type t
    external value: t = "%identity"
  }
  M.value
}
