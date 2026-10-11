// error-output-parity: Bs_ast_invariant %identity arity validation inside packed modules.
module type S = {}

let value = module({
  external value: int = "%identity"
}: S)
