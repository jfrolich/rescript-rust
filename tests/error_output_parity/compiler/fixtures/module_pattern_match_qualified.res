// error-output-parity: Ast_tuple_pattern_flatten rejects qualified record labels when destructuring packed modules.
module M = {
  let x = 1
}

let {M.x: value} = module(M)
