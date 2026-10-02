// error-output-parity: Bs_ast_invariant nonrecursive GADT inside a submodule
module M = {
  type t = | A: t
}
