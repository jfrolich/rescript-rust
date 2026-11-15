// The result's `module type U = X.T` cannot be made independent of the
// parameter when the argument's `T` is abstract, so it becomes abstract
// (compiler/ml/mtype.ml:147-158) and a structure cannot be constrained to it.
module type S = {let x: int}
module A = {module type T = S}
module F = (X: {module type T}) => {
  module type U = X.T
}
module type P = {module type T}
let m = module(A: P)
module R = F(unpack(m))
module M: R.U = {let x = 1}
