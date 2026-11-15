// In the parameter of a functor in the result a module type declaration of
// the parameter cannot become abstract (compiler/ml/mtype.ml:153-158).
module type S = {let x: int}
module A = {module type T = S}
module F = (X: {module type T}) => (Y: {module type U = X.T}) => {
  let v = 1
}
module type P = {module type T}
let m = module(A: P)
module R = F(unpack(m))
