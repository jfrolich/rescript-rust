// Inside a module type declaration of the result a type declaration that
// keeps the eliminated parameter is strict, so the module type becomes
// abstract (compiler/ml/mtype.ml:139-140 and 147-158).
module F = (X: {type t}) => {
  module type U = {type u = X.t}
}
module R = F({type t})
module M: R.U = {type u = int}
