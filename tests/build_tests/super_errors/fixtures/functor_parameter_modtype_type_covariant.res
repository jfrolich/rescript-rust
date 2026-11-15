// In the result itself a type declaration that keeps the eliminated
// parameter becomes abstract, so two of them are different types.
module F = (X: {type t}) => {
  type u = X.t
  type w = X.t
}
module R = F({type t})
let f = (x: R.u): R.w => x
