// In the parameter of a functor in the result, a type declaration whose
// manifest keeps the eliminated parameter cannot become abstract
// (compiler/ml/mtype.ml:139-140, compiler/ml/ctype.ml:4485-4497).
module F = (X: {type t}) => (Y: {type u = X.t}) => {
  let v = 1
}
module R = F({type t})
