// An extension of an extensible type of the parameter that the argument
// does not name rejects the application (compiler/ml/ctype.ml:4523-4532).
module F = (X: {type t = ..}) => {
  type X.t += A
}
module R = F({type t = ..})
