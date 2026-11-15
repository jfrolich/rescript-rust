// An extension constructor of the result whose argument keeps the
// eliminated parameter rejects the application
// (compiler/ml/ctype.ml:4539-4541).
module F = (X: {type t}) => {
  exception E({v: X.t})
}
module R = F({type t})
