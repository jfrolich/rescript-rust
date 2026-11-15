// Unifying first-class module types follows OCaml's `unify_package`
// (compiler/ml/ctype.ml:2172-2181): two module types with different paths
// unify when each is included in the other.

module type S = {
  let x: int
}
module type T = {
  let x: int
}

let otherPath = (x: module(S)): module(T) => x

let inArray = (x: module(S), y: module(T)) => [x, y]

module type U = S

let abbreviation = (x: module(S)): module(U) => x

// The same path (agreed before).
let samePath = (x: module(S)): module(S) => x
