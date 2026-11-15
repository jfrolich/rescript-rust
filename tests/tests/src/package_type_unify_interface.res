module type S = {
  let x: int
}
module type T = {
  let x: int
}

// `moregen` on a value against its interface.
let f = (x: module(S)) => x

// `Ctype.equal` on a type manifest against its interface.
type t = module(S)
