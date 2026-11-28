module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
let g = (o: {"f": 'a. (module(S), 'a) => unit}): {"f": 'a. (module(T), 'a) => unit} => o
