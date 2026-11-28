module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
let g = (o: {"f": 'a. (module(S), module(S), 'a)}): {"f": 'a. (module(T), module(T), 'a)} => o
