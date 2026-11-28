module type T = {
  type t
  @deprecated("right")
  let x: t
}
module type S = {
  type t
  let x: t
}
let g = (o: {"f": 'a. (module(S), 'a)}): {"f": 'a. (module(T), 'a)} => o
