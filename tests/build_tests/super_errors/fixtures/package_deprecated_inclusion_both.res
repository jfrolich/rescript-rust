module type T = {
  type t
  @deprecated("r")
  let x: t
}
module type S = {
  type t
  @deprecated("l")
  let x: t
}
let g = (o: {"f": 'a. (module(S), 'a)}): {"f": 'a. (module(T), 'a)} => o
