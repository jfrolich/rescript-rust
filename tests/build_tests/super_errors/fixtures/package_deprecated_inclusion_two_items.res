module type T = {
  type t
  let x: t
  let y: t
}
module type S = {
  type t
  @deprecated("dx")
  let x: t
  @deprecated("dy")
  let y: t
}
let g = (o: {"f": 'a. (module(S), 'a)}): {"f": 'a. (module(T), 'a)} => o
