module type T = {
  type t
  let x: t
}
module type S = {
  type t
  @deprecated("plain")
  let x: t
  let y: int
}
let g = (o: module(S)): module(T) => o
