module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
type a = A(module(S))
type b = A(module(T))
let g = (o: {"f": 'a. (a, 'a)}) => (o :> {"f": 'a. (b, 'a)})
