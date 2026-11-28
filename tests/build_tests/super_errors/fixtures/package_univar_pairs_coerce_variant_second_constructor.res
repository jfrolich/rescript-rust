module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
type a = B(int) | A(module(S))
type b = B(int) | A(module(T))
let g = (o: {"f": 'a. (a, 'a)}) => (o :> {"f": 'a. (b, 'a)})
