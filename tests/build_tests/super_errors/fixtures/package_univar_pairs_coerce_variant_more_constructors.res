module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
type a = A(module(S)) | B(int)
type b = A(module(T)) | B(int) | C
let g = (o: {"f": 'a. (a, 'a)}) => (o :> {"f": 'a. (b, 'a)})
