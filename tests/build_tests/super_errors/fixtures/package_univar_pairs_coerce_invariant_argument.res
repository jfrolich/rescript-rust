module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
let g = (o: {"f": 'a. (array<module(S with type t = int)>, 'a)}) => (o :> {"f": 'a. (array<module(T with type t = int)>, 'a)})
