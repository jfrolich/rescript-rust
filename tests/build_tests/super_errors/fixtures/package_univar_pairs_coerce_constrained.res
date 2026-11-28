module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
let g = (o: {"f": 'a. (module(S with type t = int), 'a)}) => (o :> {"f": 'a. (module(T with type t = int), 'a)})
