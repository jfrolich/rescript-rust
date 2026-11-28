module type T = {
  type t
}
module type S = {
  type t
}
let g = (o: {"f": 'a. (module(S), 'a)}) => (o :> {"f": 'a. (module(T), 'a)})
