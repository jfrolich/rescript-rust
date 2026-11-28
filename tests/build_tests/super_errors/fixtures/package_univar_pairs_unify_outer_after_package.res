module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
let g = (o: {"f": 'a. (module(S), {"g": 'b. ('b, 'a)})}): {"f": 'a. (module(T), {"g": 'b. ('b, 'a)})} => o
