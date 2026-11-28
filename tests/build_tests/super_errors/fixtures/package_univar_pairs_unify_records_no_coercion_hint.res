module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
type r1 = {f: 'a. (module(S), 'a)}
type r2 = {f: 'a. (module(T), 'a)}
let g = (o: r1): r2 => o
