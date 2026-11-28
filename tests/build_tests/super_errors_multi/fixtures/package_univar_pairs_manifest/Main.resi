module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
type u = {"f": 'a. (module(T), 'a)}
