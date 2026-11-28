module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
let v: {"f": 'a. (module(S), 'a)} = Obj.magic(1)
