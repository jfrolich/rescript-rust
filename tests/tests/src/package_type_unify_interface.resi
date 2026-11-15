module type S = {
  let x: int
}
module type T = {
  let x: int
}

let f: module(T) => module(T)

type t = module(T)
