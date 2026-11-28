module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
module type TE = {}
module type SE = {}

let varFirst: {"f": 'a. ('a, module(T))}
let emptyModuleTypes: {"f": 'a. (module(TE), 'a)}
type varFirstField = {f: 'a. ('a, module(T))}
type innerBody = {"f": 'a. ({"g": 'b. ('b, module(T))}, 'a)}
