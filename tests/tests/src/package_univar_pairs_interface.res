// Values, record fields and manifests with packages inside polymorphic
// types, included in an interface that names another module type with the
// same items; both compilers accept them.
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

let varFirst: {"f": 'a. ('a, module(S))} = Obj.magic(1)
let emptyModuleTypes: {"f": 'a. (module(SE), 'a)} = Obj.magic(1)
type varFirstField = {f: 'a. ('a, module(S))}
type innerBody = {"f": 'a. ({"g": 'b. ('b, module(S))}, 'a)}
