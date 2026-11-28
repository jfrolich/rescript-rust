// Packages inside polymorphic types that both compilers accept: the
// universal variable comes before the package, the type is not polymorphic,
// the variable is outside the body, or the module types have no items.
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

let varFirst = (o: {"f": 'a. ('a, module(S with type t = int))}) =>
  (o :> {"f": 'a. ('a, module(T with type t = int))})
let pkgOnly = (o: {"f": (module(S with type t = int), int)}) =>
  (o :> {"f": (module(T with type t = int), int)})
let arrowRes = (o: {"f": 'a. 'a => module(S with type t = int)}) =>
  (o :> {"f": 'a. 'a => module(T with type t = int)})
let emptyFirst = (o: {"f": 'a. (module(SE), 'a)}) => (o :> {"f": 'a. (module(TE), 'a)})
let uVarFirst = (o: {"f": 'a. ('a, module(S))}): {"f": 'a. ('a, module(T))} => o
let uPkgOnly = (o: {"f": (module(S), int)}): {"f": (module(T), int)} => o
let uEmptyFirst = (o: {"f": 'a. (module(SE), 'a)}): {"f": 'a. (module(TE), 'a)} => o
