// Packages inside polymorphic types that both compilers accept: the
// universal variables of the body are all met before the inclusion check of
// the two packages, the variable belongs to a body the check is not in, the
// module types are the same, or the check compares no value, type or
// extension constructor.
module type T = {
  type t
  let x: t
}
module type S = {
  type t
  let x: t
}
module type TSub = {
  module M: {}
}
module type SSub = {
  module M: {}
}
module type TMty = {
  module type X
}
module type SMty = {
  module type X
}
module type TFun = {
  module F: (X: {}) => {}
}
module type SFun = {
  module F: (X: {}) => {}
}

let arrowParamBefore = (o: {"f": 'a. ('a, module(S with type t = int)) => unit}) =>
  (o :> {"f": 'a. ('a, module(T with type t = int)) => unit})
let nestedTupleBefore = (o: {"f": 'a. ('a, (int, module(S)))}): {"f": 'a. ('a, (int, module(T)))} =>
  o
let variantBefore = (o: {"f": 'a. ('a, option<module(S)>)}): {"f": 'a. ('a, option<module(T)>)} =>
  o
let objectBefore = (o: {"f": 'a. ('a, {"m": module(S)})}): {"f": 'a. ('a, {"m": module(T)})} => o
let varPackageVar = (o: {"f": 'a. ('a, module(S), 'a)}): {"f": 'a. ('a, module(T), 'a)} => o
let innerBodyThenOuter = (o: {"f": 'a. ({"g": 'b. ('b, module(S))}, 'a)}): {
  "f": 'a. ({"g": 'b. ('b, module(T))}, 'a),
} => o
let innerBodyAfterPackage = (o: {"f": 'a. (module(S), {"g": 'b. ('b, 'b)})}): {
  "f": 'a. (module(T), {"g": 'b. ('b, 'b)}),
} => o
let sameModuleType = (o: {"f": 'a. (module(S), 'a)}) => (o :> {"f": 'a. (module(S), 'a)})
let constraintOnUnivar = (o: {"f": 'a. module(S with type t = 'a)}): {
  "f": 'a. module(T with type t = 'a),
} => o
let emptySubmodule = (o: {"f": 'a. (module(SSub), 'a)}): {"f": 'a. (module(TSub), 'a)} => o
let moduleTypeItem = (o: {"f": 'a. (module(SMty), 'a)}): {"f": 'a. (module(TMty), 'a)} => o
let functorItem = (o: {"f": 'a. (module(SFun), 'a)}): {"f": 'a. (module(TFun), 'a)} => o
