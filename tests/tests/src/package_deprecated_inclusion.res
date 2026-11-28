// A package inclusion check prints the deprecation of an item that is
// `@deprecated` on its left side only, whatever the check returns.

module type T = {
  type t
  let x: t
}

module type S = {
  type t
  @deprecated("x of S")
  let x: t
}

// A unification asks both ways: the warning comes from `S` included in `T`.
let unifyLeft = (o: module(S)): module(T) => o
let unifyRight = (o: module(T)): module(S) => o

// A coercion asks once.
let coerce = (o: {"f": module(S)}) => (o :> {"f": module(T)})
let coerceRight = (o: {"f": module(T)}) => (o :> {"f": module(S)})

// Two uses, two checks.
let twice = (o: module(S)): (module(T), module(T)) => (o, o)

module type TypeItemT = {
  type t
  let x: t
}

module type TypeItemS = {
  @deprecated("t of TypeItemS")
  type t
  @deprecated("x of TypeItemS")
  let x: t
}

let typeItem = (o: module(TypeItemS)): module(TypeItemT) => o

module type CtorT = {
  type t = A | B
}

module type CtorS = {
  type t = | @deprecated("A of CtorS") A | B
}

let ctor = (o: module(CtorS)): module(CtorT) => o

module type I = {
  let v: int
}

module type J = {
  @deprecated("v of J")
  let v: int
}

module type ModT = {
  module M: I
}

module type ModS = {
  @deprecated("M of ModS")
  module M: I
}

module type NestedS = {
  module M: J
}

let moduleItem = (o: module(ModS)): module(ModT) => o
let nested = (o: module(NestedS)): module(ModT) => o

module type ModtypeT = {
  module type K = {
    let v: int
  }
}

module type ModtypeS = {
  @deprecated("K of ModtypeS")
  module type K = {
    let v: int
  }
}

let modtypeItem = (o: module(ModtypeS)): module(ModtypeT) => o

// `with module` checks the module against the declaration it replaces.
module N: J = {
  let v = 1
}

module type WithN = ModT with module M = N

// The interface's `moregen` and `eqtype` reach the same check.
let moregen = (_: module(S)) => ()
type eqtype = module(S)
