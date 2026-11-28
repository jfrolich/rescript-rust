module type T = {
  type t
  let x: t
}

module type S = {
  type t
  @deprecated("x of S")
  let x: t
}

let unifyLeft: module(S) => module(T)
let unifyRight: module(T) => module(S)
let coerce: {"f": module(S)} => {"f": module(T)}
let coerceRight: {"f": module(T)} => {"f": module(S)}
let twice: module(S) => (module(T), module(T))

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

let typeItem: module(TypeItemS) => module(TypeItemT)

module type CtorT = {
  type t = A | B
}

module type CtorS = {
  type t = | @deprecated("A of CtorS") A | B
}

let ctor: module(CtorS) => module(CtorT)

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

let moduleItem: module(ModS) => module(ModT)
let nested: module(NestedS) => module(ModT)

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

let modtypeItem: module(ModtypeS) => module(ModtypeT)

module N: J

module type WithN = ModT with module M = N

let moregen: module(T) => unit
type eqtype = module(T)
