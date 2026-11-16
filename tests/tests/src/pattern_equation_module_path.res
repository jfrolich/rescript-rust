// An equation of a constructor pattern refines an abstract type reached
// through a module path, as OCaml's `is_instantiable` allows
// (compiler/ml/ctype.ml:1874-1881).
type rec eq<_, _> = Refl: eq<'a, 'a>
type rec t<_> = I: t<int> | S: t<string>
type rec only<_> = Only: only<int>

module Param = (X: {
  type t
}) => {
  let annotated = (Only: only<X.t>, v: X.t): int => v
  let toInt = (w: eq<X.t, int>, v: X.t): int =>
    switch w {
    | Refl => v
    }
  let ofString = (w: eq<X.t, string>, s: string): X.t =>
    switch w {
    | Refl => s
    }
  let both = (x: t<X.t>, y: X.t) =>
    switch x {
    | I => y + 1
    | S => String.length(y)
    }
}

module Mk = () => {
  type t
}
module Result = Mk()
let ofResult = (w: eq<Result.t, int>, v: Result.t): int =>
  switch w {
  | Refl => v
  }

module Sealed: {
  type t
} = {
  type t = int
}
let ofSealed = (w: eq<Sealed.t, int>, v: Sealed.t): int =>
  switch w {
  | Refl => v
  }

module rec Recursive: {
  type t
  let f: (eq<Recursive.t, int>, Recursive.t) => int
} = {
  type t = int
  let f = (w: eq<Recursive.t, int>, v: Recursive.t): int =>
    switch w {
    | Refl => v
    }
}
let ofRecursive = (w: eq<Recursive.t, int>, v: Recursive.t): int =>
  switch w {
  | Refl => v
  }

module Deep = (P: {
  module Q: {
    type t
  }
}) => {
  let f = (w: eq<P.Q.t, int>, v: P.Q.t): int =>
    switch w {
    | Refl => v
    }
}

let ofDate = (w: eq<Date.t, int>, v: Date.t): int =>
  switch w {
  | Refl => v
  }

module Two = (
  X: {
    type t
  },
  Y: {
    type u
  },
) => {
  let f = (w: eq<X.t, Y.u>, v: X.t): Y.u =>
    switch w {
    | Refl => v
    }
}

module Local = (X: {
  type t
}) => {
  let f = (type a, w: eq<X.t, a>, v: X.t): a =>
    switch w {
    | Refl => v
    }
}

let () = {
  module P = Param({
    type t = int
  })
  Console.log(P.toInt(Refl, 1))
  Console.log(ofSealed(Obj.magic(Refl), Obj.magic(2)))
}
