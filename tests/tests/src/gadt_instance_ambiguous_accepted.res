// Programs where a GADT equation's type does not leave its case: both
// compilers accept them (the refused ones are the super_errors fixtures
// gadt_instance_ambiguous_*).

module ResultAnnotation = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a): int =>
    switch x {
    | Int => if true { y } else { 0 }
    }
}

module PlusOne = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => y + 1
    }
}

module TupleTwoCases = {
  type rec t<_> = Int: t<int> | Int2: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => (0, 1)
    | Int2 => (y, 2)
    }
}

module EqTwoVars = {
  type rec eq<'a, 'b> = Refl: eq<'a, 'a>
  let f = (type a b, e: eq<a, b>, x: a, y: b) =>
    switch e {
    | Refl => if true { x } else { y }
    }
}

module BranchAnnotation = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => if true { (y: int) } else { 0 }
    }
}

module PassToIntFn = {
  type rec t<_> = Int: t<int>
  let h = (n: int) => n * 2
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => h(y)
    }
}

module ExistentialNoEscape = {
  type rec t<_> = Int: t<int>
  type rec ex = Ex(t<'a>, 'a): ex
  let g = e =>
    switch e {
    | Ex(Int, v) => v + 1
    }
}

module ArrayResultAnnotation = {
  type rec t<_> = Int: t<int> | Str: t<string>
  let f = (type a, x: t<a>, y: a): array<int> =>
    switch x {
    | Int => [y, 0]
    | Str => []
    }
}

module ExistentialIgnored = {
  type rec t<_> = Int: t<int>
  type rec ex = Ex(t<'a>, 'a): ex
  let g = e =>
    switch e {
    | Ex(Int, v) => ignore(v)
    }
}

module PolyvariantOpen = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => if true { #A(y) } else { #B(0) }
    }
}

module ResultIsA = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a): a =>
    switch x {
    | Int => if true { y } else { 0 }
    }
}

module ObjectFieldLevel = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, o: {..}) =>
    switch x {
    | Int => {
        let p = {"f": 0, "g": y}
        if true { p } else { o }
      }
    }
}

module PolyvariantClosed = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, v: [< #A(int) | #B]) =>
    switch x {
    | Int =>
      switch v {
      | #A(n) => if true { #A(n) } else { #A(y) }
      | #B => #B
      }
    }
}

module Unify2ChainEscape = {
  type rec t<_> = Int: t<int>
  type u = int
  let f = (type a, x: t<a>, y: a) => {
    let r = ref([])
    switch x {
    | Int => {
        let z: u = y
        r := [z]
      }
    }
    r
  }
}

module LowerArgs = {
  type rec t<_> = Int: t<int>
  let g = (n: int, m) => n + m
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => g(y, ...)
    }
}

module LocalAbbrevRec = {
  type rec t<_> = Int: t<int> | L: t<list<'b>>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => 0
    | L => List.length(y)
    }
}

module NestedSwitchLevels = {
  type rec t<_> = Int: t<int>
  type rec s<_> = Str: s<string>
  let f = (type a b, x: t<a>, z: s<b>, y: a, w: b) =>
    switch x {
    | Int =>
      switch z {
      | Str => (y + 1, w ++ "")
      }
    }
}

module FieldObjectMethod = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => {
        let o = {"m": y}
        o["m"] + 0
      }
    }
}

module WhileRef = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) => {
    let r = ref(y)
    switch x {
    | Int => r.contents = r.contents + 1
    }
    r.contents
  }
}

module ChainEquality = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => {
        let w = 1
        ignore(y == w)
        if true { w } else { w }
      }
    }
}

module ChainAnnot = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => {
        let w = 1
        let _ = [y, w]
        w
      }
    }
}

module ChainAbbrev = {
  type rec t<_> = Int: t<int>
  type u = int
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => {
        let w: u = 1
        ignore(y == w)
        [w]
      }
    }
}

module ChainOuterParam = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, w: int) =>
    switch x {
    | Int => {
        ignore(y == w)
        w
      }
    }
}

module ObjectFields = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a, o) =>
    switch x {
    | Int => {
        ignore(o["g"] == 1)
        if true { o } else { {"f": y, "g": 0} }
      }
    }
}

module PolyvariantOpenMore = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) => {
    let r = ref(None)
    switch x {
    | Int => r := Some(#A(y))
    }
    r
  }
}

module LocalRecAbbrev = {
  type rec t<_> = Int: t<int> | Lst: t<list<int>>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => y + 1
    | Lst => List.length(y)
    }
}

module EqChain = {
  type rec eq<'a, 'b> = Refl: eq<'a, 'a>
  let f = (type a, e: eq<a, int>, y: a) =>
    switch e {
    | Refl => {
        let w = 2
        ignore(y == w)
        w
      }
    }
}

module ChainRef = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => {
        let w = ref(1)
        ignore(y == w.contents)
        w.contents
      }
    }
}

module ChainRefArray = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => {
        let w = [1]
        ignore(y == w[0]->Option.getOr(0))
        w
      }
    }
}

module ChainParamFn = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => {
        let g = n => n
        ignore(g(y) == 1)
        g
      }
    }
}

module ChainRefReverse = {
  type rec t<_> = Int: t<int>
  let f = (type a, x: t<a>, y: a) =>
    switch x {
    | Int => {
        let w = ref(1)
        ignore(w.contents == y)
        w
      }
    }
}
