open Mocha
open Test_utils

// `with type` on a parameterized type.
module type Container = {
  type t<'a>
  let one: t<int>
}
module ListContainer: Container with type t<'a> = list<'a> = {
  type t<'a> = list<'a>
  let one = list{1}
}
let listOne: list<int> = ListContainer.one

// `with type` keeps the constrained declaration's variant constructors.
module type Shape = {
  type t = Circle | Square
  type u
  let name: u => t
}
module ShapeImpl = {
  type t = Circle | Square
  type u = t
  let name = x => x
}
module Shape: Shape with type t = ShapeImpl.t and type u = ShapeImpl.t = ShapeImpl
let square = Shape.name(ShapeImpl.Square)

// `with type ... = private` on an open polymorphic variant.
module type Tagged = {
  type t
  let v: t
}
module Tag: Tagged with type t = private [> #A | #B] = {
  type t = [#A | #B | #C]
  let v = #A
}
let tag = (Tag.v :> [> #A | #B])

// A destructive substitution by a type function.
module type Indexed = {
  type t<'a>
  type u = t<int>
  let v: u
}
module Arr: Indexed with type t<'a> := array<'a> = {
  type u = array<int>
  let v = [1]
}
let arr: array<int> = Arr.v

// Not an alias of a constructor applied to the parameters: a
// `Type_function` substitution.
module Pairs: Indexed with type t<'a> := ('a, int) = {
  type u = (int, int)
  let v = (1, 2)
}
let pairs: (int, int) = Pairs.v

// A nested type constraint and a nested destructive type substitution.
module type Nested = {
  module A: {
    type t
  }
  let w: A.t
}
module NestedEq: Nested with type A.t = int = {
  module A = {
    type t = int
  }
  let w = 2
}
module NestedSubst: Nested with type A.t := string = {
  module A = {}
  let w = "s"
}
let nestedEq: int = NestedEq.w
let nestedSubst: string = NestedSubst.w

module type T = {
  type t
}
module X = {
  type t = int
}

// A nested destructive module substitution: references to `A.O` outside
// `A` become `X` too.
module type HasNested = {
  module A: {
    module O: T
    let v: O.t
  }
  let w: A.O.t
  module B: {
    let u: A.O.t
  }
}
module Removed: HasNested with module A.O := X = {
  module A = {
    let v = 1
  }
  let w = 2
  module B = {
    let u = 3
  }
}
let removedSum: int = Removed.w + Removed.A.v + Removed.B.u

// A nested destructive type function substitution.
module type HasParam = {
  module A: {
    type t<'a>
    let v: t<int>
  }
  let w: A.t<string>
}
module Param: HasParam with type A.t<'a> := array<'a> = {
  module A = {
    let v = [1]
  }
  let w = ["s"]
}
let paramW: array<string> = Param.w
let paramV: array<int> = Param.A.v

// A package type whose constraint goes through `merge_constraint`.
module type Valued = {
  type t
  let x: t
}
let unpackValue = (m: module(Valued with type t = int)) => {
  module M = unpack(m)
  M.x
}
module Seven = {
  type t = int
  let x = 7
}

describe(__MODULE__, () => {
  test("with type", () => {
    eq(__LOC__, list{1}, listOne)
    eq(__LOC__, ShapeImpl.Square, square)
    eq(__LOC__, #A, tag)
    eq(__LOC__, [1], arr)
    eq(__LOC__, (1, 2), pairs)
    eq(__LOC__, 2, nestedEq)
    eq(__LOC__, "s", nestedSubst)
  })
  test("with module", () => {
    eq(__LOC__, 6, removedSum)
    eq(__LOC__, ["s"], paramW)
    eq(__LOC__, [1], paramV)
  })
  test("package type", () => {
    eq(__LOC__, 7, unpackValue(module(Seven)))
  })
})
