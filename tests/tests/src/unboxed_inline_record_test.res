open Mocha
open Test_utils

// A single-constructor @unboxed variant whose inline record has more than one
// field is not unboxed: its value is the record object.
@unboxed type t = Many({a: string, b: int})

let make = (a, b) => Many({a, b})
let getA = (Many(r)) => r.a
let getB = (Many({b})) => b
let bump = (Many(r)) => Many({...r, b: r.b + 1})
let literal = Many({a: "lit", b: 1})
let classify = x =>
  switch x {
  | Many({a: "lit", b}) => b
  | Many({b: 2}) => 20
  | Many(_) => 0
  }

// One field: the value is that field.
@unboxed type one = One({a: string})

let makeOne = a => One({a: a})
let getOne = (One({a})) => a

// Optional fields.
@unboxed type withOptional = WithOptional({a?: int, b: string})

let makeWithOptional = (~a=?, b) => WithOptional({?a, b})
let optionalA = x =>
  switch x {
  | WithOptional({a: ?Some(a)}) => a
  | WithOptional({a: ?None}) => -1
  }

@unboxed type oneOptional = OneOptional({a?: int})

let makeOneOptional = a => OneOptional({?a})
let getOneOptional = (OneOptional(r)) => r.a

// Mutable fields.
@unboxed type mut = Mut({mutable count: int, label: string})

let makeMut = label => Mut({count: 0, label})
let incr = (Mut(r)) => {
  r.count = r.count + 1
  r.count
}

// Nested and polymorphic uses.
@unboxed type outer = Outer({inner: t, c: int})
@unboxed type single = Single({s: t})
@unboxed type poly<'a> = Poly({value: 'a, n: int})
@unboxed type rec chain = Chain({name: string, next: option<chain>})

let makeOuter = () => Outer({inner: Many({a: "in", b: 2}), c: 3})
let innerA = (Outer({inner: Many({a})})) => a
let singleB = (Single({s: Many({b})})) => b
let makePoly = value => Poly({value, n: 1})
let polyValue = (Poly(r)) => r.value
let optionB = (x: option<t>) =>
  switch x {
  | Some(Many({b})) => b
  | None => 0
  }
let rec chainLength = (Chain({next})) =>
  switch next {
  | None => 1
  | Some(rest) => 1 + chainLength(rest)
  }

describe(__MODULE__, () => {
  test("two-field inline record is the record object", () => {
    let x = make("x", 1)
    eq(__LOC__, Obj.magic(x), {"a": "x", "b": 1})
    eq(__LOC__, getA(x), "x")
    eq(__LOC__, getB(x), 1)
    eq(__LOC__, getB(bump(x)), 2)
    eq(__LOC__, classify(literal), 1)
    eq(__LOC__, classify(make("y", 2)), 20)
    eq(__LOC__, classify(make("y", 3)), 0)
  })

  test("one-field inline record is the field", () => {
    eq(__LOC__, Obj.magic(makeOne("v")), "v")
    eq(__LOC__, getOne(makeOne("v")), "v")
    eq(__LOC__, Obj.magic(makeOneOptional(Some(4))), 4)
    eq(__LOC__, getOneOptional(makeOneOptional(None)), None)
  })

  test("optional and mutable fields", () => {
    eq(__LOC__, optionalA(makeWithOptional(~a=5, "b")), 5)
    eq(__LOC__, optionalA(makeWithOptional("b")), -1)
    let m = makeMut("m")
    eq(__LOC__, incr(m), 1)
    eq(__LOC__, incr(m), 2)
  })

  test("nested uses", () => {
    eq(__LOC__, innerA(makeOuter()), "in")
    eq(__LOC__, singleB(Single({s: make("s", 7)})), 7)
    eq(__LOC__, polyValue(makePoly(true)), true)
    eq(__LOC__, optionB(Some(make("o", 9))), 9)
    eq(__LOC__, chainLength(Chain({name: "a", next: Some(Chain({name: "b", next: None}))})), 2)
  })
})
