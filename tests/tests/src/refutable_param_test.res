@@config({
  flags: ["-w", "-8"],
})

open Mocha
open Test_utils

// A refutable parameter pattern raises Match_failure at the position where
// the function starts, as OCaml's transl_function passes the function's
// location to Matching.for_function for every parameter.
let first = (Some(n), m) => n + m

let second = (type a, m: int, Some(n): option<a>) => m

let failure = f =>
  try {
    f()
    None
  } catch {
  | Match_failure((_, line, column)) => Some((line, column))
  }

describe(__MODULE__, () => {
  test("a matching parameter", () => {
    eq(__LOC__, 3, first(Some(1), 2))
    eq(__LOC__, 4, second(4, Some("a")))
  })

  test("Match_failure names the function", () => {
    eq(__LOC__, Some((11, 12)), failure(() => ignore(first(None, 2))))
    eq(__LOC__, Some((13, 13)), failure(() => ignore(second(4, None))))
  })
})
