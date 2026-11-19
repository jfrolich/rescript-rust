// A conditional run for its effects inside a function returning unit. The
// closure in its predicate is flattened to if/else like any other closure.
let pushOnMatch = (o: option<int>, n: int, a: array<int>) =>
  o->Option.mapOr(false, m => m == n && m == 3) ? a->Array.push(1) : a->Array.push(2)

let pushOnMatchSwitch = (o: option<int>, n: int, a: array<int>) =>
  switch o {
  | Some(m) if [1, 2]->Array.some(x => x == m && x == n) => a->Array.push(1)
  | _ => a->Array.push(2)
  }

// Returned conditionals and `if` without `else` keep the closure as is.
let returnOnMatch = (o: option<int>, n: int) =>
  o->Option.mapOr(false, m => m == n && m == 3) ? 1 : 2

let pushIfMatch = (o: option<int>, n: int, a: array<int>) =>
  if o->Option.mapOr(false, m => m == n && m == 3) {
    a->Array.push(1)
  }
