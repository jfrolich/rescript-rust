type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a): {.."f": int} =>
  switch x {
  | Int => {"f": y}
  }
