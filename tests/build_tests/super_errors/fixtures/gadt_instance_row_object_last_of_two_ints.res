type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, o: {.."f": int, "g": int}) =>
  switch x {
  | Int => {"f": 1, "g": y} === o
  }
