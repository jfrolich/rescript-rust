type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, o: {.."f": string, "g": int}) =>
  switch x {
  | Int => {"f": "s", "g": y} === o
  }
