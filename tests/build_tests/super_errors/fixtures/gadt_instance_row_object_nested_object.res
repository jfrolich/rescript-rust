type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, o: {.."f": {.."g": int}}) =>
  switch x {
  | Int => {"f": {"g": y}} === o
  }
