type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, o: {.."f": int}) =>
  switch x {
  | Int => o === {"f": y}
  }
