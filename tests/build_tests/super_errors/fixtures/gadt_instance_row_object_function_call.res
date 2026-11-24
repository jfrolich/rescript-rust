type rec t<_> = Int: t<int>
let same = (p: 'x, q: 'x) => p === q
let f = (type a, x: t<a>, y: a, o: {.."f": int}) =>
  switch x {
  | Int => same({"f": y}, o)
  }
