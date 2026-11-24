type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, o2: {.."f": a}, o: {.."f": int}) =>
  switch x {
  | Int => o2 === o
  }
