type rec t<_> = Int: t<int>
type box<'x> = {l: 'x, m: 'x}
let f = (type a, x: t<a>, y: a, o: {.."f": int}) =>
  switch x {
  | Int => {l: {"f": y}, m: o}
  }
