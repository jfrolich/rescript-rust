type u = int
type rec t<_> = U: t<u>
let f = (type a, x: t<a>, y: a, o: {.."f": int}) =>
  switch x {
  | U => {"f": y} === o
  }
