type rec eq<'a, 'b> = Refl: eq<'a, 'a>
let f = (type a, w: eq<a, int>, y: a, o: {.."f": int}) =>
  switch w {
  | Refl => {"f": y} === o
  }
