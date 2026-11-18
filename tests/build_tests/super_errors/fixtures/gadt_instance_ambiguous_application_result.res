type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, g) =>
  switch x {
  | Int => {
      ignore(g(y) + 1)
      g(0)
    }
  }
