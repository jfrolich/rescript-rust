type rec t<_> = Int: t<int> | Str: t<string>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => [y, 0]
  | Str => []
  }
