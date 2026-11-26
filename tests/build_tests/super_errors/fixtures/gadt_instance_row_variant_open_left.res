type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, v: [> #A(int)]) =>
  switch x {
  | Int => #A(y) === v
  }
