type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, v2: [> #A(a)], v: [> #A(int)]) =>
  switch x {
  | Int => v2 === v
  }
