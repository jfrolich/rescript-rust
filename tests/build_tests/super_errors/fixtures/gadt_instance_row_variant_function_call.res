type rec t<_> = Int: t<int>
let same = (p: 'x, q: 'x) => p === q
let f = (type a, x: t<a>, y: a, v: [> #A(int)]) =>
  switch x {
  | Int => same(#A(y), v)
  }
