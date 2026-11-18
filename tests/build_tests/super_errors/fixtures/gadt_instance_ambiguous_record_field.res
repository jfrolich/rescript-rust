type rec t<_> = Int: t<int>
type r<'a> = {a: 'a, b: 'a}
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => {a: y, b: 0}
  }
