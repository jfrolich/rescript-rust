type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, v: [> #A(string) | #B(int)]) =>
  switch x {
  | Int => (if true { #A("s") } else { #B(y) }) === v
  }
