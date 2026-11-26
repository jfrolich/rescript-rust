type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, v: [> #A(int) | #B(string)]) =>
  switch x {
  | Int => (if true { #A(y) } else { #B("s") }) === v
  }
