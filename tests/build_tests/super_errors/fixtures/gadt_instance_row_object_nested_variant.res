type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, o: {.."f": [> #A(int)]}) =>
  switch x {
  | Int => {"f": #A(y)} === o
  }
