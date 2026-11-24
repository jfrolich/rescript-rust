type rec t<_> = Int: t<int>
type r<'a> = 'a constraint 'a = [> #A(int)]
let f = (type a, x: t<a>, y: a, v: r<_>) =>
  switch x {
  | Int => #A(y) === v
  }
