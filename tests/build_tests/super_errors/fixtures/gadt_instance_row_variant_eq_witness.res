type rec eq<'a, 'b> = Refl: eq<'a, 'a>
let f = (type a, w: eq<a, int>, y: a, v: [> #A(int)]) =>
  switch w {
  | Refl => #A(y) === v
  }
