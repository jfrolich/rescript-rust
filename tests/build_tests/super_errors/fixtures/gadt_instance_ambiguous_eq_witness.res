type rec eq<'a, 'b> = Refl: eq<'a, 'a>
let f = (type a, e: eq<a, int>, y: a) =>
  switch e {
  | Refl => if true { y } else { 0 }
  }
