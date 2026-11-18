type rec t<_> = Int: t<int> | Str: t<string>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => if true { y } else { 0 }
  | Str => if true { y } else { "" }
  }
