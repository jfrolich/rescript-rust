type rec t<_> = Int: t<int>
type rec s<_> = Str: s<string>
let f = (type a b, x: t<a>, w: s<b>, y: a, v: b) =>
  switch x {
  | Int => switch w { | Str => { let g = (z: a) => z; g(y) } }
  }
