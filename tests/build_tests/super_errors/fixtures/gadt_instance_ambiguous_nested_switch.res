type rec t<_> = Int: t<int>
type rec s<_> = Str: s<string>
let f = (type a b, x: t<a>, z: s<b>, y: a, w: b) =>
  switch x {
  | Int =>
    switch z {
    | Str => if true { (y, w) } else { (0, "") }
    }
  }
