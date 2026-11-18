type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, b) =>
  switch x {
  | Int =>
    switch b {
    | true => y
    | false => 0
    }
  }
