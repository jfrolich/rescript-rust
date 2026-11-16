type rec t<_> = I: t<int> | S: t<string>
module F = (X: {type t}) => {
  let f = (x: t<X.t>, y: X.t) =>
    switch x {
    | I => y + 1
    }
}
