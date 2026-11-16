type rec t<_> = I: t<int>
module F = (X: {type t}) => {
  let f = (I: t<X.t>, v: X.t): string => v
}
