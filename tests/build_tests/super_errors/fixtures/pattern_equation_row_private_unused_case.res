type rec t<_> = A: t<[#a]> | B: t<[#b]>
module F = (X: {type t = private [< #a | #b]}) => {
  let f = (x: t<X.t>) => switch x { | A => 0 | B => 1 }
  let g = (x: t<X.t>) => switch x { | A => 0 }
}
