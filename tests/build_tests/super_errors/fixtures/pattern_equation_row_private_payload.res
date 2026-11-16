type rec t<_> = A: t<[#a(int)]>
module F = (X: {type t = private [< #a(string) | #b]}) => {
  let f = (x: t<X.t>) => switch x { | A => 0 }
}
