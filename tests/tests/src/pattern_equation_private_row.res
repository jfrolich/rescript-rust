// A row clash in a constructor pattern is undone and retried as OCaml's
// unify3 does in pattern mode (compiler/ml/ctype.ml:2400-2411): both sides
// are reified and only their compatibility is tested.
type rec eq<_, _> = Refl: eq<'a, 'a>
type rec t<_> = A: t<[#a]> | B: t<[#b]>
type rec payload<_> = P: payload<[#a(int)]>
type rec pair<_> = Pair: pair<([#a], [#b])>

module F = (X: {
  type t = private [< #a | #b]
}) => {
  let closed = (w: eq<X.t, [#a]>) =>
    switch w {
    | Refl => 0
    }
  let both = (x: t<X.t>) =>
    switch x {
    | A => 0
    | B => 1
    }
  let nested = (x: pair<(X.t, X.t)>) =>
    switch x {
    | Pair => 0
    }
}

module G = (X: {
  type t = private [> #a]
}) => {
  let open_ = (w: eq<X.t, [#a | #b]>) =>
    switch w {
    | Refl => 0
    }
}

module H = (X: {
  type t = private [< #a(int) | #b]
}) => {
  let f = (x: payload<X.t>) =>
    switch x {
    | P => 0
    }
}
