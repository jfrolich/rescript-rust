// In the body, every `X` is the one `Pident X` of `Subst.add_module`: 395 words, printed.
module type S = {
  type t
}
module F: (X: S) =>
{
  let a0: (X.t, int)
  let a1: (X.t, int)
  let v: string
} = (X: S) => {
  let a0: (X.t, int) = %raw(`0`)
  let a1: (X.t, int) = %raw(`0`)
  let v = 1
}
