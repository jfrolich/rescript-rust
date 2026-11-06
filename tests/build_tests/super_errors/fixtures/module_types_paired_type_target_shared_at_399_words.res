// In N, every `t` is the one `Pident t` of `Subst.add_type`: 399 words, printed.
module M: {
  type t
  module N: {
    let a0: (t, t)
    let a1: (t, t, t)
    let v: string
  }
} = {
  type t = int
  module N = {
    let a0: (t, t) = %raw(`0`)
    let a1: (t, t, t) = %raw(`0`)
    let v = 1
  }
}
