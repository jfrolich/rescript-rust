// The types of a and b, read from Stdlib_Int's interface, hold that
// interface's own `int` and `string` identifiers, not the predefined ones:
// 401 words, elided.
module M: {
  let v: string
} = {
  let a = Int.toString
  let b = Int.toString
  let h0 = true
  let v = 1
}
