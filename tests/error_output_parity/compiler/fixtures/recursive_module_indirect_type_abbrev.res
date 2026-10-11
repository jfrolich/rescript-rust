// error-output-parity: Typedecl.Cycle_in_def through a recursive module constraint.
module rec A: {
  type t = A.u
  type u = t
} = {
  type t = int
  type u = int
}
