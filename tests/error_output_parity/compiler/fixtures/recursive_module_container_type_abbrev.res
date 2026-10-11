// error-output-parity: Typedecl.Recursive_abbrev through a recursive module constraint payload.
module rec A: {
  type t = array<A.t>
} = {
  type t = array<int>
}
