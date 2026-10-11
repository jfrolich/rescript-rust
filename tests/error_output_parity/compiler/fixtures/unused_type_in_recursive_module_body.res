// error-output-parity: Typedecl.Recursive_abbrev through a recursive module constraint.
module rec A: {} = {
  type t = int
}
