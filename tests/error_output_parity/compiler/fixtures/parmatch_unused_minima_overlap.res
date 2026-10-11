// Keep unused-case compatibility/minima filtering aligned with OCaml Parmatch.
type t = A | B | C

let classify = value =>
  switch value {
  | A | B => 0
  | A => 1
  | C when true => 2
  | C => 3
  | B => 4
  }
