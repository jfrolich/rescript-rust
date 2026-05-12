// error-output-parity: OCaml rejects type-parameter constraints inside a
// module-type `with type` constraint as a reserved keyword.
module type S = {
  type t<'a>
}

module type T = S with type t<'a> := 'a constraint 'a = int
