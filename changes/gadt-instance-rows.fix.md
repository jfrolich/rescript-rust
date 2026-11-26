- Type checker: an object field and a polymorphic variant row are lowered
  under a GADT equation as in OCaml, so a value whose type is known only
  through the equation is refused when an object or variant comparison would
  let it escape, with OCaml's "This instance of int is ambiguous" error.
