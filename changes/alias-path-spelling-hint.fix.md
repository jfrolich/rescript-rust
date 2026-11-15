- Type checker: a misspelled name read through a module path that ends in an
  alias (`Outer.A.Aple` for `module A = R` in `Outer`) gets the spelling hint
  of the OCaml compiler ("Hint: Did you mean Apple?") for values, constructors,
  record labels, types, modules and module types, and a misspelled qualified
  module type (`R.Sigg`) gets its hint too.
