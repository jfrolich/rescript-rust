- Unifying two polymorphic variant constructors whose payloads hold a type variable
  of a polymorphic type splits those payloads off, as the OCaml compiler does, so
  such programs are reported with OCaml's type and location.
