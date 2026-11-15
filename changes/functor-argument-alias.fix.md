- Module aliases declared in a functor parameter's signature compile as the
  OCaml compiler compiles them: `module Z = X.M` keeps the alias, and a functor
  whose result re-exports such an alias can be applied to a structure.
