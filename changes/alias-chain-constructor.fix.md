- Type checker: constructors, exception and extension constructors and record
  labels are found through an alias of a module that holds an alias
  (`module O = Outer` then `O.A.A` for `module A = R` in `Outer`), in an
  expression and in a pattern, as in the OCaml compiler.
