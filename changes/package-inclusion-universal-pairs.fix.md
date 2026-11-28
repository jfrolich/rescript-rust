- Type checker: after the inclusion check of two packages of different module
  types inside a polymorphic type, the rest of that polymorphic body no longer
  pairs its universal variables, as in the OCaml compiler, so coercions and
  annotations such as `{"f": 'a. (module(S), 'a)}` to
  `{"f": 'a. (module(T), 'a)}` are refused with the same error.
