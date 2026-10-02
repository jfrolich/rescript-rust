// error-output-parity: Typemod.With_cannot_remove_constrained_type for destructive substitution of a constrained type parameter.

module type S = {
  type t<_> constraint 'a = int
}

module type T = S with type t<'a> := 'a
