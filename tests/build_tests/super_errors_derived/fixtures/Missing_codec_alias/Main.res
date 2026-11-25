// The argument of a constructor application has no codec in scope.
type plain = {a: int}

@spice
type t = array<plain>
