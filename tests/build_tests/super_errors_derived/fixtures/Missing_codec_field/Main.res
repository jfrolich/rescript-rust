// A record field's type has no codec in scope.
type plain = {a: int}

@spice
type t = {field: plain}
