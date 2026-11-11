type a = {x: int}
type b = {x: int}

@unboxed
type t = A(a) | B(b)
