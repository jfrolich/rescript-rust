// error-output-parity: Apply_non_function is reported at the typed function loc, which a constraint keeps from its argument.
let f2 = (a, b, c, d) => a(b)->(c, d: dict<int>)
