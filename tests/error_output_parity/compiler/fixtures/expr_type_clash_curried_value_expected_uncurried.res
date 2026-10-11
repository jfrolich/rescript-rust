// error-output-parity: Typecore.Expr_type_clash curried function value where uncurried is expected.
let g = x => y => x + y
let f: (int, int) => int = g
