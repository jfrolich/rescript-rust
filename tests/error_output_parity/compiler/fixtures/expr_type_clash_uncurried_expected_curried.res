// error-output-parity: Typecore.Expr_type_clash uncurried function where curried is expected.
let f: int => int => int = (x, y) => x + y
