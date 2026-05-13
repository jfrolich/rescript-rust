// error-output-parity: Typecore.Expr_type_clash curried function where uncurried is expected.
let f: (int, int) => int = x => y => x + y
